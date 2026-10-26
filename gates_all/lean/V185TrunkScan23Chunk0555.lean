import V185TrunkScan23Chunk0554

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3280069 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_3280069 : Nat := 118140960795 + 3280069 * 2 ^ 59
def prefixEnd_3280069 : Nat := 4983230072969 + 3 ^ 40 * 3280069 * 2
def baseEnd_3280069 : Nat := 1684251976912432448652743

theorem tailTrace_3280069 : CollatzResearch.WordTrace tailWord_3280069 prefixEnd_3280069 1684251976912432448652743 := by
  unfold tailWord_3280069
  simp only [CollatzResearch.WordTrace]
  refine ⟨119633944753877679031211261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79755963169251786020807507 119633944753877679031211261)
  ·
    refine ⟨44862729282704129636704223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119633944753877679031211261 44862729282704129636704223)
    ·
      refine ⟨67294093924056194455056335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44862729282704129636704223 67294093924056194455056335)
      ·
        refine ⟨100941140886084291682584503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67294093924056194455056335 100941140886084291682584503)
        ·
          refine ⟨151411711329126437523876755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100941140886084291682584503 151411711329126437523876755)
          ·
            refine ⟨227117566993689656285815133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151411711329126437523876755 227117566993689656285815133)
            ·
              refine ⟨85169087622633621107180675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227117566993689656285815133 85169087622633621107180675)
              ·
                refine ⟨127753631433950431660771013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85169087622633621107180675 127753631433950431660771013)
                ·
                  refine ⟨23953805893865705936394565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127753631433950431660771013 23953805893865705936394565)
                  ·
                    refine ⟨4491338605099819863073981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23953805893865705936394565 4491338605099819863073981)
                    ·
                      refine ⟨1684251976912432448652743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491338605099819863073981 1684251976912432448652743)
                      ·
                        rfl

theorem cell23_3280069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_3280069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280069 prefixEnd_3280069 := by exact prefixLift 3280069
  have htrace : WordTrace (prefixWord ++ tailWord_3280069) baseStart_3280069 baseEnd_3280069 := by
    simpa [prefixWord, tailWord_3280069, baseEnd_3280069] using wordTrace_append hprefix tailTrace_3280069
  have hstable : (prefixWord ++ tailWord_3280069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280069).length < 2 ^ (prefixWord ++ tailWord_3280069).sum := by decide
  have hdescent : baseEnd_3280069 < baseStart_3280069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280100 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_3280100 : Nat := 118140960795 + 3280100 * 2 ^ 59
def prefixEnd_3280100 : Nat := 4983230072969 + 3 ^ 40 * 3280100 * 2
def baseEnd_3280100 : Nat := 1684267894812721827365101

theorem tailTrace_3280100 : CollatzResearch.WordTrace tailWord_3280100 prefixEnd_3280100 1684267894812721827365101 := by
  unfold tailWord_3280100
  simp only [CollatzResearch.WordTrace]
  refine ⟨59817537708382685662794877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79756716944510247550393169 59817537708382685662794877)
  ·
    refine ⟨22431576640643507123548079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59817537708382685662794877 22431576640643507123548079)
    ·
      refine ⟨33647364960965260685322119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22431576640643507123548079 33647364960965260685322119)
      ·
        refine ⟨50471047441447891027983179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33647364960965260685322119 50471047441447891027983179)
        ·
          refine ⟨75706571162171836541974769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50471047441447891027983179 75706571162171836541974769)
          ·
            refine ⟨56779928371628877406481077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75706571162171836541974769 56779928371628877406481077)
            ·
              refine ⟨5323118284840207256857601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56779928371628877406481077 5323118284840207256857601)
              ·
                refine ⟨3992338713630155442643201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323118284840207256857601 3992338713630155442643201)
                ·
                  refine ⟨2994254035222616581982401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3992338713630155442643201 2994254035222616581982401)
                  ·
                    refine ⟨2245690526416962436486801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2994254035222616581982401 2245690526416962436486801)
                    ·
                      refine ⟨1684267894812721827365101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245690526416962436486801 1684267894812721827365101)
                      ·
                        rfl

theorem cell23_3280100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_3280100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280100 prefixEnd_3280100 := by exact prefixLift 3280100
  have htrace : WordTrace (prefixWord ++ tailWord_3280100) baseStart_3280100 baseEnd_3280100 := by
    simpa [prefixWord, tailWord_3280100, baseEnd_3280100] using wordTrace_append hprefix tailTrace_3280100
  have hstable : (prefixWord ++ tailWord_3280100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280100).length < 2 ^ (prefixWord ++ tailWord_3280100).sum := by decide
  have hdescent : baseEnd_3280100 < baseStart_3280100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280106 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 7]
def baseStart_3280106 : Nat := 118140960795 + 3280106 * 2 ^ 59
def prefixEnd_3280106 : Nat := 4983230072969 + 3 ^ 40 * 3280106 * 2
def baseEnd_3280106 : Nat := 187141219521849867098897

theorem tailTrace_3280106 : CollatzResearch.WordTrace tailWord_3280106 prefixEnd_3280106 187141219521849867098897 := by
  unfold tailWord_3280106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29908823563685908587577043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79756862836495756233538781 29908823563685908587577043)
  ·
    refine ⟨44863235345528862881365565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29908823563685908587577043 44863235345528862881365565)
    ·
      refine ⟨16823713254573323580512087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44863235345528862881365565 16823713254573323580512087)
      ·
        refine ⟨25235569881859985370768131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823713254573323580512087 25235569881859985370768131)
        ·
          refine ⟨37853354822789978056152197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25235569881859985370768131 37853354822789978056152197)
          ·
            refine ⟨7097504029273120885528537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37853354822789978056152197 7097504029273120885528537)
            ·
              refine ⟨5323128021954840664146403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097504029273120885528537 5323128021954840664146403)
              ·
                refine ⟨7984692032932260996219605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323128021954840664146403 7984692032932260996219605)
                ·
                  refine ⟨187141219521849867098897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7984692032932260996219605 187141219521849867098897)
                  ·
                    rfl

theorem cell23_3280106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_3280106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280106 prefixEnd_3280106 := by exact prefixLift 3280106
  have htrace : WordTrace (prefixWord ++ tailWord_3280106) baseStart_3280106 baseEnd_3280106 := by
    simpa [prefixWord, tailWord_3280106, baseEnd_3280106] using wordTrace_append hprefix tailTrace_3280106
  have hstable : (prefixWord ++ tailWord_3280106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280106).length < 2 ^ (prefixWord ++ tailWord_3280106).sum := by decide
  have hdescent : baseEnd_3280106 < baseStart_3280106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280119 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 4, 5]
def baseStart_3280119 : Nat := 118140960795 + 3280119 * 2 ^ 59
def prefixEnd_3280119 : Nat := 4983230072969 + 3 ^ 40 * 3280119 * 2
def baseEnd_3280119 : Nat := 561425883648385751009171

theorem tailTrace_3280119 : CollatzResearch.WordTrace tailWord_3280119 prefixEnd_3280119 561425883648385751009171 := by
  unfold tailWord_3280119
  simp only [CollatzResearch.WordTrace]
  refine ⟨119635768403696537570531411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79757178935797691713687607 119635768403696537570531411)
  ·
    refine ⟨179453652605544806355797117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119635768403696537570531411 179453652605544806355797117)
    ·
      refine ⟨67295119727079302383423919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179453652605544806355797117 67295119727079302383423919)
      ·
        refine ⟨100942679590618953575135879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67295119727079302383423919 100942679590618953575135879)
        ·
          refine ⟨151414019385928430362703819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100942679590618953575135879 151414019385928430362703819)
          ·
            refine ⟨227121029078892645544055729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151414019385928430362703819 227121029078892645544055729)
            ·
              refine ⟨170340771809169484158041797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227121029078892645544055729 170340771809169484158041797)
              ·
                refine ⟨31938894714219278279632837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170340771809169484158041797 31938894714219278279632837)
                ·
                  refine ⟨5988542758916114677431157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31938894714219278279632837 5988542758916114677431157)
                  ·
                    refine ⟨561425883648385751009171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5988542758916114677431157 561425883648385751009171)
                    ·
                      rfl

theorem cell23_3280119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_3280119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280119 prefixEnd_3280119 := by exact prefixLift 3280119
  have htrace : WordTrace (prefixWord ++ tailWord_3280119) baseStart_3280119 baseEnd_3280119 := by
    simpa [prefixWord, tailWord_3280119, baseEnd_3280119] using wordTrace_append hprefix tailTrace_3280119
  have hstable : (prefixWord ++ tailWord_3280119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280119).length < 2 ^ (prefixWord ++ tailWord_3280119).sum := by decide
  have hdescent : baseEnd_3280119 < baseStart_3280119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280156 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3280156 : Nat := 118140960795 + 3280156 * 2 ^ 59
def prefixEnd_3280156 : Nat := 4983230072969 + 3 ^ 40 * 3280156 * 2
def baseEnd_3280156 : Nat := 1684296649729373608264843

theorem tailTrace_3280156 : CollatzResearch.WordTrace tailWord_3280156 prefixEnd_3280156 1684296649729373608264843 := by
  unfold tailWord_3280156
  simp only [CollatzResearch.WordTrace]
  refine ⟨59818558952281246444814161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79758078603041661926418881 59818558952281246444814161)
  ·
    refine ⟨44863919214210934833610621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59818558952281246444814161 44863919214210934833610621)
    ·
      refine ⟨16823969705329100562603983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44863919214210934833610621 16823969705329100562603983)
      ·
        refine ⟨25235954557993650843905975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823969705329100562603983 25235954557993650843905975)
        ·
          refine ⟨37853931836990476265858963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25235954557993650843905975 37853931836990476265858963)
          ·
            refine ⟨56780897755485714398788445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37853931836990476265858963 56780897755485714398788445)
            ·
              refine ⟨21292836658307142899545667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56780897755485714398788445 21292836658307142899545667)
              ·
                refine ⟨31939254987460714349318501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21292836658307142899545667 31939254987460714349318501)
                ·
                  refine ⟨5988610310148883940497219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31939254987460714349318501 5988610310148883940497219)
                  ·
                    refine ⟨8982915465223325910745829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5988610310148883940497219 8982915465223325910745829)
                    ·
                      refine ⟨1684296649729373608264843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8982915465223325910745829 1684296649729373608264843)
                      ·
                        rfl

theorem cell23_3280156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3280156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280156 prefixEnd_3280156 := by exact prefixLift 3280156
  have htrace : WordTrace (prefixWord ++ tailWord_3280156) baseStart_3280156 baseEnd_3280156 := by
    simpa [prefixWord, tailWord_3280156, baseEnd_3280156] using wordTrace_append hprefix tailTrace_3280156
  have hstable : (prefixWord ++ tailWord_3280156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280156).length < 2 ^ (prefixWord ++ tailWord_3280156).sum := by decide
  have hdescent : baseEnd_3280156 < baseStart_3280156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280169 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_3280169 : Nat := 118140960795 + 3280169 * 2 ^ 59
def prefixEnd_3280169 : Nat := 4983230072969 + 3 ^ 40 * 3280169 * 2
def baseEnd_3280169 : Nat := 1684303324977882057402283

theorem tailTrace_3280169 : CollatzResearch.WordTrace tailWord_3280169 prefixEnd_3280169 1684303324977882057402283 := by
  unfold tailWord_3280169
  simp only [CollatzResearch.WordTrace]
  refine ⟨119637592053515396109851561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79758394702343597406567707 119637592053515396109851561)
  ·
    refine ⟨89728194040136547082388671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119637592053515396109851561 89728194040136547082388671)
    ·
      refine ⟨134592291060204820623583007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89728194040136547082388671 134592291060204820623583007)
      ·
        refine ⟨201888436590307230935374511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134592291060204820623583007 201888436590307230935374511)
        ·
          refine ⟨302832654885460846403061767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201888436590307230935374511 302832654885460846403061767)
          ·
            refine ⟨454248982328191269604592651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302832654885460846403061767 454248982328191269604592651)
            ·
              refine ⟨681373473492286904406888977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454248982328191269604592651 681373473492286904406888977)
              ·
                refine ⟨511030105119215178305166733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681373473492286904406888977 511030105119215178305166733)
                ·
                  refine ⟨191636289419705691864437525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511030105119215178305166733 191636289419705691864437525)
                  ·
                    refine ⟨8982951066548704306145509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 191636289419705691864437525 8982951066548704306145509)
                    ·
                      refine ⟨1684303324977882057402283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8982951066548704306145509 1684303324977882057402283)
                      ·
                        rfl

theorem cell23_3280169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_3280169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280169 prefixEnd_3280169 := by exact prefixLift 3280169
  have htrace : WordTrace (prefixWord ++ tailWord_3280169) baseStart_3280169 baseEnd_3280169 := by
    simpa [prefixWord, tailWord_3280169, baseEnd_3280169] using wordTrace_append hprefix tailTrace_3280169
  have hstable : (prefixWord ++ tailWord_3280169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280169).length < 2 ^ (prefixWord ++ tailWord_3280169).sum := by decide
  have hdescent : baseEnd_3280169 < baseStart_3280169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280176 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3]
def baseStart_3280176 : Nat := 118140960795 + 3280176 * 2 ^ 59
def prefixEnd_3280176 : Nat := 4983230072969 + 3 ^ 40 * 3280176 * 2
def baseEnd_3280176 : Nat := 1684306919342463530014751

theorem tailTrace_3280176 : CollatzResearch.WordTrace tailWord_3280176 prefixEnd_3280176 1684306919342463530014751 := by
  unfold tailWord_3280176
  simp only [CollatzResearch.WordTrace]
  refine ⟨59818923682245018152678191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79758564909660024203570921 59818923682245018152678191)
  ·
    refine ⟨89728385523367527229017287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59818923682245018152678191 89728385523367527229017287)
    ·
      refine ⟨134592578285051290843525931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89728385523367527229017287 134592578285051290843525931)
      ·
        refine ⟨201888867427576936265288897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134592578285051290843525931 201888867427576936265288897)
        ·
          refine ⟨151416650570682702198966673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201888867427576936265288897 151416650570682702198966673)
          ·
            refine ⟨113562487928012026649225005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151416650570682702198966673 113562487928012026649225005)
            ·
              refine ⟨42585932973004509993459377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113562487928012026649225005 42585932973004509993459377)
              ·
                refine ⟨31939449729753382495094533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42585932973004509993459377 31939449729753382495094533)
                ·
                  refine ⟨5988646824328759217830225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31939449729753382495094533 5988646824328759217830225)
                  ·
                    refine ⟨4491485118246569413372669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988646824328759217830225 4491485118246569413372669)
                    ·
                      refine ⟨1684306919342463530014751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491485118246569413372669 1684306919342463530014751)
                      ·
                        rfl

theorem cell23_3280176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_3280176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280176 prefixEnd_3280176 := by exact prefixLift 3280176
  have htrace : WordTrace (prefixWord ++ tailWord_3280176) baseStart_3280176 baseEnd_3280176 := by
    simpa [prefixWord, tailWord_3280176, baseEnd_3280176] using wordTrace_append hprefix tailTrace_3280176
  have hstable : (prefixWord ++ tailWord_3280176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280176).length < 2 ^ (prefixWord ++ tailWord_3280176).sum := by decide
  have hdescent : baseEnd_3280176 < baseStart_3280176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280213 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 6]
def baseStart_3280213 : Nat := 118140960795 + 3280213 * 2 ^ 59
def prefixEnd_3280213 : Nat := 4983230072969 + 3 ^ 40 * 3280213 * 2
def baseEnd_3280213 : Nat := 187147324236297765028009

theorem tailTrace_3280213 : CollatzResearch.WordTrace tailWord_3280213 prefixEnd_3280213 187147324236297765028009 := by
  unfold tailWord_3280213
  simp only [CollatzResearch.WordTrace]
  refine ⟨119639196865355991624453293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79759464576903994416302195 119639196865355991624453293)
  ·
    refine ⟨44864698824508496859169985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119639196865355991624453293 44864698824508496859169985)
    ·
      refine ⟨33648524118381372644377489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44864698824508496859169985 33648524118381372644377489)
      ·
        refine ⟨25236393088786029483283117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33648524118381372644377489 25236393088786029483283117)
        ·
          refine ⟨9463647408294761056231169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25236393088786029483283117 9463647408294761056231169)
          ·
            refine ⟨7097735556221070792173377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9463647408294761056231169 7097735556221070792173377)
            ·
              refine ⟨5323301667165803094130033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097735556221070792173377 5323301667165803094130033)
              ·
                refine ⟨3992476250374352320597525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323301667165803094130033 3992476250374352320597525)
                ·
                  refine ⟨187147324236297765028009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3992476250374352320597525 187147324236297765028009)
                  ·
                    rfl

theorem cell23_3280213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_3280213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280213 prefixEnd_3280213 := by exact prefixLift 3280213
  have htrace : WordTrace (prefixWord ++ tailWord_3280213) baseStart_3280213 baseEnd_3280213 := by
    simpa [prefixWord, tailWord_3280213, baseEnd_3280213] using wordTrace_append hprefix tailTrace_3280213
  have hstable : (prefixWord ++ tailWord_3280213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280213).length < 2 ^ (prefixWord ++ tailWord_3280213).sum := by decide
  have hdescent : baseEnd_3280213 < baseStart_3280213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280223 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 3]
def baseStart_3280223 : Nat := 118140960795 + 3280223 * 2 ^ 59
def prefixEnd_3280223 : Nat := 4983230072969 + 3 ^ 40 * 3280223 * 2
def baseEnd_3280223 : Nat := 1684331052933224846127035

theorem tailTrace_3280223 : CollatzResearch.WordTrace tailWord_3280223 prefixEnd_3280223 1684331052933224846127035 := by
  unfold tailWord_3280223
  simp only [CollatzResearch.WordTrace]
  refine ⟨119639561595319763332317323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79759707730213175554878215 119639561595319763332317323)
  ·
    refine ⟨179459342392979644998475985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119639561595319763332317323 179459342392979644998475985)
    ·
      refine ⟨134594506794734733748856989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179459342392979644998475985 134594506794734733748856989)
      ·
        refine ⟨50472940048025525155821371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134594506794734733748856989 50472940048025525155821371)
        ·
          refine ⟨75709410072038287733732057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50472940048025525155821371 75709410072038287733732057)
          ·
            refine ⟨56782057554028715800299043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75709410072038287733732057 56782057554028715800299043)
            ·
              refine ⟨85173086331043073700448565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56782057554028715800299043 85173086331043073700448565)
              ·
                refine ⟨7984976843535288159417053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85173086331043073700448565 7984976843535288159417053)
                ·
                  refine ⟨2994366316325733059781395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7984976843535288159417053 2994366316325733059781395)
                  ·
                    refine ⟨4491549474488599589672093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2994366316325733059781395 4491549474488599589672093)
                    ·
                      refine ⟨1684331052933224846127035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491549474488599589672093 1684331052933224846127035)
                      ·
                        rfl

theorem cell23_3280223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_3280223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280223 prefixEnd_3280223 := by exact prefixLift 3280223
  have htrace : WordTrace (prefixWord ++ tailWord_3280223) baseStart_3280223 baseEnd_3280223 := by
    simpa [prefixWord, tailWord_3280223, baseEnd_3280223] using wordTrace_append hprefix tailTrace_3280223
  have hstable : (prefixWord ++ tailWord_3280223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280223).length < 2 ^ (prefixWord ++ tailWord_3280223).sum := by decide
  have hdescent : baseEnd_3280223 < baseStart_3280223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280260 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_3280260 : Nat := 118140960795 + 3280260 * 2 ^ 59
def prefixEnd_3280260 : Nat := 4983230072969 + 3 ^ 40 * 3280260 * 2
def baseEnd_3280260 : Nat := 561450017239147067121455

theorem tailTrace_3280260 : CollatzResearch.WordTrace tailWord_3280260 prefixEnd_3280260 561450017239147067121455 := by
  unfold tailWord_3280260
  simp only [CollatzResearch.WordTrace]
  refine ⟨59820455548092859325707117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79760607397457145767609489 59820455548092859325707117)
  ·
    refine ⟨22432670830534822247140169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59820455548092859325707117 22432670830534822247140169)
    ·
      refine ⟨16824503122901116685355127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22432670830534822247140169 16824503122901116685355127)
      ·
        refine ⟨25236754684351675028032691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16824503122901116685355127 25236754684351675028032691)
        ·
          refine ⟨37855132026527512542049037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25236754684351675028032691 37855132026527512542049037)
          ·
            refine ⟨14195674509947817203268389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37855132026527512542049037 14195674509947817203268389)
            ·
              refine ⟨2661688970615215725612823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14195674509947817203268389 2661688970615215725612823)
              ·
                refine ⟨3992533455922823588419235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661688970615215725612823 3992533455922823588419235)
                ·
                  refine ⟨5988800183884235382628853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992533455922823588419235 5988800183884235382628853)
                  ·
                    refine ⟨561450017239147067121455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5988800183884235382628853 561450017239147067121455)
                    ·
                      rfl

theorem cell23_3280260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_3280260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280260 prefixEnd_3280260 := by exact prefixLift 3280260
  have htrace : WordTrace (prefixWord ++ tailWord_3280260) baseStart_3280260 baseEnd_3280260 := by
    simpa [prefixWord, tailWord_3280260, baseEnd_3280260] using wordTrace_append hprefix tailTrace_3280260
  have hstable : (prefixWord ++ tailWord_3280260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280260).length < 2 ^ (prefixWord ++ tailWord_3280260).sum := by decide
  have hdescent : baseEnd_3280260 < baseStart_3280260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280274 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3280274 : Nat := 118140960795 + 3280274 * 2 ^ 59
def prefixEnd_3280274 : Nat := 4983230072969 + 3 ^ 40 * 3280274 * 2
def baseEnd_3280274 : Nat := 1684357240446604146589301

theorem tailTrace_3280274 : CollatzResearch.WordTrace tailWord_3280274 prefixEnd_3280274 1684357240446604146589301 := by
  unfold tailWord_3280274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29910355429533749760605969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79760947812089999361615917 29910355429533749760605969)
  ·
    refine ⟨22432766572150312320454477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29910355429533749760605969 22432766572150312320454477)
    ·
      refine ⟨8412287464556367120170429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22432766572150312320454477 8412287464556367120170429)
      ·
        refine ⟨3154607799208637670063911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8412287464556367120170429 3154607799208637670063911)
        ·
          refine ⟨4731911698812956505095867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154607799208637670063911 4731911698812956505095867)
          ·
            refine ⟨7097867548219434757643801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731911698812956505095867 7097867548219434757643801)
            ·
              refine ⟨5323400661164576068232851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097867548219434757643801 5323400661164576068232851)
              ·
                refine ⟨7985100991746864102349277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323400661164576068232851 7985100991746864102349277)
                ·
                  refine ⟨2994412871905074038380979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7985100991746864102349277 2994412871905074038380979)
                  ·
                    refine ⟨4491619307857611057571469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2994412871905074038380979 4491619307857611057571469)
                    ·
                      refine ⟨1684357240446604146589301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491619307857611057571469 1684357240446604146589301)
                      ·
                        rfl

theorem cell23_3280274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3280274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280274 prefixEnd_3280274 := by exact prefixLift 3280274
  have htrace : WordTrace (prefixWord ++ tailWord_3280274) baseStart_3280274 baseEnd_3280274 := by
    simpa [prefixWord, tailWord_3280274, baseEnd_3280274] using wordTrace_append hprefix tailTrace_3280274
  have hstable : (prefixWord ++ tailWord_3280274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280274).length < 2 ^ (prefixWord ++ tailWord_3280274).sum := by decide
  have hdescent : baseEnd_3280274 < baseStart_3280274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280290 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3280290 : Nat := 118140960795 + 3280290 * 2 ^ 59
def prefixEnd_3280290 : Nat := 4983230072969 + 3 ^ 40 * 3280290 * 2
def baseEnd_3280290 : Nat := 561455152045692027996409

theorem tailTrace_3280290 : CollatzResearch.WordTrace tailWord_3280290 prefixEnd_3280290 561455152045692027996409 := by
  unfold tailWord_3280290
  simp only [CollatzResearch.WordTrace]
  refine ⟨29910501321519258443751581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79761336857384689183337549 29910501321519258443751581)
  ·
    refine ⟨11216437995569721916406843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29910501321519258443751581 11216437995569721916406843)
    ·
      refine ⟨16824656993354582874610265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216437995569721916406843 16824656993354582874610265)
      ·
        refine ⟨12618492745015937155957699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16824656993354582874610265 12618492745015937155957699)
        ·
          refine ⟨18927739117523905733936549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12618492745015937155957699 18927739117523905733936549)
          ·
            refine ⟨3548951084535732325113103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18927739117523905733936549 3548951084535732325113103)
            ·
              refine ⟨5323426626803598487669655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548951084535732325113103 5323426626803598487669655)
              ·
                refine ⟨7985139940205397731504483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323426626803598487669655 7985139940205397731504483)
                ·
                  refine ⟨11977709910308096597256725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7985139940205397731504483 11977709910308096597256725)
                  ·
                    refine ⟨561455152045692027996409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11977709910308096597256725 561455152045692027996409)
                    ·
                      rfl

theorem cell23_3280290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3280290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280290 prefixEnd_3280290 := by exact prefixLift 3280290
  have htrace : WordTrace (prefixWord ++ tailWord_3280290) baseStart_3280290 baseEnd_3280290 := by
    simpa [prefixWord, tailWord_3280290, baseEnd_3280290] using wordTrace_append hprefix tailTrace_3280290
  have hstable : (prefixWord ++ tailWord_3280290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280290).length < 2 ^ (prefixWord ++ tailWord_3280290).sum := by decide
  have hdescent : baseEnd_3280290 < baseStart_3280290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280330 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_3280330 : Nat := 118140960795 + 3280330 * 2 ^ 59
def prefixEnd_3280330 : Nat := 4983230072969 + 3 ^ 40 * 3280330 * 2
def baseEnd_3280330 : Nat := 1684385995363255927489043

theorem tailTrace_3280330 : CollatzResearch.WordTrace tailWord_3280330 prefixEnd_3280330 1684385995363255927489043 := by
  unfold tailWord_3280330
  simp only [CollatzResearch.WordTrace]
  refine ⟨29910866051483030151615611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79762309470621413737641629 29910866051483030151615611)
  ·
    refine ⟨44866299077224545227423417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29910866051483030151615611 44866299077224545227423417)
    ·
      refine ⟨33649724307918408920567563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44866299077224545227423417 33649724307918408920567563)
      ·
        refine ⟨50474586461877613380851345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33649724307918408920567563 50474586461877613380851345)
        ·
          refine ⟨37855939846408210035638509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50474586461877613380851345 37855939846408210035638509)
          ·
            refine ⟨14195977442403078763364441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37855939846408210035638509 14195977442403078763364441)
            ·
              refine ⟨10646983081802309072523331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14195977442403078763364441 10646983081802309072523331)
              ·
                refine ⟨15970474622703463608784997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646983081802309072523331 15970474622703463608784997)
                ·
                  refine ⟨2994463991756899426647187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15970474622703463608784997 2994463991756899426647187)
                  ·
                    refine ⟨4491695987635349139970781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2994463991756899426647187 4491695987635349139970781)
                    ·
                      refine ⟨1684385995363255927489043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491695987635349139970781 1684385995363255927489043)
                      ·
                        rfl

theorem cell23_3280330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_3280330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280330 prefixEnd_3280330 := by exact prefixLift 3280330
  have htrace : WordTrace (prefixWord ++ tailWord_3280330) baseStart_3280330 baseEnd_3280330 := by
    simpa [prefixWord, tailWord_3280330, baseEnd_3280330] using wordTrace_append hprefix tailTrace_3280330
  have hstable : (prefixWord ++ tailWord_3280330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280330).length < 2 ^ (prefixWord ++ tailWord_3280330).sum := by decide
  have hdescent : baseEnd_3280330 < baseStart_3280330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280336 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_3280336 : Nat := 118140960795 + 3280336 * 2 ^ 59
def prefixEnd_3280336 : Nat := 4983230072969 + 3 ^ 40 * 3280336 * 2
def baseEnd_3280336 : Nat := 1684389076247182904014015

theorem tailTrace_3280336 : CollatzResearch.WordTrace tailWord_3280336 prefixEnd_3280336 1684389076247182904014015 := by
  unfold tailWord_3280336
  simp only [CollatzResearch.WordTrace]
  refine ⟨59821841521955191815590431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79762455362606922420787241 59821841521955191815590431)
  ·
    refine ⟨89732762282932787723385647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59821841521955191815590431 89732762282932787723385647)
    ·
      refine ⟨134599143424399181585078471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89732762282932787723385647 134599143424399181585078471)
      ·
        refine ⟨201898715136598772377617707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134599143424399181585078471 201898715136598772377617707)
        ·
          refine ⟨302848072704898158566426561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201898715136598772377617707 302848072704898158566426561)
          ·
            refine ⟨227136054528673618924819921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302848072704898158566426561 227136054528673618924819921)
            ·
              refine ⟨170352040896505214193614941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227136054528673618924819921 170352040896505214193614941)
              ·
                refine ⟨63882015336189455322605603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170352040896505214193614941 63882015336189455322605603)
                ·
                  refine ⟨95823023004284182983908405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63882015336189455322605603 95823023004284182983908405)
                  ·
                    refine ⟨8983408406651642154741413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95823023004284182983908405 8983408406651642154741413)
                    ·
                      refine ⟨1684389076247182904014015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8983408406651642154741413 1684389076247182904014015)
                      ·
                        rfl

theorem cell23_3280336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_3280336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280336 prefixEnd_3280336 := by exact prefixLift 3280336
  have htrace : WordTrace (prefixWord ++ tailWord_3280336) baseStart_3280336 baseEnd_3280336 := by
    simpa [prefixWord, tailWord_3280336, baseEnd_3280336] using wordTrace_append hprefix tailTrace_3280336
  have hstable : (prefixWord ++ tailWord_3280336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280336).length < 2 ^ (prefixWord ++ tailWord_3280336).sum := by decide
  have hdescent : baseEnd_3280336 < baseStart_3280336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280357 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3280357 : Nat := 118140960795 + 3280357 * 2 ^ 59
def prefixEnd_3280357 : Nat := 4983230072969 + 3 ^ 40 * 3280357 * 2
def baseEnd_3280357 : Nat := 1684399859340927321851419

theorem tailTrace_3280357 : CollatzResearch.WordTrace tailWord_3280357 prefixEnd_3280357 1684399859340927321851419 := by
  unfold tailWord_3280357
  simp only [CollatzResearch.WordTrace]
  refine ⟨119644448976834304217695325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79762965984556202811796883 119644448976834304217695325)
  ·
    refine ⟨44866668366312864081635747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119644448976834304217695325 44866668366312864081635747)
    ·
      refine ⟨67300002549469296122453621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44866668366312864081635747 67300002549469296122453621)
      ·
        refine ⟨6309375239012746511480027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67300002549469296122453621 6309375239012746511480027)
        ·
          refine ⟨9464062858519119767220041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6309375239012746511480027 9464062858519119767220041)
          ·
            refine ⟨7098047143889339825415031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9464062858519119767220041 7098047143889339825415031)
            ·
              refine ⟨10647070715834009738122547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098047143889339825415031 10647070715834009738122547)
              ·
                refine ⟨15970606073751014607183821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10647070715834009738122547 15970606073751014607183821)
                ·
                  refine ⟨5988977277656630477693933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15970606073751014607183821 5988977277656630477693933)
                  ·
                    refine ⟨2245866479121236429135225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5988977277656630477693933 2245866479121236429135225)
                    ·
                      refine ⟨1684399859340927321851419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245866479121236429135225 1684399859340927321851419)
                      ·
                        rfl

theorem cell23_3280357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3280357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280357 prefixEnd_3280357 := by exact prefixLift 3280357
  have htrace : WordTrace (prefixWord ++ tailWord_3280357) baseStart_3280357 baseEnd_3280357 := by
    simpa [prefixWord, tailWord_3280357, baseEnd_3280357] using wordTrace_append hprefix tailTrace_3280357
  have hstable : (prefixWord ++ tailWord_3280357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280357).length < 2 ^ (prefixWord ++ tailWord_3280357).sum := by decide
  have hdescent : baseEnd_3280357 < baseStart_3280357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280382 : List Nat := [4, 2, 2, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3280382 : Nat := 118140960795 + 3280382 * 2 ^ 59
def prefixEnd_3280382 : Nat := 4983230072969 + 3 ^ 40 * 3280382 * 2
def baseEnd_3280382 : Nat := 1684412696357289724038805

theorem tailTrace_3280382 : CollatzResearch.WordTrace tailWord_3280382 prefixEnd_3280382 1684412696357289724038805 := by
  unfold tailWord_3280382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955670100217966685919425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79763573867829155658236933 14955670100217966685919425)
  ·
    refine ⟨11216752575163475014439569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14955670100217966685919425 11216752575163475014439569)
    ·
      refine ⟨8412564431372606260829677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11216752575163475014439569 8412564431372606260829677)
      ·
        refine ⟨3154711661764727347811129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8412564431372606260829677 3154711661764727347811129)
        ·
          refine ⟨2366033746323545510858347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3154711661764727347811129 2366033746323545510858347)
          ·
            refine ⟨3549050619485318266287521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366033746323545510858347 3549050619485318266287521)
            ·
              refine ⟨2661787964613988699715641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549050619485318266287521 2661787964613988699715641)
              ·
                refine ⟨1996340973460491524786731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661787964613988699715641 1996340973460491524786731)
                ·
                  refine ⟨2994511460190737287180097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996340973460491524786731 2994511460190737287180097)
                  ·
                    refine ⟨2245883595143052965385073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2994511460190737287180097 2245883595143052965385073)
                    ·
                      refine ⟨1684412696357289724038805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245883595143052965385073 1684412696357289724038805)
                      ·
                        rfl

theorem cell23_3280382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3280382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280382 prefixEnd_3280382 := by exact prefixLift 3280382
  have htrace : WordTrace (prefixWord ++ tailWord_3280382) baseStart_3280382 baseEnd_3280382 := by
    simpa [prefixWord, tailWord_3280382, baseEnd_3280382] using wordTrace_append hprefix tailTrace_3280382
  have hstable : (prefixWord ++ tailWord_3280382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280382).length < 2 ^ (prefixWord ++ tailWord_3280382).sum := by decide
  have hdescent : baseEnd_3280382 < baseStart_3280382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280403 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 3]
def baseStart_3280403 : Nat := 118140960795 + 3280403 * 2 ^ 59
def prefixEnd_3280403 : Nat := 4983230072969 + 3 ^ 40 * 3280403 * 2
def baseEnd_3280403 : Nat := 1684423479451034141876207

theorem tailTrace_3280403 : CollatzResearch.WordTrace tailWord_3280403 prefixEnd_3280403 1684423479451034141876207 := by
  unfold tailWord_3280403
  simp only [CollatzResearch.WordTrace]
  refine ⟨119646126734667654073869863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79764084489778436049246575 119646126734667654073869863)
  ·
    refine ⟨179469190102001481110804795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119646126734667654073869863 179469190102001481110804795)
    ·
      refine ⟨269203785153002221666207193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179469190102001481110804795 269203785153002221666207193)
      ·
        refine ⟨201902838864751666249655395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269203785153002221666207193 201902838864751666249655395)
        ·
          refine ⟨302854258297127499374483093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201902838864751666249655395 302854258297127499374483093)
          ·
            refine ⟨14196293357677851533178895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 302854258297127499374483093 14196293357677851533178895)
            ·
              refine ⟨21294440036516777299768343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14196293357677851533178895 21294440036516777299768343)
              ·
                refine ⟨31941660054775165949652515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21294440036516777299768343 31941660054775165949652515)
                ·
                  refine ⟨47912490082162748924478773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31941660054775165949652515 47912490082162748924478773)
                  ·
                    refine ⟨4491795945202757711669885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47912490082162748924478773 4491795945202757711669885)
                    ·
                      refine ⟨1684423479451034141876207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491795945202757711669885 1684423479451034141876207)
                      ·
                        rfl

theorem cell23_3280403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_3280403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280403 prefixEnd_3280403 := by exact prefixLift 3280403
  have htrace : WordTrace (prefixWord ++ tailWord_3280403) baseStart_3280403 baseEnd_3280403 := by
    simpa [prefixWord, tailWord_3280403, baseEnd_3280403] using wordTrace_append hprefix tailTrace_3280403
  have hstable : (prefixWord ++ tailWord_3280403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280403).length < 2 ^ (prefixWord ++ tailWord_3280403).sum := by decide
  have hdescent : baseEnd_3280403 < baseStart_3280403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280438 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_3280438 : Nat := 118140960795 + 3280438 * 2 ^ 59
def prefixEnd_3280438 : Nat := 4983230072969 + 3 ^ 40 * 3280438 * 2
def baseEnd_3280438 : Nat := 1684441451273941504938547

theorem tailTrace_3280438 : CollatzResearch.WordTrace tailWord_3280438 prefixEnd_3280438 1684441451273941504938547 := by
  unfold tailWord_3280438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477962705596303440712123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79764935526360570034262645 7477962705596303440712123)
  ·
    refine ⟨11216944058394455161068185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7477962705596303440712123 11216944058394455161068185)
    ·
      refine ⟨8412708043795841370801139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11216944058394455161068185 8412708043795841370801139)
      ·
        refine ⟨12619062065693762056201709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8412708043795841370801139 12619062065693762056201709)
        ·
          refine ⟨4732148274635160771075641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12619062065693762056201709 4732148274635160771075641)
          ·
            refine ⟨3549111205976370578306731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4732148274635160771075641 3549111205976370578306731)
            ·
              refine ⟨5323666808964555867460097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549111205976370578306731 5323666808964555867460097)
              ·
                refine ⟨3992750106723416900595073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323666808964555867460097 3992750106723416900595073)
                ·
                  refine ⟨2994562580042562675446305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3992750106723416900595073 2994562580042562675446305)
                  ·
                    refine ⟨2245921935031922006584729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2994562580042562675446305 2245921935031922006584729)
                    ·
                      refine ⟨1684441451273941504938547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245921935031922006584729 1684441451273941504938547)
                      ·
                        rfl

theorem cell23_3280438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_3280438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280438 prefixEnd_3280438 := by exact prefixLift 3280438
  have htrace : WordTrace (prefixWord ++ tailWord_3280438) baseStart_3280438 baseEnd_3280438 := by
    simpa [prefixWord, tailWord_3280438, baseEnd_3280438] using wordTrace_append hprefix tailTrace_3280438
  have hstable : (prefixWord ++ tailWord_3280438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280438).length < 2 ^ (prefixWord ++ tailWord_3280438).sum := by decide
  have hdescent : baseEnd_3280438 < baseStart_3280438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280480 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3]
def baseStart_3280480 : Nat := 118140960795 + 3280480 * 2 ^ 59
def prefixEnd_3280480 : Nat := 4983230072969 + 3 ^ 40 * 3280480 * 2
def baseEnd_3280480 : Nat := 1684463017461430340613353

theorem tailTrace_3280480 : CollatzResearch.WordTrace tailWord_3280480 prefixEnd_3280480 1684463017461430340613353 := by
  unfold tailWord_3280480
  simp only [CollatzResearch.WordTrace]
  refine ⟨59824467577694348112211447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79765956770259130816281929 59824467577694348112211447)
  ·
    refine ⟨89736701366541522168317171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59824467577694348112211447 89736701366541522168317171)
    ·
      refine ⟨134605052049812283252475757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89736701366541522168317171 134605052049812283252475757)
      ·
        refine ⟨50476894518679606219678409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134605052049812283252475757 50476894518679606219678409)
        ·
          refine ⟨37857670889009704664758807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50476894518679606219678409 37857670889009704664758807)
          ·
            refine ⟨56786506333514556997138211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37857670889009704664758807 56786506333514556997138211)
            ·
              refine ⟨85179759500271835495707317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56786506333514556997138211 85179759500271835495707317)
              ·
                refine ⟨7985602453150484577722561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85179759500271835495707317 7985602453150484577722561)
                ·
                  refine ⟨5989201839862863433291921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7985602453150484577722561 5989201839862863433291921)
                  ·
                    refine ⟨4491901379897147574968941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5989201839862863433291921 4491901379897147574968941)
                    ·
                      refine ⟨1684463017461430340613353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491901379897147574968941 1684463017461430340613353)
                      ·
                        rfl

theorem cell23_3280480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_3280480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280480 prefixEnd_3280480 := by exact prefixLift 3280480
  have htrace : WordTrace (prefixWord ++ tailWord_3280480) baseStart_3280480 baseEnd_3280480 := by
    simpa [prefixWord, tailWord_3280480, baseEnd_3280480] using wordTrace_append hprefix tailTrace_3280480
  have hstable : (prefixWord ++ tailWord_3280480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280480).length < 2 ^ (prefixWord ++ tailWord_3280480).sum := by decide
  have hdescent : baseEnd_3280480 < baseStart_3280480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280483 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 8]
def baseStart_3280483 : Nat := 118140960795 + 3280483 * 2 ^ 59
def prefixEnd_3280483 : Nat := 4983230072969 + 3 ^ 40 * 3280483 * 2
def baseEnd_3280483 : Nat := 187162728655932647652871

theorem tailTrace_3280483 : CollatzResearch.WordTrace tailWord_3280483 prefixEnd_3280483 187162728655932647652871 := by
  unfold tailWord_3280483
  simp only [CollatzResearch.WordTrace]
  refine ⟨119649044574377827736782103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79766029716251885157854735 119649044574377827736782103)
  ·
    refine ⟨179473566861566741605173155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119649044574377827736782103 179473566861566741605173155)
    ·
      refine ⟨269210350292350112407759733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179473566861566741605173155 269210350292350112407759733)
      ·
        refine ⟨25238470339907823038227475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269210350292350112407759733 25238470339907823038227475)
        ·
          refine ⟨37857705509861734557341213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25238470339907823038227475 37857705509861734557341213)
          ·
            refine ⟨14196639566198150459002955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37857705509861734557341213 14196639566198150459002955)
            ·
              refine ⟨21294959349297225688504433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14196639566198150459002955 21294959349297225688504433)
              ·
                refine ⟨15971219511972919266378325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21294959349297225688504433 15971219511972919266378325)
                ·
                  refine ⟨187162728655932647652871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15971219511972919266378325 187162728655932647652871)
                  ·
                    rfl

theorem cell23_3280483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 8].length) (baseStart_3280483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280483 prefixEnd_3280483 := by exact prefixLift 3280483
  have htrace : WordTrace (prefixWord ++ tailWord_3280483) baseStart_3280483 baseEnd_3280483 := by
    simpa [prefixWord, tailWord_3280483, baseEnd_3280483] using wordTrace_append hprefix tailTrace_3280483
  have hstable : (prefixWord ++ tailWord_3280483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280483).length < 2 ^ (prefixWord ++ tailWord_3280483).sum := by decide
  have hdescent : baseEnd_3280483 < baseStart_3280483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280547 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 1, 5]
def baseStart_3280547 : Nat := 118140960795 + 3280547 * 2 ^ 59
def prefixEnd_3280547 : Nat := 4983230072969 + 3 ^ 40 * 3280547 * 2
def baseEnd_3280547 : Nat := 561499140221760526158515

theorem tailTrace_3280547 : CollatzResearch.WordTrace tailWord_3280547 prefixEnd_3280547 561499140221760526158515 := by
  unfold tailWord_3280547
  simp only [CollatzResearch.WordTrace]
  refine ⟨119651378846145966667111895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79767585897430644444741263 119651378846145966667111895)
  ·
    refine ⟨179477068269218950000667843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119651378846145966667111895 179477068269218950000667843)
    ·
      refine ⟨269215602403828425001001765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179477068269218950000667843 269215602403828425001001765)
      ·
        refine ⟨50477925450717829687687831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269215602403828425001001765 50477925450717829687687831)
        ·
          refine ⟨75716888176076744531531747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50477925450717829687687831 75716888176076744531531747)
          ·
            refine ⟨113575332264115116797297621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75716888176076744531531747 113575332264115116797297621)
            ·
              refine ⟨2661921849940198049936663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 113575332264115116797297621 2661921849940198049936663)
              ·
                refine ⟨3992882774910297074904995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661921849940198049936663 3992882774910297074904995)
                ·
                  refine ⟨5989324162365445612357493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992882774910297074904995 5989324162365445612357493)
                  ·
                    refine ⟨561499140221760526158515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5989324162365445612357493 561499140221760526158515)
                    ·
                      rfl

theorem cell23_3280547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 5].length) (baseStart_3280547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280547 prefixEnd_3280547 := by exact prefixLift 3280547
  have htrace : WordTrace (prefixWord ++ tailWord_3280547) baseStart_3280547 baseEnd_3280547 := by
    simpa [prefixWord, tailWord_3280547, baseEnd_3280547] using wordTrace_append hprefix tailTrace_3280547
  have hstable : (prefixWord ++ tailWord_3280547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280547).length < 2 ^ (prefixWord ++ tailWord_3280547).sum := by decide
  have hdescent : baseEnd_3280547 < baseStart_3280547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280560 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 4, 4]
def baseStart_3280560 : Nat := 118140960795 + 3280560 * 2 ^ 59
def prefixEnd_3280560 : Nat := 4983230072969 + 3 ^ 40 * 3280560 * 2
def baseEnd_3280560 : Nat := 561501365304596675870995

theorem tailTrace_3280560 : CollatzResearch.WordTrace tailWord_3280560 prefixEnd_3280560 561501365304596675870995 := by
  unfold tailWord_3280560
  simp only [CollatzResearch.WordTrace]
  refine ⟨59825926497549434943667567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79767901996732579924890089 59825926497549434943667567)
  ·
    refine ⟨89738889746324152415501351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59825926497549434943667567 89738889746324152415501351)
    ·
      refine ⟨134608334619486228623252027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89738889746324152415501351 134608334619486228623252027)
      ·
        refine ⟨201912501929229342934878041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134608334619486228623252027 201912501929229342934878041)
        ·
          refine ⟨151434376446922007201158531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201912501929229342934878041 151434376446922007201158531)
          ·
            refine ⟨227151564670383010801737797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151434376446922007201158531 227151564670383010801737797)
            ·
              refine ⟨42590918375696814525325837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227151564670383010801737797 42590918375696814525325837)
              ·
                refine ⟨15971594390886305446997189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42590918375696814525325837 15971594390886305446997189)
                ·
                  refine ⟨2994673948291182271311973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15971594390886305446997189 2994673948291182271311973)
                  ·
                    refine ⟨561501365304596675870995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994673948291182271311973 561501365304596675870995)
                    ·
                      rfl

theorem cell23_3280560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_3280560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280560 prefixEnd_3280560 := by exact prefixLift 3280560
  have htrace : WordTrace (prefixWord ++ tailWord_3280560) baseStart_3280560 baseEnd_3280560 := by
    simpa [prefixWord, tailWord_3280560, baseEnd_3280560] using wordTrace_append hprefix tailTrace_3280560
  have hstable : (prefixWord ++ tailWord_3280560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280560).length < 2 ^ (prefixWord ++ tailWord_3280560).sum := by decide
  have hdescent : baseEnd_3280560 < baseStart_3280560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280584 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_3280584 : Nat := 118140960795 + 3280584 * 2 ^ 59
def prefixEnd_3280584 : Nat := 4983230072969 + 3 ^ 40 * 3280584 * 2
def baseEnd_3280584 : Nat := 1684516419449497933712875

theorem tailTrace_3280584 : CollatzResearch.WordTrace tailWord_3280584 prefixEnd_3280584 1684516419449497933712875 := by
  unfold tailWord_3280584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59826364173505960993104403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79768485564674614657472537 59826364173505960993104403)
  ·
    refine ⟨89739546260258941489656605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59826364173505960993104403 89739546260258941489656605)
    ·
      refine ⟨33652329847597103058621227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89739546260258941489656605 33652329847597103058621227)
      ·
        refine ⟨50478494771395654587931841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33652329847597103058621227 50478494771395654587931841)
        ·
          refine ⟨37858871078546740940948881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50478494771395654587931841 37858871078546740940948881)
          ·
            refine ⟨28394153308910055705711661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37858871078546740940948881 28394153308910055705711661)
            ·
              refine ⟨10647807490841270889641873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28394153308910055705711661 10647807490841270889641873)
              ·
                refine ⟨7985855618130953167231405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10647807490841270889641873 7985855618130953167231405)
                ·
                  refine ⟨2994695856799107437711777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7985855618130953167231405 2994695856799107437711777)
                  ·
                    refine ⟨2246021892599330578283833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2994695856799107437711777 2246021892599330578283833)
                    ·
                      refine ⟨1684516419449497933712875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246021892599330578283833 1684516419449497933712875)
                      ·
                        rfl

theorem cell23_3280584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_3280584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280584 prefixEnd_3280584 := by exact prefixLift 3280584
  have htrace : WordTrace (prefixWord ++ tailWord_3280584) baseStart_3280584 baseEnd_3280584 := by
    simpa [prefixWord, tailWord_3280584, baseEnd_3280584] using wordTrace_append hprefix tailTrace_3280584
  have hstable : (prefixWord ++ tailWord_3280584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280584).length < 2 ^ (prefixWord ++ tailWord_3280584).sum := by decide
  have hdescent : baseEnd_3280584 < baseStart_3280584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280588 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3280588 : Nat := 118140960795 + 3280588 * 2 ^ 59
def prefixEnd_3280588 : Nat := 4983230072969 + 3 ^ 40 * 3280588 * 2
def baseEnd_3280588 : Nat := 1684518473372115918062857

theorem tailTrace_3280588 : CollatzResearch.WordTrace tailWord_3280588 prefixEnd_3280588 1684518473372115918062857 := by
  unfold tailWord_3280588
  simp only [CollatzResearch.WordTrace]
  refine ⟨59826437119498715334677209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79768582825998287112902945 59826437119498715334677209)
  ·
    refine ⟨44869827839624036501007907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59826437119498715334677209 44869827839624036501007907)
    ·
      refine ⟨67304741759436054751511861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44869827839624036501007907 67304741759436054751511861)
      ·
        refine ⟨6309819539947130132954237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67304741759436054751511861 6309819539947130132954237)
        ·
          refine ⟨2366182327480173799857839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6309819539947130132954237 2366182327480173799857839)
          ·
            refine ⟨3549273491220260699786759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366182327480173799857839 3549273491220260699786759)
            ·
              refine ⟨5323910236830391049680139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549273491220260699786759 5323910236830391049680139)
              ·
                refine ⟨7985865355245586574520209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323910236830391049680139 7985865355245586574520209)
                ·
                  refine ⟨5989399016434189930890157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7985865355245586574520209 5989399016434189930890157)
                  ·
                    refine ⟨2246024631162821224083809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5989399016434189930890157 2246024631162821224083809)
                    ·
                      refine ⟨1684518473372115918062857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246024631162821224083809 1684518473372115918062857)
                      ·
                        rfl

theorem cell23_3280588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3280588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280588 prefixEnd_3280588 := by exact prefixLift 3280588
  have htrace : WordTrace (prefixWord ++ tailWord_3280588) baseStart_3280588 baseEnd_3280588 := by
    simpa [prefixWord, tailWord_3280588, baseEnd_3280588] using wordTrace_append hprefix tailTrace_3280588
  have hstable : (prefixWord ++ tailWord_3280588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280588).length < 2 ^ (prefixWord ++ tailWord_3280588).sum := by decide
  have hdescent : baseEnd_3280588 < baseStart_3280588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280601 : List Nat := [1, 2, 1, 2, 3, 3, 1, 5, 1, 2, 2]
def baseStart_3280601 : Nat := 118140960795 + 3280601 * 2 ^ 59
def prefixEnd_3280601 : Nat := 4983230072969 + 3 ^ 40 * 3280601 * 2
def baseEnd_3280601 : Nat := 1684525148620624367200297

theorem tailTrace_3280601 : CollatzResearch.WordTrace tailWord_3280601 prefixEnd_3280601 1684525148620624367200297 := by
  unfold tailWord_3280601
  simp only [CollatzResearch.WordTrace]
  refine ⟨119653348387950333889577657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79768898925300222593051771 119653348387950333889577657)
  ·
    refine ⟨89740011290962750417183243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119653348387950333889577657 89740011290962750417183243)
    ·
      refine ⟨134610016936444125625774865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89740011290962750417183243 134610016936444125625774865)
      ·
        refine ⟨100957512702333094219331149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134610016936444125625774865 100957512702333094219331149)
        ·
          refine ⟨37859067263374910332249181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100957512702333094219331149 37859067263374910332249181)
          ·
            refine ⟨14197150223765591374593443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37859067263374910332249181 14197150223765591374593443)
            ·
              refine ⟨21295725335648387061890165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14197150223765591374593443 21295725335648387061890165)
              ·
                refine ⟨1996474250217036287052203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21295725335648387061890165 1996474250217036287052203)
                ·
                  refine ⟨2994711375325554430578305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996474250217036287052203 2994711375325554430578305)
                  ·
                    refine ⟨2246033531494165822933729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2994711375325554430578305 2246033531494165822933729)
                    ·
                      refine ⟨1684525148620624367200297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246033531494165822933729 1684525148620624367200297)
                      ·
                        rfl

theorem cell23_3280601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_3280601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280601 prefixEnd_3280601 := by exact prefixLift 3280601
  have htrace : WordTrace (prefixWord ++ tailWord_3280601) baseStart_3280601 baseEnd_3280601 := by
    simpa [prefixWord, tailWord_3280601, baseEnd_3280601] using wordTrace_append hprefix tailTrace_3280601
  have hstable : (prefixWord ++ tailWord_3280601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280601).length < 2 ^ (prefixWord ++ tailWord_3280601).sum := by decide
  have hdescent : baseEnd_3280601 < baseStart_3280601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280611 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 2, 4]
def baseStart_3280611 : Nat := 118140960795 + 3280611 * 2 ^ 59
def prefixEnd_3280611 : Nat := 4983230072969 + 3 ^ 40 * 3280611 * 2
def baseEnd_3280611 : Nat := 561510094475723109358417

theorem tailTrace_3280611 : CollatzResearch.WordTrace tailWord_3280611 prefixEnd_3280611 561510094475723109358417 := by
  unfold tailWord_3280611
  simp only [CollatzResearch.WordTrace]
  refine ⟨119653713117914105597441687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79769142078609403731627791 119653713117914105597441687)
  ·
    refine ⟨179480569676871158396162531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119653713117914105597441687 179480569676871158396162531)
    ·
      refine ⟨269220854515306737594243797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179480569676871158396162531 269220854515306737594243797)
      ·
        refine ⟨6309863777702501662365089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 269220854515306737594243797 6309863777702501662365089)
        ·
          refine ⟨4732397833276876246773817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6309863777702501662365089 4732397833276876246773817)
          ·
            refine ⟨3549298374957657185080363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4732397833276876246773817 3549298374957657185080363)
            ·
              refine ⟨5323947562436485777620545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549298374957657185080363 5323947562436485777620545)
              ·
                refine ⟨3992960671827364333215409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323947562436485777620545 3992960671827364333215409)
                ·
                  refine ⟨2994720503870523249911557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3992960671827364333215409 2994720503870523249911557)
                  ·
                    refine ⟨561510094475723109358417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994720503870523249911557 561510094475723109358417)
                    ·
                      rfl

theorem cell23_3280611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 4].length) (baseStart_3280611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280611 prefixEnd_3280611 := by exact prefixLift 3280611
  have htrace : WordTrace (prefixWord ++ tailWord_3280611) baseStart_3280611 baseEnd_3280611 := by
    simpa [prefixWord, tailWord_3280611, baseEnd_3280611] using wordTrace_append hprefix tailTrace_3280611
  have hstable : (prefixWord ++ tailWord_3280611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280611).length < 2 ^ (prefixWord ++ tailWord_3280611).sum := by decide
  have hdescent : baseEnd_3280611 < baseStart_3280611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280627 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 5, 3, 2]
def baseStart_3280627 : Nat := 118140960795 + 3280627 * 2 ^ 59
def prefixEnd_3280627 : Nat := 4983230072969 + 3 ^ 40 * 3280627 * 2
def baseEnd_3280627 : Nat := 1684538499117641265475177

theorem tailTrace_3280627 : CollatzResearch.WordTrace tailWord_3280627 prefixEnd_3280627 1684538499117641265475177 := by
  unfold tailWord_3280627
  simp only [CollatzResearch.WordTrace]
  refine ⟨119654296685856140330024135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79769531123904093553349423 119654296685856140330024135)
  ·
    refine ⟨179481445028784210495036203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119654296685856140330024135 179481445028784210495036203)
    ·
      refine ⟨269222167543176315742554305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179481445028784210495036203 269222167543176315742554305)
      ·
        refine ⟨201916625657382236806915729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269222167543176315742554305 201916625657382236806915729)
        ·
          refine ⟨151437469243036677605186797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201916625657382236806915729 151437469243036677605186797)
          ·
            refine ⟨56789050966138754101945049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151437469243036677605186797 56789050966138754101945049)
            ·
              refine ⟨42591788224604065576458787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56789050966138754101945049 42591788224604065576458787)
              ·
                refine ⟨63887682336906098364688181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42591788224604065576458787 63887682336906098364688181)
                ·
                  refine ⟨5989470219084946721689517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63887682336906098364688181 5989470219084946721689517)
                  ·
                    refine ⟨2246051332156855020633569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5989470219084946721689517 2246051332156855020633569)
                    ·
                      refine ⟨1684538499117641265475177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246051332156855020633569 1684538499117641265475177)
                      ·
                        rfl

theorem cell23_3280627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3, 2].length) (baseStart_3280627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280627 prefixEnd_3280627 := by exact prefixLift 3280627
  have htrace : WordTrace (prefixWord ++ tailWord_3280627) baseStart_3280627 baseEnd_3280627 := by
    simpa [prefixWord, tailWord_3280627, baseEnd_3280627] using wordTrace_append hprefix tailTrace_3280627
  have hstable : (prefixWord ++ tailWord_3280627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280627).length < 2 ^ (prefixWord ++ tailWord_3280627).sum := by decide
  have hdescent : baseEnd_3280627 < baseStart_3280627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280646 : List Nat := [6, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3280646 : Nat := 118140960795 + 3280646 * 2 ^ 59
def prefixEnd_3280646 : Nat := 4983230072969 + 3 ^ 40 * 3280646 * 2
def baseEnd_3280646 : Nat := 1684548255250076691137591

theorem tailTrace_3280646 : CollatzResearch.WordTrace tailWord_3280646 prefixEnd_3280646 1684548255250076691137591 := by
  unfold tailWord_3280646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3739218427274603330467681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79769993115191537716643861 3739218427274603330467681)
  ·
    refine ⟨2804413820455952497850761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3739218427274603330467681 2804413820455952497850761)
    ·
      refine ⟨2103310365341964373388071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2804413820455952497850761 2103310365341964373388071)
      ·
        refine ⟨3154965548012946560082107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103310365341964373388071 3154965548012946560082107)
        ·
          refine ⟨4732448322019419840123161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154965548012946560082107 4732448322019419840123161)
          ·
            refine ⟨3549336241514564880092371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4732448322019419840123161 3549336241514564880092371)
            ·
              refine ⟨5324004362271847320138557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549336241514564880092371 5324004362271847320138557)
              ·
                refine ⟨1996501635851942745051959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5324004362271847320138557 1996501635851942745051959)
                ·
                  refine ⟨2994752453777914117577939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996501635851942745051959 2994752453777914117577939)
                  ·
                    refine ⟨4492128680666871176366909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2994752453777914117577939 4492128680666871176366909)
                    ·
                      refine ⟨1684548255250076691137591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4492128680666871176366909 1684548255250076691137591)
                      ·
                        rfl

theorem cell23_3280646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3280646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280646 prefixEnd_3280646 := by exact prefixLift 3280646
  have htrace : WordTrace (prefixWord ++ tailWord_3280646) baseStart_3280646 baseEnd_3280646 := by
    simpa [prefixWord, tailWord_3280646, baseEnd_3280646] using wordTrace_append hprefix tailTrace_3280646
  have hstable : (prefixWord ++ tailWord_3280646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280646).length < 2 ^ (prefixWord ++ tailWord_3280646).sum := by decide
  have hdescent : baseEnd_3280646 < baseStart_3280646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280657 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 3, 4, 2]
def baseStart_3280657 : Nat := 118140960795 + 3280657 * 2 ^ 59
def prefixEnd_3280657 : Nat := 4983230072969 + 3 ^ 40 * 3280657 * 2
def baseEnd_3280657 : Nat := 1684553903537276148100039

theorem tailTrace_3280657 : CollatzResearch.WordTrace tailWord_3280657 prefixEnd_3280657 1684553903537276148100039 := by
  unfold tailWord_3280657
  simp only [CollatzResearch.WordTrace]
  refine ⟨119655390875747455453616225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79770260583831636969077483 119655390875747455453616225)
  ·
    refine ⟨89741543156810591590212169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119655390875747455453616225 89741543156810591590212169)
    ·
      refine ⟨67306157367607943692659127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89741543156810591590212169 67306157367607943692659127)
      ·
        refine ⟨100959236051411915538988691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67306157367607943692659127 100959236051411915538988691)
        ·
          refine ⟨151438854077117873308483037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100959236051411915538988691 151438854077117873308483037)
          ·
            refine ⟨56789570278919202490681139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151438854077117873308483037 56789570278919202490681139)
            ·
              refine ⟨85184355418378803736021709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56789570278919202490681139 85184355418378803736021709)
              ·
                refine ⟨31944133281892051401008141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85184355418378803736021709 31944133281892051401008141)
                ·
                  refine ⟨11979049980709519275378053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31944133281892051401008141 11979049980709519275378053)
                  ·
                    refine ⟨2246071871383034864133385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11979049980709519275378053 2246071871383034864133385)
                    ·
                      refine ⟨1684553903537276148100039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246071871383034864133385 1684553903537276148100039)
                      ·
                        rfl

theorem cell23_3280657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_3280657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280657 prefixEnd_3280657 := by exact prefixLift 3280657
  have htrace : WordTrace (prefixWord ++ tailWord_3280657) baseStart_3280657 baseEnd_3280657 := by
    simpa [prefixWord, tailWord_3280657, baseEnd_3280657] using wordTrace_append hprefix tailTrace_3280657
  have hstable : (prefixWord ++ tailWord_3280657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280657).length < 2 ^ (prefixWord ++ tailWord_3280657).sum := by decide
  have hdescent : baseEnd_3280657 < baseStart_3280657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280694 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3280694 : Nat := 118140960795 + 3280694 * 2 ^ 59
def prefixEnd_3280694 : Nat := 4983230072969 + 3 ^ 40 * 3280694 * 2
def baseEnd_3280694 : Nat := 1684572902321492503337369

theorem tailTrace_3280694 : CollatzResearch.WordTrace tailWord_3280694 prefixEnd_3280694 1684572902321492503337369 := by
  unfold tailWord_3280694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478546273538338173294571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79771160251075607181808757 7478546273538338173294571)
  ·
    refine ⟨11217819410307507259941857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7478546273538338173294571 11217819410307507259941857)
    ·
      refine ⟨8413364557730630444956393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11217819410307507259941857 8413364557730630444956393)
      ·
        refine ⟨6310023418297972833717295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8413364557730630444956393 6310023418297972833717295)
        ·
          refine ⟨9465035127446959250575943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310023418297972833717295 9465035127446959250575943)
          ·
            refine ⟨14197552691170438875863915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9465035127446959250575943 14197552691170438875863915)
            ·
              refine ⟨21296329036755658313795873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14197552691170438875863915 21296329036755658313795873)
              ·
                refine ⟨15972246777566743735346905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21296329036755658313795873 15972246777566743735346905)
                ·
                  refine ⟨11979185083175057801510179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15972246777566743735346905 11979185083175057801510179)
                  ·
                    refine ⟨17968777624762586702265269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11979185083175057801510179 17968777624762586702265269)
                    ·
                      refine ⟨1684572902321492503337369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17968777624762586702265269 1684572902321492503337369)
                      ·
                        rfl

theorem cell23_3280694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3280694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280694 prefixEnd_3280694 := by exact prefixLift 3280694
  have htrace : WordTrace (prefixWord ++ tailWord_3280694) baseStart_3280694 baseEnd_3280694 := by
    simpa [prefixWord, tailWord_3280694, baseEnd_3280694] using wordTrace_append hprefix tailTrace_3280694
  have hstable : (prefixWord ++ tailWord_3280694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280694).length < 2 ^ (prefixWord ++ tailWord_3280694).sum := by decide
  have hdescent : baseEnd_3280694 < baseStart_3280694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280791 : List Nat := [1, 1, 3, 3, 1, 3, 2, 4, 1, 4]
def baseStart_3280791 : Nat := 118140960795 + 3280791 * 2 ^ 59
def prefixEnd_3280791 : Nat := 4983230072969 + 3 ^ 40 * 3280791 * 2
def baseEnd_3280791 : Nat := 561540903314992874608141

theorem tailTrace_3280791 : CollatzResearch.WordTrace tailWord_3280791 prefixEnd_3280791 561540903314992874608141 := by
  unfold tailWord_3280791
  simp only [CollatzResearch.WordTrace]
  refine ⟨119660278257261996338994227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79773518838174664225996151 119660278257261996338994227)
  ·
    refine ⟨179490417385892994508491341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119660278257261996338994227 179490417385892994508491341)
    ·
      refine ⟨67308906519709872940684253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179490417385892994508491341 67308906519709872940684253)
      ·
        refine ⟨25240839944891202352756595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67308906519709872940684253 25240839944891202352756595)
        ·
          refine ⟨37861259917336803529134893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25240839944891202352756595 37861259917336803529134893)
          ·
            refine ⟨14197972469001301323425585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37861259917336803529134893 14197972469001301323425585)
            ·
              refine ⟨10648479351750975992569189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14197972469001301323425585 10648479351750975992569189)
              ·
                refine ⟨1996589878453307998606723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10648479351750975992569189 1996589878453307998606723)
                ·
                  refine ⟨2994884817679961997910085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996589878453307998606723 2994884817679961997910085)
                  ·
                    refine ⟨561540903314992874608141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994884817679961997910085 561540903314992874608141)
                    ·
                      rfl

theorem cell23_3280791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_3280791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280791 prefixEnd_3280791 := by exact prefixLift 3280791
  have htrace : WordTrace (prefixWord ++ tailWord_3280791) baseStart_3280791 baseEnd_3280791 := by
    simpa [prefixWord, tailWord_3280791, baseEnd_3280791] using wordTrace_append hprefix tailTrace_3280791
  have hstable : (prefixWord ++ tailWord_3280791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280791).length < 2 ^ (prefixWord ++ tailWord_3280791).sum := by decide
  have hdescent : baseEnd_3280791 < baseStart_3280791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280824 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 1, 5, 2]
def baseStart_3280824 : Nat := 118140960795 + 3280824 * 2 ^ 59
def prefixEnd_3280824 : Nat := 4983230072969 + 3 ^ 40 * 3280824 * 2
def baseEnd_3280824 : Nat := 1684639654806576994711771

theorem tailTrace_3280824 : CollatzResearch.WordTrace tailWord_3280824 prefixEnd_3280824 1684639654806576994711771 := by
  unfold tailWord_3280824
  simp only [CollatzResearch.WordTrace]
  refine ⟨59830740933071221487472763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79774321244094961983297017 59830740933071221487472763)
  ·
    refine ⟨89746111399606832231209145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59830740933071221487472763 89746111399606832231209145)
    ·
      refine ⟨67309583549705124173406859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89746111399606832231209145 67309583549705124173406859)
      ·
        refine ⟨100964375324557686260110289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67309583549705124173406859 100964375324557686260110289)
        ·
          refine ⟨75723281493418264695082717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100964375324557686260110289 75723281493418264695082717)
          ·
            refine ⟨28396230560031849260656019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75723281493418264695082717 28396230560031849260656019)
            ·
              refine ⟨42594345840047773890984029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28396230560031849260656019 42594345840047773890984029)
              ·
                refine ⟨15972879690017915209119011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42594345840047773890984029 15972879690017915209119011)
                ·
                  refine ⟨23959319535026872813678517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15972879690017915209119011 23959319535026872813678517)
                  ·
                    refine ⟨2246186206408769326282361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23959319535026872813678517 2246186206408769326282361)
                    ·
                      refine ⟨1684639654806576994711771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246186206408769326282361 1684639654806576994711771)
                      ·
                        rfl

theorem cell23_3280824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_3280824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280824 prefixEnd_3280824 := by exact prefixLift 3280824
  have htrace : WordTrace (prefixWord ++ tailWord_3280824) baseStart_3280824 baseEnd_3280824 := by
    simpa [prefixWord, tailWord_3280824, baseEnd_3280824] using wordTrace_append hprefix tailTrace_3280824
  have hstable : (prefixWord ++ tailWord_3280824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280824).length < 2 ^ (prefixWord ++ tailWord_3280824).sum := by decide
  have hdescent : baseEnd_3280824 < baseStart_3280824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280871 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3280871 : Nat := 118140960795 + 3280871 * 2 ^ 59
def prefixEnd_3280871 : Nat := 4983230072969 + 3 ^ 40 * 3280871 * 2
def baseEnd_3280871 : Nat := 1684663788397338310824055

theorem tailTrace_3280871 : CollatzResearch.WordTrace tailWord_3280871 prefixEnd_3280871 1684663788397338310824055 := by
  unfold tailWord_3280871
  simp only [CollatzResearch.WordTrace]
  refine ⟨119663196096972170001906467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79775464064648113334604311 119663196096972170001906467)
  ·
    refine ⟨179494794145458255002859701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119663196096972170001906467 179494794145458255002859701)
    ·
      refine ⟨16827636951136711406518097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179494794145458255002859701 16827636951136711406518097)
      ·
        refine ⟨12620727713352533554888573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16827636951136711406518097 12620727713352533554888573)
        ·
          refine ⟨4732772892507200083083215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12620727713352533554888573 4732772892507200083083215)
          ·
            refine ⟨7099159338760800124624823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732772892507200083083215 7099159338760800124624823)
            ·
              refine ⟨10648739008141200186937235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099159338760800124624823 10648739008141200186937235)
              ·
                refine ⟨15973108512211800280405853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10648739008141200186937235 15973108512211800280405853)
                ·
                  refine ⟨5989915692079425105152195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15973108512211800280405853 5989915692079425105152195)
                  ·
                    refine ⟨8984873538119137657728293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5989915692079425105152195 8984873538119137657728293)
                    ·
                      refine ⟨1684663788397338310824055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8984873538119137657728293 1684663788397338310824055)
                      ·
                        rfl

theorem cell23_3280871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3280871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280871 prefixEnd_3280871 := by exact prefixLift 3280871
  have htrace : WordTrace (prefixWord ++ tailWord_3280871) baseStart_3280871 baseEnd_3280871 := by
    simpa [prefixWord, tailWord_3280871, baseEnd_3280871] using wordTrace_append hprefix tailTrace_3280871
  have hstable : (prefixWord ++ tailWord_3280871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280871).length < 2 ^ (prefixWord ++ tailWord_3280871).sum := by decide
  have hdescent : baseEnd_3280871 < baseStart_3280871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280894 : List Nat := [4, 2, 2, 2, 1, 12]
def baseStart_3280894 : Nat := 118140960795 + 3280894 * 2 ^ 59
def prefixEnd_3280894 : Nat := 4983230072969 + 3 ^ 40 * 3280894 * 2
def baseEnd_3280894 : Nat := 6932821392808196382043

theorem tailTrace_3280894 : CollatzResearch.WordTrace tailWord_3280894 prefixEnd_3280894 6932821392808196382043 := by
  unfold tailWord_3280894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14958004371986105616249217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79776023317259229953329157 14958004371986105616249217)
  ·
    refine ⟨11218503278989579212186913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14958004371986105616249217 11218503278989579212186913)
    ·
      refine ⟨8413877459242184409140185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11218503278989579212186913 8413877459242184409140185)
      ·
        refine ⟨6310408094431638306855139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8413877459242184409140185 6310408094431638306855139)
        ·
          refine ⟨9465612141647457460282709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310408094431638306855139 9465612141647457460282709)
          ·
            refine ⟨6932821392808196382043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9465612141647457460282709 6932821392808196382043)
            ·
              rfl

theorem cell23_3280894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 12].length) (baseStart_3280894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280894 prefixEnd_3280894 := by exact prefixLift 3280894
  have htrace : WordTrace (prefixWord ++ tailWord_3280894) baseStart_3280894 baseEnd_3280894 := by
    simpa [prefixWord, tailWord_3280894, baseEnd_3280894] using wordTrace_append hprefix tailTrace_3280894
  have hstable : (prefixWord ++ tailWord_3280894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280894).length < 2 ^ (prefixWord ++ tailWord_3280894).sum := by decide
  have hdescent : baseEnd_3280894 < baseStart_3280894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280904 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3280904 : Nat := 118140960795 + 3280904 * 2 ^ 59
def prefixEnd_3280904 : Nat := 4983230072969 + 3 ^ 40 * 3280904 * 2
def baseEnd_3280904 : Nat := 1684680733258936681711403

theorem tailTrace_3280904 : CollatzResearch.WordTrace tailWord_3280904 prefixEnd_3280904 1684680733258936681711403 := by
  unfold tailWord_3280904
  simp only [CollatzResearch.WordTrace]
  refine ⟨59832199852926308318928883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79776266470568411091905177 59832199852926308318928883)
  ·
    refine ⟨89748299779389462478393325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59832199852926308318928883 89748299779389462478393325)
    ·
      refine ⟨33655612417271048429397497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89748299779389462478393325 33655612417271048429397497)
      ·
        refine ⟨25241709312953286322048123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33655612417271048429397497 25241709312953286322048123)
        ·
          refine ⟨37862563969429929483072185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25241709312953286322048123 37862563969429929483072185)
          ·
            refine ⟨28396922977072447112304139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37862563969429929483072185 28396922977072447112304139)
            ·
              refine ⟨42595384465608670668456209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28396922977072447112304139 42595384465608670668456209)
              ·
                refine ⟨31946538349206503001342157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42595384465608670668456209 31946538349206503001342157)
                ·
                  refine ⟨11979951880952438625503309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31946538349206503001342157 11979951880952438625503309)
                  ·
                    refine ⟨4492481955357164484563741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11979951880952438625503309 4492481955357164484563741)
                    ·
                      refine ⟨1684680733258936681711403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4492481955357164484563741 1684680733258936681711403)
                      ·
                        rfl

theorem cell23_3280904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3280904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280904 prefixEnd_3280904 := by exact prefixLift 3280904
  have htrace : WordTrace (prefixWord ++ tailWord_3280904) baseStart_3280904 baseEnd_3280904 := by
    simpa [prefixWord, tailWord_3280904, baseEnd_3280904] using wordTrace_append hprefix tailTrace_3280904
  have hstable : (prefixWord ++ tailWord_3280904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280904).length < 2 ^ (prefixWord ++ tailWord_3280904).sum := by decide
  have hdescent : baseEnd_3280904 < baseStart_3280904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280907 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 9]
def baseStart_3280907 : Nat := 118140960795 + 3280907 * 2 ^ 59
def prefixEnd_3280907 : Nat := 4983230072969 + 3 ^ 40 * 3280907 * 2
def baseEnd_3280907 : Nat := 561560757900300056657963

theorem tailTrace_3280907 : CollatzResearch.WordTrace tailWord_3280907 prefixEnd_3280907 561560757900300056657963 := by
  unfold tailWord_3280907
  simp only [CollatzResearch.WordTrace]
  refine ⟨119664509124841748150216975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79776339416561165433477983 119664509124841748150216975)
  ·
    refine ⟨179496763687262622225325463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119664509124841748150216975 179496763687262622225325463)
    ·
      refine ⟨269245145530893933337988195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179496763687262622225325463 269245145530893933337988195)
      ·
        refine ⟨403867718296340900006982293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269245145530893933337988195 403867718296340900006982293)
        ·
          refine ⟨18931299295140979687827295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 403867718296340900006982293 18931299295140979687827295)
          ·
            refine ⟨28396948942711469531740943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18931299295140979687827295 28396948942711469531740943)
            ·
              refine ⟨42595423414067204297611415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28396948942711469531740943 42595423414067204297611415)
              ·
                refine ⟨63893135121100806446417123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42595423414067204297611415 63893135121100806446417123)
                ·
                  refine ⟨95839702681651209669625685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63893135121100806446417123 95839702681651209669625685)
                  ·
                    refine ⟨561560757900300056657963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 95839702681651209669625685 561560757900300056657963)
                    ·
                      rfl

theorem cell23_3280907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_3280907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280907 prefixEnd_3280907 := by exact prefixLift 3280907
  have htrace : WordTrace (prefixWord ++ tailWord_3280907) baseStart_3280907 baseEnd_3280907 := by
    simpa [prefixWord, tailWord_3280907, baseEnd_3280907] using wordTrace_append hprefix tailTrace_3280907
  have hstable : (prefixWord ++ tailWord_3280907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280907).length < 2 ^ (prefixWord ++ tailWord_3280907).sum := by decide
  have hdescent : baseEnd_3280907 < baseStart_3280907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280931 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 3, 3, 2]
def baseStart_3280931 : Nat := 118140960795 + 3280931 * 2 ^ 59
def prefixEnd_3280931 : Nat := 4983230072969 + 3 ^ 40 * 3280931 * 2
def baseEnd_3280931 : Nat := 1684694597236608076073779

theorem tailTrace_3280931 : CollatzResearch.WordTrace tailWord_3280931 prefixEnd_3280931 1684694597236608076073779 := by
  unfold tailWord_3280931
  simp only [CollatzResearch.WordTrace]
  refine ⟨119665384476754800249090647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79776922984503200166060431 119665384476754800249090647)
  ·
    refine ⟨179498076715132200373635971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119665384476754800249090647 179498076715132200373635971)
    ·
      refine ⟨269247115072698300560453957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179498076715132200373635971 269247115072698300560453957)
      ·
        refine ⟨50483834076130931355085117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269247115072698300560453957 50483834076130931355085117)
        ·
          refine ⟨18931437778549099258156919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50483834076130931355085117 18931437778549099258156919)
          ·
            refine ⟨28397156667823648887235379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18931437778549099258156919 28397156667823648887235379)
            ·
              refine ⟨42595735001735473330853069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28397156667823648887235379 42595735001735473330853069)
              ·
                refine ⟨15973400625650802499069901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42595735001735473330853069 15973400625650802499069901)
                ·
                  refine ⟨5990025234619050937151213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15973400625650802499069901 5990025234619050937151213)
                  ·
                    refine ⟨2246259462982144101431705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5990025234619050937151213 2246259462982144101431705)
                    ·
                      refine ⟨1684694597236608076073779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246259462982144101431705 1684694597236608076073779)
                      ·
                        rfl

theorem cell23_3280931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_3280931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280931 prefixEnd_3280931 := by exact prefixLift 3280931
  have htrace : WordTrace (prefixWord ++ tailWord_3280931) baseStart_3280931 baseEnd_3280931 := by
    simpa [prefixWord, tailWord_3280931, baseEnd_3280931] using wordTrace_append hprefix tailTrace_3280931
  have hstable : (prefixWord ++ tailWord_3280931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280931).length < 2 ^ (prefixWord ++ tailWord_3280931).sum := by decide
  have hdescent : baseEnd_3280931 < baseStart_3280931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280982 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3280982 : Nat := 118140960795 + 3280982 * 2 ^ 59
def prefixEnd_3280982 : Nat := 4983230072969 + 3 ^ 40 * 3280982 * 2
def baseEnd_3280982 : Nat := 1684720784749987376536045

theorem tailTrace_3280982 : CollatzResearch.WordTrace tailWord_3280982 prefixEnd_3280982 1684720784749987376536045 := by
  unfold tailWord_3280982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479202787473127247449825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79778163066380023972798133 7479202787473127247449825)
  ·
    refine ⟨5609402090604845435587369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7479202787473127247449825 5609402090604845435587369)
    ·
      refine ⟨4207051567953634076690527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5609402090604845435587369 4207051567953634076690527)
      ·
        refine ⟨6310577351930451115035791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207051567953634076690527 6310577351930451115035791)
        ·
          refine ⟨9465866027895676672553687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310577351930451115035791 9465866027895676672553687)
          ·
            refine ⟨14198799041843515008830531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9465866027895676672553687 14198799041843515008830531)
            ·
              refine ⟨21298198562765272513245797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14198799041843515008830531 21298198562765272513245797)
              ·
                refine ⟨3993412230518488596233587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21298198562765272513245797 3993412230518488596233587)
                ·
                  refine ⟨5990118345777732894350381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993412230518488596233587 5990118345777732894350381)
                  ·
                    refine ⟨2246294379666649835381393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5990118345777732894350381 2246294379666649835381393)
                    ·
                      refine ⟨1684720784749987376536045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246294379666649835381393 1684720784749987376536045)
                      ·
                        rfl

theorem cell23_3280982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3280982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280982 prefixEnd_3280982 := by exact prefixLift 3280982
  have htrace : WordTrace (prefixWord ++ tailWord_3280982) baseStart_3280982 baseEnd_3280982 := by
    simpa [prefixWord, tailWord_3280982, baseEnd_3280982] using wordTrace_append hprefix tailTrace_3280982
  have hstable : (prefixWord ++ tailWord_3280982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280982).length < 2 ^ (prefixWord ++ tailWord_3280982).sum := by decide
  have hdescent : baseEnd_3280982 < baseStart_3280982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280984 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 7]
def baseStart_3280984 : Nat := 118140960795 + 3280984 * 2 ^ 59
def prefixEnd_3280984 : Nat := 4983230072969 + 3 ^ 40 * 3280984 * 2
def baseEnd_3280984 : Nat := 187191312412366263190115

theorem tailTrace_3280984 : CollatzResearch.WordTrace tailWord_3280984 prefixEnd_3280984 187191312412366263190115 := by
  unfold tailWord_3280984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59833658772781395150385003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79778211697041860200513337 59833658772781395150385003)
  ·
    refine ⟨89750488159172092725577505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59833658772781395150385003 89750488159172092725577505)
    ·
      refine ⟨67312866119379069544183129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89750488159172092725577505 67312866119379069544183129)
      ·
        refine ⟨50484649589534302158137347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67312866119379069544183129 50484649589534302158137347)
        ·
          refine ⟨75726974384301453237206021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50484649589534302158137347 75726974384301453237206021)
          ·
            refine ⟨14198807697056522481976129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75726974384301453237206021 14198807697056522481976129)
            ·
              refine ⟨10649105772792391861482097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14198807697056522481976129 10649105772792391861482097)
              ·
                refine ⟨7986829329594293896111573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10649105772792391861482097 7986829329594293896111573)
                ·
                  refine ⟨187191312412366263190115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7986829329594293896111573 187191312412366263190115)
                  ·
                    rfl

theorem cell23_3280984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 7].length) (baseStart_3280984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280984 prefixEnd_3280984 := by exact prefixLift 3280984
  have htrace : WordTrace (prefixWord ++ tailWord_3280984) baseStart_3280984 baseEnd_3280984 := by
    simpa [prefixWord, tailWord_3280984, baseEnd_3280984] using wordTrace_append hprefix tailTrace_3280984
  have hstable : (prefixWord ++ tailWord_3280984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280984).length < 2 ^ (prefixWord ++ tailWord_3280984).sum := by decide
  have hdescent : baseEnd_3280984 < baseStart_3280984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281046 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3281046 : Nat := 118140960795 + 3281046 * 2 ^ 59
def prefixEnd_3281046 : Nat := 4983230072969 + 3 ^ 40 * 3281046 * 2
def baseEnd_3281046 : Nat := 1684753647511875126135751

theorem tailTrace_3281046 : CollatzResearch.WordTrace tailWord_3281046 prefixEnd_3281046 1684753647511875126135751 := by
  unfold tailWord_3281046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479348679458635930595437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79779719247558783259684661 7479348679458635930595437)
  ·
    refine ⟨2804755754796988473973289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7479348679458635930595437 2804755754796988473973289)
    ·
      refine ⟨2103566816097741355479967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2804755754796988473973289 2103566816097741355479967)
      ·
        refine ⟨3155350224146612033219951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103566816097741355479967 3155350224146612033219951)
        ·
          refine ⟨4733025336219918049829927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155350224146612033219951 4733025336219918049829927)
          ·
            refine ⟨7099538004329877074744891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733025336219918049829927 7099538004329877074744891)
            ·
              refine ⟨10649307006494815612117337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099538004329877074744891 10649307006494815612117337)
              ·
                refine ⟨7986980254871111709088003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10649307006494815612117337 7986980254871111709088003)
                ·
                  refine ⟨11980470382306667563632005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7986980254871111709088003 11980470382306667563632005)
                  ·
                    refine ⟨2246338196682500168181001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11980470382306667563632005 2246338196682500168181001)
                    ·
                      refine ⟨1684753647511875126135751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246338196682500168181001 1684753647511875126135751)
                      ·
                        rfl

theorem cell23_3281046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3281046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281046 prefixEnd_3281046 := by exact prefixLift 3281046
  have htrace : WordTrace (prefixWord ++ tailWord_3281046) baseStart_3281046 baseEnd_3281046 := by
    simpa [prefixWord, tailWord_3281046, baseEnd_3281046] using wordTrace_append hprefix tailTrace_3281046
  have hstable : (prefixWord ++ tailWord_3281046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281046).length < 2 ^ (prefixWord ++ tailWord_3281046).sum := by decide
  have hdescent : baseEnd_3281046 < baseStart_3281046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281048 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 2, 5]
def baseStart_3281048 : Nat := 118140960795 + 3281048 * 2 ^ 59
def prefixEnd_3281048 : Nat := 4983230072969 + 3 ^ 40 * 3281048 * 2
def baseEnd_3281048 : Nat := 561584891491061372770247

theorem tailTrace_3281048 : CollatzResearch.WordTrace tailWord_3281048 prefixEnd_3281048 561584891491061372770247 := by
  unfold tailWord_3281048
  simp only [CollatzResearch.WordTrace]
  refine ⟨59834825908665464615549899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79779767878220619487399865 59834825908665464615549899)
  ·
    refine ⟨89752238862998196923324849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59834825908665464615549899 89752238862998196923324849)
    ·
      refine ⟨67314179147248647692493637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89752238862998196923324849 67314179147248647692493637)
      ·
        refine ⟨12621408590109121442342557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67314179147248647692493637 12621408590109121442342557)
        ·
          refine ⟨4733028221290920540878459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12621408590109121442342557 4733028221290920540878459)
          ·
            refine ⟨7099542331936380811317689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733028221290920540878459 7099542331936380811317689)
            ·
              refine ⟨5324656748952285608488267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7099542331936380811317689 5324656748952285608488267)
              ·
                refine ⟨7986985123428428412732401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324656748952285608488267 7986985123428428412732401)
                ·
                  refine ⟨5990238842571321309549301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7986985123428428412732401 5990238842571321309549301)
                  ·
                    refine ⟨561584891491061372770247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5990238842571321309549301 561584891491061372770247)
                    ·
                      rfl

theorem cell23_3281048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_3281048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281048 prefixEnd_3281048 := by exact prefixLift 3281048
  have htrace : WordTrace (prefixWord ++ tailWord_3281048) baseStart_3281048 baseEnd_3281048 := by
    simpa [prefixWord, tailWord_3281048, baseEnd_3281048] using wordTrace_append hprefix tailTrace_3281048
  have hstable : (prefixWord ++ tailWord_3281048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281048).length < 2 ^ (prefixWord ++ tailWord_3281048).sum := by decide
  have hdescent : baseEnd_3281048 < baseStart_3281048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281135 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 3]
def baseStart_3281135 : Nat := 118140960795 + 3281135 * 2 ^ 59
def prefixEnd_3281135 : Nat := 4983230072969 + 3 ^ 40 * 3281135 * 2
def baseEnd_3281135 : Nat := 1684799347290125277922841

theorem tailTrace_3281135 : CollatzResearch.WordTrace tailWord_3281135 prefixEnd_3281135 1684799347290125277922841 := by
  unfold tailWord_3281135
  simp only [CollatzResearch.WordTrace]
  refine ⟨119672824968015743089516859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79781883312010495393011239 119672824968015743089516859)
  ·
    refine ⟨179509237452023614634275289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119672824968015743089516859 179509237452023614634275289)
    ·
      refine ⟨134631928089017710975706467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179509237452023614634275289 134631928089017710975706467)
      ·
        refine ⟨201947892133526566463559701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134631928089017710975706467 201947892133526566463559701)
        ·
          refine ⟨9466307443759057802979361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201947892133526566463559701 9466307443759057802979361)
          ·
            refine ⟨7099730582819293352234521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9466307443759057802979361 7099730582819293352234521)
            ·
              refine ⟨5324797937114470014175891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7099730582819293352234521 5324797937114470014175891)
              ·
                refine ⟨7987196905671705021263837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324797937114470014175891 7987196905671705021263837)
                ·
                  refine ⟨2995198839626889382973939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7987196905671705021263837 2995198839626889382973939)
                  ·
                    refine ⟨4492798259440334074460909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2995198839626889382973939 4492798259440334074460909)
                    ·
                      refine ⟨1684799347290125277922841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4492798259440334074460909 1684799347290125277922841)
                      ·
                        rfl

theorem cell23_3281135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 3].length) (baseStart_3281135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281135 prefixEnd_3281135 := by exact prefixLift 3281135
  have htrace : WordTrace (prefixWord ++ tailWord_3281135) baseStart_3281135 baseEnd_3281135 := by
    simpa [prefixWord, tailWord_3281135, baseEnd_3281135] using wordTrace_append hprefix tailTrace_3281135
  have hstable : (prefixWord ++ tailWord_3281135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281135).length < 2 ^ (prefixWord ++ tailWord_3281135).sum := by decide
  have hdescent : baseEnd_3281135 < baseStart_3281135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281171 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4]
def baseStart_3281171 : Nat := 118140960795 + 3281171 * 2 ^ 59
def prefixEnd_3281171 : Nat := 4983230072969 + 3 ^ 40 * 3281171 * 2
def baseEnd_3281171 : Nat := 1684817832593687137072675

theorem tailTrace_3281171 : CollatzResearch.WordTrace tailWord_3281171 prefixEnd_3281171 1684817832593687137072675 := by
  unfold tailWord_3281171
  simp only [CollatzResearch.WordTrace]
  refine ⟨119674137995885321237827367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79782758663923547491884911 119674137995885321237827367)
  ·
    refine ⟨179511206993827981856741051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119674137995885321237827367 179511206993827981856741051)
    ·
      refine ⟨269266810490741972785111577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179511206993827981856741051 269266810490741972785111577)
      ·
        refine ⟨201950107868056479588833683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269266810490741972785111577 201950107868056479588833683)
        ·
          refine ⟨302925161802084719383250525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201950107868056479588833683 302925161802084719383250525)
          ·
            refine ⟨113596935675781769768718947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302925161802084719383250525 113596935675781769768718947)
            ·
              refine ⟨170395403513672654653078421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113596935675781769768718947 170395403513672654653078421)
              ·
                refine ⟨7987284539703405686863051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170395403513672654653078421 7987284539703405686863051)
                ·
                  refine ⟨11980926809555108530294577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7987284539703405686863051 11980926809555108530294577)
                  ·
                    refine ⟨8985695107166331397720933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11980926809555108530294577 8985695107166331397720933)
                    ·
                      refine ⟨1684817832593687137072675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8985695107166331397720933 1684817832593687137072675)
                      ·
                        rfl

theorem cell23_3281171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_3281171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281171 prefixEnd_3281171 := by exact prefixLift 3281171
  have htrace : WordTrace (prefixWord ++ tailWord_3281171) baseStart_3281171 baseEnd_3281171 := by
    simpa [prefixWord, tailWord_3281171, baseEnd_3281171] using wordTrace_append hprefix tailTrace_3281171
  have hstable : (prefixWord ++ tailWord_3281171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281171).length < 2 ^ (prefixWord ++ tailWord_3281171).sum := by decide
  have hdescent : baseEnd_3281171 < baseStart_3281171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281241 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 2, 6]
def baseStart_3281241 : Nat := 118140960795 + 3281241 * 2 ^ 59
def prefixEnd_3281241 : Nat := 4983230072969 + 3 ^ 40 * 3281241 * 2
def baseEnd_3281241 : Nat := 561617925413167287732451

theorem tailTrace_3281241 : CollatzResearch.WordTrace tailWord_3281241 prefixEnd_3281241 561617925413167287732451 := by
  unfold tailWord_3281241
  simp only [CollatzResearch.WordTrace]
  refine ⟨119676691105631723192875577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79784460737087815461917051 119676691105631723192875577)
  ·
    refine ⟨89757518329223792394656683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119676691105631723192875577 89757518329223792394656683)
    ·
      refine ⟨134636277493835688591985025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89757518329223792394656683 134636277493835688591985025)
      ·
        refine ⟨100977208120376766443988769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134636277493835688591985025 100977208120376766443988769)
        ·
          refine ⟨75732906090282574832991577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100977208120376766443988769 75732906090282574832991577)
          ·
            refine ⟨56799679567711931124743683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75732906090282574832991577 56799679567711931124743683)
            ·
              refine ⟨85199519351567896687115525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56799679567711931124743683 85199519351567896687115525)
              ·
                refine ⟨15974909878418980628834161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85199519351567896687115525 15974909878418980628834161)
                ·
                  refine ⟨11981182408814235471625621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15974909878418980628834161 11981182408814235471625621)
                  ·
                    refine ⟨561617925413167287732451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11981182408814235471625621 561617925413167287732451)
                    ·
                      rfl

theorem cell23_3281241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_3281241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281241 prefixEnd_3281241 := by exact prefixLift 3281241
  have htrace : WordTrace (prefixWord ++ tailWord_3281241) baseStart_3281241 baseEnd_3281241 := by
    simpa [prefixWord, tailWord_3281241, baseEnd_3281241] using wordTrace_append hprefix tailTrace_3281241
  have hstable : (prefixWord ++ tailWord_3281241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281241).length < 2 ^ (prefixWord ++ tailWord_3281241).sum := by decide
  have hdescent : baseEnd_3281241 < baseStart_3281241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281258 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3281258 : Nat := 118140960795 + 3281258 * 2 ^ 59
def prefixEnd_3281258 : Nat := 4983230072969 + 3 ^ 40 * 3281258 * 2
def baseEnd_3281258 : Nat := 561620835136876098894925

theorem tailTrace_3281258 : CollatzResearch.WordTrace tailWord_3281258 prefixEnd_3281258 561620835136876098894925 := by
  unfold tailWord_3281258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29919327786642533774061107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79784874097713423397496285 29919327786642533774061107)
  ·
    refine ⟨44878991679963800661091661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29919327786642533774061107 44878991679963800661091661)
    ·
      refine ⟨16829621879986425247909373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44878991679963800661091661 16829621879986425247909373)
      ·
        refine ⟨6311108204994909467966015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16829621879986425247909373 6311108204994909467966015)
        ·
          refine ⟨9466662307492364201949023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311108204994909467966015 9466662307492364201949023)
          ·
            refine ⟨14199993461238546302923535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9466662307492364201949023 14199993461238546302923535)
            ·
              refine ⟨21299990191857819454385303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14199993461238546302923535 21299990191857819454385303)
              ·
                refine ⟨31949985287786729181577955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21299990191857819454385303 31949985287786729181577955)
                ·
                  refine ⟨47924977931680093772366933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31949985287786729181577955 47924977931680093772366933)
                  ·
                    refine ⟨561620835136876098894925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47924977931680093772366933 561620835136876098894925)
                    ·
                      rfl

theorem cell23_3281258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3281258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281258 prefixEnd_3281258 := by exact prefixLift 3281258
  have htrace : WordTrace (prefixWord ++ tailWord_3281258) baseStart_3281258 baseEnd_3281258 := by
    simpa [prefixWord, tailWord_3281258, baseEnd_3281258] using wordTrace_append hprefix tailTrace_3281258
  have hstable : (prefixWord ++ tailWord_3281258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281258).length < 2 ^ (prefixWord ++ tailWord_3281258).sum := by decide
  have hdescent : baseEnd_3281258 < baseStart_3281258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281265 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 6, 2, 2]
def baseStart_3281265 : Nat := 118140960795 + 3281265 * 2 ^ 59
def prefixEnd_3281265 : Nat := 4983230072969 + 3 ^ 40 * 3281265 * 2
def baseEnd_3281265 : Nat := 1684866099775209769297243

theorem tailTrace_3281265 : CollatzResearch.WordTrace tailWord_3281265 prefixEnd_3281265 1684866099775209769297243 := by
  unfold tailWord_3281265
  simp only [CollatzResearch.WordTrace]
  refine ⟨119677566457544775291749249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79785044305029850194499499 119677566457544775291749249)
  ·
    refine ⟨89758174843158581468811937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119677566457544775291749249 89758174843158581468811937)
    ·
      refine ⟨67318631132368936101608953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89758174843158581468811937 67318631132368936101608953)
      ·
        refine ⟨50488973349276702076206715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67318631132368936101608953 50488973349276702076206715)
        ·
          refine ⟨75733460023915053114310073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50488973349276702076206715 75733460023915053114310073)
          ·
            refine ⟨56800095017936289835732555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75733460023915053114310073 56800095017936289835732555)
            ·
              refine ⟨85200142526904434753598833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56800095017936289835732555 85200142526904434753598833)
              ·
                refine ⟨63900106895178326065199125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85200142526904434753598833 63900106895178326065199125)
                ·
                  refine ⟨2995317510711484034306209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63900106895178326065199125 2995317510711484034306209)
                  ·
                    refine ⟨2246488133033613025729657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2995317510711484034306209 2246488133033613025729657)
                    ·
                      refine ⟨1684866099775209769297243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246488133033613025729657 1684866099775209769297243)
                      ·
                        rfl

theorem cell23_3281265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_3281265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281265 prefixEnd_3281265 := by exact prefixLift 3281265
  have htrace : WordTrace (prefixWord ++ tailWord_3281265) baseStart_3281265 baseEnd_3281265 := by
    simpa [prefixWord, tailWord_3281265, baseEnd_3281265] using wordTrace_append hprefix tailTrace_3281265
  have hstable : (prefixWord ++ tailWord_3281265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281265).length < 2 ^ (prefixWord ++ tailWord_3281265).sum := by decide
  have hdescent : baseEnd_3281265 < baseStart_3281265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281338 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_3281338 : Nat := 118140960795 + 3281338 * 2 ^ 59
def prefixEnd_3281338 : Nat := 4983230072969 + 3 ^ 40 * 3281338 * 2
def baseEnd_3281338 : Nat := 1684903583862987983684407

theorem tailTrace_3281338 : CollatzResearch.WordTrace tailWord_3281338 prefixEnd_3281338 1684903583862987983684407 := by
  unfold tailWord_3281338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29920057246570077189789167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79786819324186872506104445 29920057246570077189789167)
  ·
    refine ⟨44880085869855115784683751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29920057246570077189789167 44880085869855115784683751)
    ·
      refine ⟨67320128804782673677025627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44880085869855115784683751 67320128804782673677025627)
      ·
        refine ⟨100980193207174010515538441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67320128804782673677025627 100980193207174010515538441)
        ·
          refine ⟨75735144905380507886653831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100980193207174010515538441 75735144905380507886653831)
          ·
            refine ⟨113602717358070761829980747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75735144905380507886653831 113602717358070761829980747)
            ·
              refine ⟨170404076037106142744971121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113602717358070761829980747 170404076037106142744971121)
              ·
                refine ⟨127803057027829607058728341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170404076037106142744971121 127803057027829607058728341)
                ·
                  refine ⟨5990768298179512830877891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127803057027829607058728341 5990768298179512830877891)
                  ·
                    refine ⟨8986152447269269246316837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5990768298179512830877891 8986152447269269246316837)
                    ·
                      refine ⟨1684903583862987983684407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8986152447269269246316837 1684903583862987983684407)
                      ·
                        rfl

theorem cell23_3281338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_3281338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281338 prefixEnd_3281338 := by exact prefixLift 3281338
  have htrace : WordTrace (prefixWord ++ tailWord_3281338) baseStart_3281338 baseEnd_3281338 := by
    simpa [prefixWord, tailWord_3281338, baseEnd_3281338] using wordTrace_append hprefix tailTrace_3281338
  have hstable : (prefixWord ++ tailWord_3281338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281338).length < 2 ^ (prefixWord ++ tailWord_3281338).sum := by decide
  have hdescent : baseEnd_3281338 < baseStart_3281338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281362 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3281362 : Nat := 118140960795 + 3281362 * 2 ^ 59
def prefixEnd_3281362 : Nat := 4983230072969 + 3 ^ 40 * 3281362 * 2
def baseEnd_3281362 : Nat := 1684915907398695889784297

theorem tailTrace_3281362 : CollatzResearch.WordTrace tailWord_3281362 prefixEnd_3281362 1684915907398695889784297 := by
  unfold tailWord_3281362
  simp only [CollatzResearch.WordTrace]
  refine ⟨29920276084548340214507585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79787402892128907238686893 29920276084548340214507585)
  ·
    refine ⟨22440207063411255160880689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29920276084548340214507585 22440207063411255160880689)
    ·
      refine ⟨16830155297558441370660517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22440207063411255160880689 16830155297558441370660517)
      ·
        refine ⟨3155654118292207756998847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16830155297558441370660517 3155654118292207756998847)
        ·
          refine ⟨4733481177438311635498271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155654118292207756998847 4733481177438311635498271)
          ·
            refine ⟨7100221766157467453247407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733481177438311635498271 7100221766157467453247407)
            ·
              refine ⟨10650332649236201179871111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100221766157467453247407 10650332649236201179871111)
              ·
                refine ⟨15975498973854301769806667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10650332649236201179871111 15975498973854301769806667)
                ·
                  refine ⟨23963248460781452654710001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15975498973854301769806667 23963248460781452654710001)
                  ·
                    refine ⟨17972436345586089491032501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23963248460781452654710001 17972436345586089491032501)
                    ·
                      refine ⟨1684915907398695889784297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17972436345586089491032501 1684915907398695889784297)
                      ·
                        rfl

theorem cell23_3281362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3281362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281362 prefixEnd_3281362 := by exact prefixLift 3281362
  have htrace : WordTrace (prefixWord ++ tailWord_3281362) baseStart_3281362 baseEnd_3281362 := by
    simpa [prefixWord, tailWord_3281362, baseEnd_3281362] using wordTrace_append hprefix tailTrace_3281362
  have hstable : (prefixWord ++ tailWord_3281362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281362).length < 2 ^ (prefixWord ++ tailWord_3281362).sum := by decide
  have hdescent : baseEnd_3281362 < baseStart_3281362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281412 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 6]
def baseStart_3281412 : Nat := 118140960795 + 3281412 * 2 ^ 59
def prefixEnd_3281412 : Nat := 4983230072969 + 3 ^ 40 * 3281412 * 2
def baseEnd_3281412 : Nat := 187215731270157854906563

theorem tailTrace_3281412 : CollatzResearch.WordTrace tailWord_3281412 prefixEnd_3281412 187215731270157854906563 := by
  unfold tailWord_3281412
  simp only [CollatzResearch.WordTrace]
  refine ⟨59841463994006109698675245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79788618658674812931566993 59841463994006109698675245)
  ·
    refine ⟨22440548997752291137003217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59841463994006109698675245 22440548997752291137003217)
    ·
      refine ⟨16830411748314218352752413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22440548997752291137003217 16830411748314218352752413)
      ·
        refine ⟨6311404405617831882282155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16830411748314218352752413 6311404405617831882282155)
        ·
          refine ⟨9467106608426747823423233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311404405617831882282155 9467106608426747823423233)
          ·
            refine ⟨7100329956320060867567425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9467106608426747823423233 7100329956320060867567425)
            ·
              refine ⟨5325247467240045650675569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7100329956320060867567425 5325247467240045650675569)
              ·
                refine ⟨3993935600430034238006677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5325247467240045650675569 3993935600430034238006677)
                ·
                  refine ⟨187215731270157854906563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3993935600430034238006677 187215731270157854906563)
                  ·
                    rfl

theorem cell23_3281412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_3281412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281412 prefixEnd_3281412 := by exact prefixLift 3281412
  have htrace : WordTrace (prefixWord ++ tailWord_3281412) baseStart_3281412 baseEnd_3281412 := by
    simpa [prefixWord, tailWord_3281412, baseEnd_3281412] using wordTrace_append hprefix tailTrace_3281412
  have hstable : (prefixWord ++ tailWord_3281412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281412).length < 2 ^ (prefixWord ++ tailWord_3281412).sum := by decide
  have hdescent : baseEnd_3281412 < baseStart_3281412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281445 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_3281445 : Nat := 118140960795 + 3281445 * 2 ^ 59
def prefixEnd_3281445 : Nat := 4983230072969 + 3 ^ 40 * 3281445 * 2
def baseEnd_3281445 : Nat := 1684958526293019065046415

theorem tailTrace_3281445 : CollatzResearch.WordTrace tailWord_3281445 prefixEnd_3281445 1684958526293019065046415 := by
  unfold tailWord_3281445
  simp only [CollatzResearch.WordTrace]
  refine ⟨119684131596892666033301789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79789421064595110688867859 119684131596892666033301789)
  ·
    refine ⟨44881549348834749762488171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119684131596892666033301789 44881549348834749762488171)
    ·
      refine ⟨67322324023252124643732257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44881549348834749762488171 67322324023252124643732257)
      ·
        refine ⟨50491743017439093482799193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67322324023252124643732257 50491743017439093482799193)
        ·
          refine ⟨37868807263079320112099395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50491743017439093482799193 37868807263079320112099395)
          ·
            refine ⟨56803210894618980168149093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37868807263079320112099395 56803210894618980168149093)
            ·
              refine ⟨10650602042741058781527955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56803210894618980168149093 10650602042741058781527955)
              ·
                refine ⟨15975903064111588172291933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10650602042741058781527955 15975903064111588172291933)
                ·
                  refine ⟨5990963649041845564609475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15975903064111588172291933 5990963649041845564609475)
                  ·
                    refine ⟨8986445473562768346914213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5990963649041845564609475 8986445473562768346914213)
                    ·
                      refine ⟨1684958526293019065046415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8986445473562768346914213 1684958526293019065046415)
                      ·
                        rfl

theorem cell23_3281445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_3281445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281445 prefixEnd_3281445 := by exact prefixLift 3281445
  have htrace : WordTrace (prefixWord ++ tailWord_3281445) baseStart_3281445 baseEnd_3281445 := by
    simpa [prefixWord, tailWord_3281445, baseEnd_3281445] using wordTrace_append hprefix tailTrace_3281445
  have hstable : (prefixWord ++ tailWord_3281445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281445).length < 2 ^ (prefixWord ++ tailWord_3281445).sum := by decide
  have hdescent : baseEnd_3281445 < baseStart_3281445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281465 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3281465 : Nat := 118140960795 + 3281465 * 2 ^ 59
def prefixEnd_3281465 : Nat := 4983230072969 + 3 ^ 40 * 3281465 * 2
def baseEnd_3281465 : Nat := 1684968795906108986796323

theorem tailTrace_3281465 : CollatzResearch.WordTrace tailWord_3281465 prefixEnd_3281465 1684968795906108986796323 := by
  unfold tailWord_3281465
  simp only [CollatzResearch.WordTrace]
  refine ⟨119684861056820209449029849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79789907371213472966019899 119684861056820209449029849)
  ·
    refine ⟨89763645792615157086772387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119684861056820209449029849 89763645792615157086772387)
    ·
      refine ⟨134645468688922735630158581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89763645792615157086772387 134645468688922735630158581)
      ·
        refine ⟨12623012689586506465327367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134645468688922735630158581 12623012689586506465327367)
        ·
          refine ⟨18934519034379759697991051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12623012689586506465327367 18934519034379759697991051)
          ·
            refine ⟨28401778551569639546986577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18934519034379759697991051 28401778551569639546986577)
            ·
              refine ⟨21301333913677229660239933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28401778551569639546986577 21301333913677229660239933)
              ·
                refine ⟨7988000217628961122589975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21301333913677229660239933 7988000217628961122589975)
                ·
                  refine ⟨11982000326443441683884963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7988000217628961122589975 11982000326443441683884963)
                  ·
                    refine ⟨17973000489665162525827445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11982000326443441683884963 17973000489665162525827445)
                    ·
                      refine ⟨1684968795906108986796323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17973000489665162525827445 1684968795906108986796323)
                      ·
                        rfl

theorem cell23_3281465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3281465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281465 prefixEnd_3281465 := by exact prefixLift 3281465
  have htrace : WordTrace (prefixWord ++ tailWord_3281465) baseStart_3281465 baseEnd_3281465 := by
    simpa [prefixWord, tailWord_3281465, baseEnd_3281465] using wordTrace_append hprefix tailTrace_3281465
  have hstable : (prefixWord ++ tailWord_3281465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281465).length < 2 ^ (prefixWord ++ tailWord_3281465).sum := by decide
  have hdescent : baseEnd_3281465 < baseStart_3281465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281472 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 2, 4]
def baseStart_3281472 : Nat := 118140960795 + 3281472 * 2 ^ 59
def prefixEnd_3281472 : Nat := 4983230072969 + 3 ^ 40 * 3281472 * 2
def baseEnd_3281472 : Nat := 561657463423563486469597

theorem tailTrace_3281472 : CollatzResearch.WordTrace tailWord_3281472 prefixEnd_3281472 561657463423563486469597 := by
  unfold tailWord_3281472
  simp only [CollatzResearch.WordTrace]
  refine ⟨59842558183897424822267335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79790077578529899763023113 59842558183897424822267335)
  ·
    refine ⟨89763837275846137233401003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59842558183897424822267335 89763837275846137233401003)
    ·
      refine ⟨134645755913769205850101505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89763837275846137233401003 134645755913769205850101505)
      ·
        refine ⟨100984316935326904387576129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134645755913769205850101505 100984316935326904387576129)
        ·
          refine ⟨75738237701495178290682097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100984316935326904387576129 75738237701495178290682097)
          ·
            refine ⟨56803678276121383718011573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75738237701495178290682097 56803678276121383718011573)
            ·
              refine ⟨5325344838386379723563585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56803678276121383718011573 5325344838386379723563585)
              ·
                refine ⟨3994008628789784792672689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5325344838386379723563585 3994008628789784792672689)
                ·
                  refine ⟨2995506471592338594504517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994008628789784792672689 2995506471592338594504517)
                  ·
                    refine ⟨561657463423563486469597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2995506471592338594504517 561657463423563486469597)
                    ·
                      rfl

theorem cell23_3281472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_3281472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281472 prefixEnd_3281472 := by exact prefixLift 3281472
  have htrace : WordTrace (prefixWord ++ tailWord_3281472) baseStart_3281472 baseEnd_3281472 := by
    simpa [prefixWord, tailWord_3281472, baseEnd_3281472] using wordTrace_append hprefix tailTrace_3281472
  have hstable : (prefixWord ++ tailWord_3281472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281472).length < 2 ^ (prefixWord ++ tailWord_3281472).sum := by decide
  have hdescent : baseEnd_3281472 < baseStart_3281472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281479 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_3281479 : Nat := 118140960795 + 3281479 * 2 ^ 59
def prefixEnd_3281479 : Nat := 4983230072969 + 3 ^ 40 * 3281479 * 2
def baseEnd_3281479 : Nat := 1684975984635271932021259

theorem tailTrace_3281479 : CollatzResearch.WordTrace tailWord_3281479 prefixEnd_3281479 1684975984635271932021259 := by
  unfold tailWord_3281479
  simp only [CollatzResearch.WordTrace]
  refine ⟨119685371678769489840039491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79790247785846326560026327 119685371678769489840039491)
  ·
    refine ⟨179528057518154234760059237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119685371678769489840039491 179528057518154234760059237)
    ·
      refine ⟨33661510784653919017511107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179528057518154234760059237 33661510784653919017511107)
      ·
        refine ⟨50492266176980878526266661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33661510784653919017511107 50492266176980878526266661)
        ·
          refine ⟨9467299908183914723674999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50492266176980878526266661 9467299908183914723674999)
          ·
            refine ⟨14200949862275872085512499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467299908183914723674999 14200949862275872085512499)
            ·
              refine ⟨21301424793413808128268749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14200949862275872085512499 21301424793413808128268749)
              ·
                refine ⟨7988034297530178048100781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21301424793413808128268749 7988034297530178048100781)
                ·
                  refine ⟨2995512861573816768037793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7988034297530178048100781 2995512861573816768037793)
                  ·
                    refine ⟨2246634646180362576028345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2995512861573816768037793 2246634646180362576028345)
                    ·
                      refine ⟨1684975984635271932021259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246634646180362576028345 1684975984635271932021259)
                      ·
                        rfl

theorem cell23_3281479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_3281479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281479 prefixEnd_3281479 := by exact prefixLift 3281479
  have htrace : WordTrace (prefixWord ++ tailWord_3281479) baseStart_3281479 baseEnd_3281479 := by
    simpa [prefixWord, tailWord_3281479, baseEnd_3281479] using wordTrace_append hprefix tailTrace_3281479
  have hstable : (prefixWord ++ tailWord_3281479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281479).length < 2 ^ (prefixWord ++ tailWord_3281479).sum := by decide
  have hdescent : baseEnd_3281479 < baseStart_3281479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281488 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_3281488 : Nat := 118140960795 + 3281488 * 2 ^ 59
def prefixEnd_3281488 : Nat := 4983230072969 + 3 ^ 40 * 3281488 * 2
def baseEnd_3281488 : Nat := 1684980605961162396808717

theorem tailTrace_3281488 : CollatzResearch.WordTrace tailWord_3281488 prefixEnd_3281488 1684980605961162396808717 := by
  unfold tailWord_3281488
  simp only [CollatzResearch.WordTrace]
  refine ⟨59842849967868442188558559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79790466623824589584744745 59842849967868442188558559)
  ·
    refine ⟨89764274951802663282837839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59842849967868442188558559 89764274951802663282837839)
    ·
      refine ⟨134646412427703994924256759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89764274951802663282837839 134646412427703994924256759)
      ·
        refine ⟨201969618641555992386385139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134646412427703994924256759 201969618641555992386385139)
        ·
          refine ⟨302954427962333988579577709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201969618641555992386385139 302954427962333988579577709)
          ·
            refine ⟨113607910485875245717341641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302954427962333988579577709 113607910485875245717341641)
            ·
              refine ⟨85205932864406434288006231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113607910485875245717341641 85205932864406434288006231)
              ·
                refine ⟨127808899296609651432009347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85205932864406434288006231 127808899296609651432009347)
                ·
                  refine ⟨191713348944914477148014021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127808899296609651432009347 191713348944914477148014021)
                  ·
                    refine ⟨35946252927171464465252629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191713348944914477148014021 35946252927171464465252629)
                    ·
                      refine ⟨1684980605961162396808717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35946252927171464465252629 1684980605961162396808717)
                      ·
                        rfl

theorem cell23_3281488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_3281488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281488 prefixEnd_3281488 := by exact prefixLift 3281488
  have htrace : WordTrace (prefixWord ++ tailWord_3281488) baseStart_3281488 baseEnd_3281488 := by
    simpa [prefixWord, tailWord_3281488, baseEnd_3281488] using wordTrace_append hprefix tailTrace_3281488
  have hstable : (prefixWord ++ tailWord_3281488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281488).length < 2 ^ (prefixWord ++ tailWord_3281488).sum := by decide
  have hdescent : baseEnd_3281488 < baseStart_3281488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281489 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 2, 4]
def baseStart_3281489 : Nat := 118140960795 + 3281489 * 2 ^ 59
def prefixEnd_3281489 : Nat := 4983230072969 + 3 ^ 40 * 3281489 * 2
def baseEnd_3281489 : Nat := 561660373147272297632071

theorem tailTrace_3281489 : CollatzResearch.WordTrace tailWord_3281489 prefixEnd_3281489 561660373147272297632071 := by
  unfold tailWord_3281489
  simp only [CollatzResearch.WordTrace]
  refine ⟨119685736408733261547903521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79790490939155507698602347 119685736408733261547903521)
  ·
    refine ⟨89764302306549946160927641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119685736408733261547903521 89764302306549946160927641)
    ·
      refine ⟨67323226729912459620695731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89764302306549946160927641 67323226729912459620695731)
      ·
        refine ⟨100984840094868689431043597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67323226729912459620695731 100984840094868689431043597)
        ·
          refine ⟨37869315035575758536641349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100984840094868689431043597 37869315035575758536641349)
          ·
            refine ⟨7100496569170454725620253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37869315035575758536641349 7100496569170454725620253)
            ·
              refine ⟨2662686213438920522107595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7100496569170454725620253 2662686213438920522107595)
              ·
                refine ⟨3994029320158380783161393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662686213438920522107595 3994029320158380783161393)
                ·
                  refine ⟨2995521990118785587371045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994029320158380783161393 2995521990118785587371045)
                  ·
                    refine ⟨561660373147272297632071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2995521990118785587371045 561660373147272297632071)
                    ·
                      rfl

theorem cell23_3281489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_3281489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281489 prefixEnd_3281489 := by exact prefixLift 3281489
  have htrace : WordTrace (prefixWord ++ tailWord_3281489) baseStart_3281489 baseEnd_3281489 := by
    simpa [prefixWord, tailWord_3281489, baseEnd_3281489] using wordTrace_append hprefix tailTrace_3281489
  have hstable : (prefixWord ++ tailWord_3281489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281489).length < 2 ^ (prefixWord ++ tailWord_3281489).sum := by decide
  have hdescent : baseEnd_3281489 < baseStart_3281489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281492 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_3281492 : Nat := 118140960795 + 3281492 * 2 ^ 59
def prefixEnd_3281492 : Nat := 4983230072969 + 3 ^ 40 * 3281492 * 2
def baseEnd_3281492 : Nat := 1684982659883780381158699

theorem tailTrace_3281492 : CollatzResearch.WordTrace tailWord_3281492 prefixEnd_3281492 1684982659883780381158699 := by
  unfold tailWord_3281492
  simp only [CollatzResearch.WordTrace]
  refine ⟨59842922913861196530131365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79790563885148262040175153 59842922913861196530131365)
  ·
    refine ⟨11220548046348974349399631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59842922913861196530131365 11220548046348974349399631)
    ·
      refine ⟨16830822069523461524099447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11220548046348974349399631 16830822069523461524099447)
      ·
        refine ⟨25246233104285192286149171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16830822069523461524099447 25246233104285192286149171)
        ·
          refine ⟨37869349656427788429223757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25246233104285192286149171 37869349656427788429223757)
          ·
            refine ⟨14201006121160420660958909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37869349656427788429223757 14201006121160420660958909)
            ·
              refine ⟨5325377295435157747859591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14201006121160420660958909 5325377295435157747859591)
              ·
                refine ⟨7988065943152736621789387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5325377295435157747859591 7988065943152736621789387)
                ·
                  refine ⟨11982098914729104932684081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7988065943152736621789387 11982098914729104932684081)
                  ·
                    refine ⟨8986574186046828699513061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11982098914729104932684081 8986574186046828699513061)
                    ·
                      refine ⟨1684982659883780381158699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8986574186046828699513061 1684982659883780381158699)
                      ·
                        rfl

theorem cell23_3281492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_3281492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281492 prefixEnd_3281492 := by exact prefixLift 3281492
  have htrace : WordTrace (prefixWord ++ tailWord_3281492) baseStart_3281492 baseEnd_3281492 := by
    simpa [prefixWord, tailWord_3281492, baseEnd_3281492] using wordTrace_append hprefix tailTrace_3281492
  have hstable : (prefixWord ++ tailWord_3281492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281492).length < 2 ^ (prefixWord ++ tailWord_3281492).sum := by decide
  have hdescent : baseEnd_3281492 < baseStart_3281492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281546 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3281546 : Nat := 118140960795 + 3281546 * 2 ^ 59
def prefixEnd_3281546 : Nat := 4983230072969 + 3 ^ 40 * 3281546 * 2
def baseEnd_3281546 : Nat := 1685010387839123169883451

theorem tailTrace_3281546 : CollatzResearch.WordTrace tailWord_3281546 prefixEnd_3281546 1685010387839123169883451 := by
  unfold tailWord_3281546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29921953842381690070682123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79791876913017840188485661 29921953842381690070682123)
  ·
    refine ⟨44882930763572535106023185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29921953842381690070682123 44882930763572535106023185)
    ·
      refine ⟨33662198072679401329517389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44882930763572535106023185 33662198072679401329517389)
      ·
        refine ⟨12623324277254775498569021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33662198072679401329517389 12623324277254775498569021)
        ·
          refine ⟨4733746603970540811963383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12623324277254775498569021 4733746603970540811963383)
          ·
            refine ⟨7100619905955811217945075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733746603970540811963383 7100619905955811217945075)
            ·
              refine ⟨10650929858933716826917613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100619905955811217945075 10650929858933716826917613)
              ·
                refine ⟨3994098697100143810094105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10650929858933716826917613 3994098697100143810094105)
                ·
                  refine ⟨2995574022825107857570579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994098697100143810094105 2995574022825107857570579)
                  ·
                    refine ⟨4493361034237661786355869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2995574022825107857570579 4493361034237661786355869)
                    ·
                      refine ⟨1685010387839123169883451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4493361034237661786355869 1685010387839123169883451)
                      ·
                        rfl

theorem cell23_3281546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3281546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281546 prefixEnd_3281546 := by exact prefixLift 3281546
  have htrace : WordTrace (prefixWord ++ tailWord_3281546) baseStart_3281546 baseEnd_3281546 := by
    simpa [prefixWord, tailWord_3281546, baseEnd_3281546] using wordTrace_append hprefix tailTrace_3281546
  have hstable : (prefixWord ++ tailWord_3281546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281546).length < 2 ^ (prefixWord ++ tailWord_3281546).sum := by decide
  have hdescent : baseEnd_3281546 < baseStart_3281546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281555 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 3]
def baseStart_3281555 : Nat := 118140960795 + 3281555 * 2 ^ 59
def prefixEnd_3281555 : Nat := 4983230072969 + 3 ^ 40 * 3281555 * 2
def baseEnd_3281555 : Nat := 1685015009165013634670909

theorem tailTrace_3281555 : CollatzResearch.WordTrace tailWord_3281555 prefixEnd_3281555 1685015009165013634670909 := by
  unfold tailWord_3281555
  simp only [CollatzResearch.WordTrace]
  refine ⟨119688143626494154819806119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79792095750996103213204079 119688143626494154819806119)
  ·
    refine ⟨179532215439741232229709179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119688143626494154819806119 179532215439741232229709179)
    ·
      refine ⟨269298323159611848344563769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179532215439741232229709179 269298323159611848344563769)
      ·
        refine ⟨201973742369708886258422827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269298323159611848344563769 201973742369708886258422827)
        ·
          refine ⟨302960613554563329387634241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201973742369708886258422827 302960613554563329387634241)
          ·
            refine ⟨227220460165922497040725681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302960613554563329387634241 227220460165922497040725681)
            ·
              refine ⟨170415345124441872780544261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227220460165922497040725681 170415345124441872780544261)
              ·
                refine ⟨31952877210832851146352049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170415345124441872780544261 31952877210832851146352049)
                ·
                  refine ⟨23964657908124638359764037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31952877210832851146352049 23964657908124638359764037)
                  ·
                    refine ⟨4493373357773369692455757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23964657908124638359764037 4493373357773369692455757)
                    ·
                      refine ⟨1685015009165013634670909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4493373357773369692455757 1685015009165013634670909)
                      ·
                        rfl

theorem cell23_3281555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_3281555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281555 prefixEnd_3281555 := by exact prefixLift 3281555
  have htrace : WordTrace (prefixWord ++ tailWord_3281555) baseStart_3281555 baseEnd_3281555 := by
    simpa [prefixWord, tailWord_3281555, baseEnd_3281555] using wordTrace_append hprefix tailTrace_3281555
  have hstable : (prefixWord ++ tailWord_3281555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281555).length < 2 ^ (prefixWord ++ tailWord_3281555).sum := by decide
  have hdescent : baseEnd_3281555 < baseStart_3281555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281556 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3281556 : Nat := 118140960795 + 3281556 * 2 ^ 59
def prefixEnd_3281556 : Nat := 4983230072969 + 3 ^ 40 * 3281556 * 2
def baseEnd_3281556 : Nat := 1685015522645668130758405

theorem tailTrace_3281556 : CollatzResearch.WordTrace tailWord_3281556 prefixEnd_3281556 1685015522645668130758405 := by
  unfold tailWord_3281556
  simp only [CollatzResearch.WordTrace]
  refine ⟨59844090049745265995296261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79792120066327021327061681 59844090049745265995296261)
  ·
    refine ⟨11220766884327237374118049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59844090049745265995296261 11220766884327237374118049)
    ·
      refine ⟨8415575163245428030588537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11220766884327237374118049 8415575163245428030588537)
      ·
        refine ⟨6311681372434071022941403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8415575163245428030588537 6311681372434071022941403)
        ·
          refine ⟨9467522058651106534412105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311681372434071022941403 9467522058651106534412105)
          ·
            refine ⟨7100641543988329900809079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9467522058651106534412105 7100641543988329900809079)
            ·
              refine ⟨10650962315982494851213619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100641543988329900809079 10650962315982494851213619)
              ·
                refine ⟨15976443473973742276820429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10650962315982494851213619 15976443473973742276820429)
                ·
                  refine ⟨5991166302740153353807661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15976443473973742276820429 5991166302740153353807661)
                  ·
                    refine ⟨2246687363527557507677873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5991166302740153353807661 2246687363527557507677873)
                    ·
                      refine ⟨1685015522645668130758405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246687363527557507677873 1685015522645668130758405)
                      ·
                        rfl

theorem cell23_3281556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3281556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281556 prefixEnd_3281556 := by exact prefixLift 3281556
  have htrace : WordTrace (prefixWord ++ tailWord_3281556) baseStart_3281556 baseEnd_3281556 := by
    simpa [prefixWord, tailWord_3281556, baseEnd_3281556] using wordTrace_append hprefix tailTrace_3281556
  have hstable : (prefixWord ++ tailWord_3281556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281556).length < 2 ^ (prefixWord ++ tailWord_3281556).sum := by decide
  have hdescent : baseEnd_3281556 < baseStart_3281556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281642 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3281642 : Nat := 118140960795 + 3281642 * 2 ^ 59
def prefixEnd_3281642 : Nat := 4983230072969 + 3 ^ 40 * 3281642 * 2
def baseEnd_3281642 : Nat := 1685059681981954794283009

theorem tailTrace_3281642 : CollatzResearch.WordTrace tailWord_3281642 prefixEnd_3281642 1685059681981954794283009 := by
  unfold tailWord_3281642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29922829194294742169555795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79794211184785979118815453 29922829194294742169555795)
  ·
    refine ⟨44884243791442113254333693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29922829194294742169555795 44884243791442113254333693)
    ·
      refine ⟨16831591421790792470375135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44884243791442113254333693 16831591421790792470375135)
      ·
        refine ⟨25247387132686188705562703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831591421790792470375135 25247387132686188705562703)
        ·
          refine ⟨37871080699029283058344055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25247387132686188705562703 37871080699029283058344055)
          ·
            refine ⟨56806621048543924587516083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37871080699029283058344055 56806621048543924587516083)
            ·
              refine ⟨85209931572815886881274125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56806621048543924587516083 85209931572815886881274125)
              ·
                refine ⟨31953724339805957580477797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85209931572815886881274125 31953724339805957580477797)
                ·
                  refine ⟨5991323313713617046339587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31953724339805957580477797 5991323313713617046339587)
                  ·
                    refine ⟨8986984970570425569509381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5991323313713617046339587 8986984970570425569509381)
                    ·
                      refine ⟨1685059681981954794283009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8986984970570425569509381 1685059681981954794283009)
                      ·
                        rfl

theorem cell23_3281642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3281642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281642 prefixEnd_3281642 := by exact prefixLift 3281642
  have htrace : WordTrace (prefixWord ++ tailWord_3281642) baseStart_3281642 baseEnd_3281642 := by
    simpa [prefixWord, tailWord_3281642, baseEnd_3281642] using wordTrace_append hprefix tailTrace_3281642
  have hstable : (prefixWord ++ tailWord_3281642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281642).length < 2 ^ (prefixWord ++ tailWord_3281642).sum := by decide
  have hdescent : baseEnd_3281642 < baseStart_3281642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281655 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_3281655 : Nat := 118140960795 + 3281655 * 2 ^ 59
def prefixEnd_3281655 : Nat := 4983230072969 + 3 ^ 40 * 3281655 * 2
def baseEnd_3281655 : Nat := 1685066357230463243420449

theorem tailTrace_3281655 : CollatzResearch.WordTrace tailWord_3281655 prefixEnd_3281655 1685066357230463243420449 := by
  unfold tailWord_3281655
  simp only [CollatzResearch.WordTrace]
  refine ⟨119691790926131871898446419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79794527284087914598964279 119691790926131871898446419)
  ·
    refine ⟨179537686389197807847669629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119691790926131871898446419 179537686389197807847669629)
    ·
      refine ⟨67326632395949177942876111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179537686389197807847669629 67326632395949177942876111)
      ·
        refine ⟨100989948593923766914314167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67326632395949177942876111 100989948593923766914314167)
        ·
          refine ⟨151484922890885650371471251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100989948593923766914314167 151484922890885650371471251)
          ·
            refine ⟨227227384336328475557206877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151484922890885650371471251 227227384336328475557206877)
            ·
              refine ⟨85210269126123178333952579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227227384336328475557206877 85210269126123178333952579)
              ·
                refine ⟨127815403689184767500928869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85210269126123178333952579 127815403689184767500928869)
                ·
                  refine ⟨23965388191722143906424163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127815403689184767500928869 23965388191722143906424163)
                  ·
                    refine ⟨35948082287583215859636245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23965388191722143906424163 35948082287583215859636245)
                    ·
                      refine ⟨1685066357230463243420449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35948082287583215859636245 1685066357230463243420449)
                      ·
                        rfl

theorem cell23_3281655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_3281655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281655 prefixEnd_3281655 := by exact prefixLift 3281655
  have htrace : WordTrace (prefixWord ++ tailWord_3281655) baseStart_3281655 baseEnd_3281655 := by
    simpa [prefixWord, tailWord_3281655, baseEnd_3281655] using wordTrace_append hprefix tailTrace_3281655
  have hstable : (prefixWord ++ tailWord_3281655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281655).length < 2 ^ (prefixWord ++ tailWord_3281655).sum := by decide
  have hdescent : baseEnd_3281655 < baseStart_3281655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281716 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3281716 : Nat := 118140960795 + 3281716 * 2 ^ 59
def prefixEnd_3281716 : Nat := 4983230072969 + 3 ^ 40 * 3281716 * 2
def baseEnd_3281716 : Nat := 187233075505598611639741

theorem tailTrace_3281716 : CollatzResearch.WordTrace tailWord_3281716 prefixEnd_3281716 187233075505598611639741 := by
  unfold tailWord_3281716
  simp only [CollatzResearch.WordTrace]
  refine ⟨59847007889455439658208501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79796010519273919544278001 59847007889455439658208501)
  ·
    refine ⟨5610656989636447467957047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59847007889455439658208501 5610656989636447467957047)
    ·
      refine ⟨8415985484454671201935571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5610656989636447467957047 8415985484454671201935571)
      ·
        refine ⟨12623978226682006802903357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415985484454671201935571 12623978226682006802903357)
        ·
          refine ⟨4733991835005752551088759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12623978226682006802903357 4733991835005752551088759)
          ·
            refine ⟨7100987752508628826633139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733991835005752551088759 7100987752508628826633139)
            ·
              refine ⟨10651481628762943239949709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100987752508628826633139 10651481628762943239949709)
              ·
                refine ⟨3994305610786103714981141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10651481628762943239949709 3994305610786103714981141)
                ·
                  refine ⟨187233075505598611639741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3994305610786103714981141 187233075505598611639741)
                  ·
                    rfl

theorem cell23_3281716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3281716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281716 prefixEnd_3281716 := by exact prefixLift 3281716
  have htrace : WordTrace (prefixWord ++ tailWord_3281716) baseStart_3281716 baseEnd_3281716 := by
    simpa [prefixWord, tailWord_3281716, baseEnd_3281716] using wordTrace_append hprefix tailTrace_3281716
  have hstable : (prefixWord ++ tailWord_3281716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281716).length < 2 ^ (prefixWord ++ tailWord_3281716).sum := by decide
  have hdescent : baseEnd_3281716 < baseStart_3281716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281719 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 4, 3, 2]
def baseStart_3281719 : Nat := 118140960795 + 3281719 * 2 ^ 59
def prefixEnd_3281719 : Nat := 4983230072969 + 3 ^ 40 * 3281719 * 2
def baseEnd_3281719 : Nat := 1685099219992350993020155

theorem tailTrace_3281719 : CollatzResearch.WordTrace tailWord_3281719 prefixEnd_3281719 1685099219992350993020155 := by
  unfold tailWord_3281719
  simp only [CollatzResearch.WordTrace]
  refine ⟨119694125197900010828776211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79796083465266673885850807 119694125197900010828776211)
  ·
    refine ⟨179541187796850016243164317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119694125197900010828776211 179541187796850016243164317)
    ·
      refine ⟨67327945423818756091186619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179541187796850016243164317 67327945423818756091186619)
      ·
        refine ⟨100991918135728134136779929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67327945423818756091186619 100991918135728134136779929)
        ·
          refine ⟨75743938601796100602584947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100991918135728134136779929 75743938601796100602584947)
          ·
            refine ⟨113615907902694150903877421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75743938601796100602584947 113615907902694150903877421)
            ·
              refine ⟨42605965463510306588954033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113615907902694150903877421 42605965463510306588954033)
              ·
                refine ⟨31954474097632729941715525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42605965463510306588954033 31954474097632729941715525)
                ·
                  refine ⟨5991463893306136864071661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31954474097632729941715525 5991463893306136864071661)
                  ·
                    refine ⟨2246798959989801324026873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5991463893306136864071661 2246798959989801324026873)
                    ·
                      refine ⟨1685099219992350993020155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246798959989801324026873 1685099219992350993020155)
                      ·
                        rfl

theorem cell23_3281719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_3281719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281719 prefixEnd_3281719 := by exact prefixLift 3281719
  have htrace : WordTrace (prefixWord ++ tailWord_3281719) baseStart_3281719 baseEnd_3281719 := by
    simpa [prefixWord, tailWord_3281719, baseEnd_3281719] using wordTrace_append hprefix tailTrace_3281719
  have hstable : (prefixWord ++ tailWord_3281719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281719).length < 2 ^ (prefixWord ++ tailWord_3281719).sum := by decide
  have hdescent : baseEnd_3281719 < baseStart_3281719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281736 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_3281736 : Nat := 118140960795 + 3281736 * 2 ^ 59
def prefixEnd_3281736 : Nat := 4983230072969 + 3 ^ 40 * 3281736 * 2
def baseEnd_3281736 : Nat := 1685107949163477426507577

theorem tailTrace_3281736 : CollatzResearch.WordTrace tailWord_3281736 prefixEnd_3281736 1685107949163477426507577 := by
  unfold tailWord_3281736
  simp only [CollatzResearch.WordTrace]
  refine ⟨59847372619419211366072531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79796496825892281821430041 59847372619419211366072531)
  ·
    refine ⟨89771058929128817049108797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59847372619419211366072531 89771058929128817049108797)
    ·
      refine ⟨33664147098423306393415799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89771058929128817049108797 33664147098423306393415799)
      ·
        refine ⟨50496220647634959590123699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33664147098423306393415799 50496220647634959590123699)
        ·
          refine ⟨75744330971452439385185549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50496220647634959590123699 75744330971452439385185549)
          ·
            refine ⟨28404124114294664769444581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75744330971452439385185549 28404124114294664769444581)
            ·
              refine ⟨5325773271430249644270859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28404124114294664769444581 5325773271430249644270859)
              ·
                refine ⟨7988659907145374466406289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5325773271430249644270859 7988659907145374466406289)
                ·
                  refine ⟨5991494930359030849804717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7988659907145374466406289 5991494930359030849804717)
                  ·
                    refine ⟨2246810598884636568676769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5991494930359030849804717 2246810598884636568676769)
                    ·
                      refine ⟨1685107949163477426507577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246810598884636568676769 1685107949163477426507577)
                      ·
                        rfl

theorem cell23_3281736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_3281736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281736 prefixEnd_3281736 := by exact prefixLift 3281736
  have htrace : WordTrace (prefixWord ++ tailWord_3281736) baseStart_3281736 baseEnd_3281736 := by
    simpa [prefixWord, tailWord_3281736, baseEnd_3281736] using wordTrace_append hprefix tailTrace_3281736
  have hstable : (prefixWord ++ tailWord_3281736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281736).length < 2 ^ (prefixWord ++ tailWord_3281736).sum := by decide
  have hdescent : baseEnd_3281736 < baseStart_3281736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281746 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_3281746 : Nat := 118140960795 + 3281746 * 2 ^ 59
def prefixEnd_3281746 : Nat := 4983230072969 + 3 ^ 40 * 3281746 * 2
def baseEnd_3281746 : Nat := 561704361323340795794177

theorem tailTrace_3281746 : CollatzResearch.WordTrace tailWord_3281746 prefixEnd_3281746 561704361323340795794177 := by
  unfold tailWord_3281746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29923777492200548610002273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79796739979201462960006061 29923777492200548610002273)
  ·
    refine ⟨22442833119150411457501705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29923777492200548610002273 22442833119150411457501705)
    ·
      refine ⟨16832124839362808593126279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22442833119150411457501705 16832124839362808593126279)
      ·
        refine ⟨25248187259044212889689419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16832124839362808593126279 25248187259044212889689419)
        ·
          refine ⟨37872280888566319334534129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25248187259044212889689419 37872280888566319334534129)
          ·
            refine ⟨28404210666424739500900597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37872280888566319334534129 28404210666424739500900597)
            ·
              refine ⟨2662894749977319328209431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28404210666424739500900597 2662894749977319328209431)
              ·
                refine ⟨3994342124965978992314147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662894749977319328209431 3994342124965978992314147)
                ·
                  refine ⟨5991513187448968488471221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994342124965978992314147 5991513187448968488471221)
                  ·
                    refine ⟨561704361323340795794177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5991513187448968488471221 561704361323340795794177)
                    ·
                      rfl

theorem cell23_3281746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_3281746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281746 prefixEnd_3281746 := by exact prefixLift 3281746
  have htrace : WordTrace (prefixWord ++ tailWord_3281746) baseStart_3281746 baseEnd_3281746 := by
    simpa [prefixWord, tailWord_3281746, baseEnd_3281746] using wordTrace_append hprefix tailTrace_3281746
  have hstable : (prefixWord ++ tailWord_3281746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281746).length < 2 ^ (prefixWord ++ tailWord_3281746).sum := by decide
  have hdescent : baseEnd_3281746 < baseStart_3281746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281794 : List Nat := [3, 4, 2, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3281794 : Nat := 118140960795 + 3281794 * 2 ^ 59
def prefixEnd_3281794 : Nat := 4983230072969 + 3 ^ 40 * 3281794 * 2
def baseEnd_3281794 : Nat := 1685137731041438199582311

theorem tailTrace_3281794 : CollatzResearch.WordTrace tailWord_3281794 prefixEnd_3281794 1685137731041438199582311 := by
  unfold tailWord_3281794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29924215168157074659439109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79797907115085532425170957 29924215168157074659439109)
  ·
    refine ⟨5610790344029451498644833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29924215168157074659439109 5610790344029451498644833)
    ·
      refine ⟨4208092758022088623983625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5610790344029451498644833 4208092758022088623983625)
      ·
        refine ⟨3156069568516566467987719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4208092758022088623983625 3156069568516566467987719)
        ·
          refine ⟨4734104352774849701981579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156069568516566467987719 4734104352774849701981579)
          ·
            refine ⟨7101156529162274552972369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4734104352774849701981579 7101156529162274552972369)
            ·
              refine ⟨5325867396871705914729277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7101156529162274552972369 5325867396871705914729277)
              ·
                refine ⟨1997200273826889718023479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5325867396871705914729277 1997200273826889718023479)
                ·
                  refine ⟨2995800410740334577035219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997200273826889718023479 2995800410740334577035219)
                  ·
                    refine ⟨4493700616110501865552829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2995800410740334577035219 4493700616110501865552829)
                    ·
                      refine ⟨1685137731041438199582311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4493700616110501865552829 1685137731041438199582311)
                      ·
                        rfl

theorem cell23_3281794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3281794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281794 prefixEnd_3281794 := by exact prefixLift 3281794
  have htrace : WordTrace (prefixWord ++ tailWord_3281794) baseStart_3281794 baseEnd_3281794 := by
    simpa [prefixWord, tailWord_3281794, baseEnd_3281794] using wordTrace_append hprefix tailTrace_3281794
  have hstable : (prefixWord ++ tailWord_3281794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281794).length < 2 ^ (prefixWord ++ tailWord_3281794).sum := by decide
  have hdescent : baseEnd_3281794 < baseStart_3281794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281800 : List Nat := [2, 1, 3, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_3281800 : Nat := 118140960795 + 3281800 * 2 ^ 59
def prefixEnd_3281800 : Nat := 4983230072969 + 3 ^ 40 * 3281800 * 2
def baseEnd_3281800 : Nat := 1685140811925365176107283

theorem tailTrace_3281800 : CollatzResearch.WordTrace tailWord_3281800 prefixEnd_3281800 1685140811925365176107283 := by
  unfold tailWord_3281800
  simp only [CollatzResearch.WordTrace]
  refine ⟨59848539755303280831237427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79798053007071041108316569 59848539755303280831237427)
  ·
    refine ⟨89772809632954921246856141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59848539755303280831237427 89772809632954921246856141)
    ·
      refine ⟨33664803612358095467571053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89772809632954921246856141 33664803612358095467571053)
      ·
        refine ⟨12624301354634285800339145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33664803612358095467571053 12624301354634285800339145)
        ·
          refine ⟨9468226015975714350254359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12624301354634285800339145 9468226015975714350254359)
          ·
            refine ⟨14202339023963571525381539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9468226015975714350254359 14202339023963571525381539)
            ·
              refine ⟨21303508535945357288072309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14202339023963571525381539 21303508535945357288072309)
              ·
                refine ⟨1997203925244877245756779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21303508535945357288072309 1997203925244877245756779)
                ·
                  refine ⟨2995805887867315868635169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997203925244877245756779 2995805887867315868635169)
                  ·
                    refine ⟨2246854415900486901476377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2995805887867315868635169 2246854415900486901476377)
                    ·
                      refine ⟨1685140811925365176107283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246854415900486901476377 1685140811925365176107283)
                      ·
                        rfl

theorem cell23_3281800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_3281800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281800 prefixEnd_3281800 := by exact prefixLift 3281800
  have htrace : WordTrace (prefixWord ++ tailWord_3281800) baseStart_3281800 baseEnd_3281800 := by
    simpa [prefixWord, tailWord_3281800, baseEnd_3281800] using wordTrace_append hprefix tailTrace_3281800
  have hstable : (prefixWord ++ tailWord_3281800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281800).length < 2 ^ (prefixWord ++ tailWord_3281800).sum := by decide
  have hdescent : baseEnd_3281800 < baseStart_3281800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281810 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3281810 : Nat := 118140960795 + 3281810 * 2 ^ 59
def prefixEnd_3281810 : Nat := 4983230072969 + 3 ^ 40 * 3281810 * 2
def baseEnd_3281810 : Nat := 561715315577303378994079

theorem tailTrace_3281810 : CollatzResearch.WordTrace tailWord_3281810 prefixEnd_3281810 561715315577303378994079 := by
  unfold tailWord_3281810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29924361060142583342584721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79798296160380222246892589 29924361060142583342584721)
  ·
    refine ⟨22443270795106937506938541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29924361060142583342584721 22443270795106937506938541)
    ·
      refine ⟨8416226548165101565101953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22443270795106937506938541 8416226548165101565101953)
      ·
        refine ⟨6312169911123826173826465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8416226548165101565101953 6312169911123826173826465)
        ·
          refine ⟨4734127433342869630369849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6312169911123826173826465 4734127433342869630369849)
          ·
            refine ⟨3550595575007152222777387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4734127433342869630369849 3550595575007152222777387)
            ·
              refine ⟨5325893362510728334166081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550595575007152222777387 5325893362510728334166081)
              ·
                refine ⟨3994420021883046250624561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5325893362510728334166081 3994420021883046250624561)
                ·
                  refine ⟨2995815016412284687968421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994420021883046250624561 2995815016412284687968421)
                  ·
                    refine ⟨561715315577303378994079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2995815016412284687968421 561715315577303378994079)
                    ·
                      rfl

theorem cell23_3281810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3281810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281810 prefixEnd_3281810 := by exact prefixLift 3281810
  have htrace : WordTrace (prefixWord ++ tailWord_3281810) baseStart_3281810 baseEnd_3281810 := by
    simpa [prefixWord, tailWord_3281810, baseEnd_3281810] using wordTrace_append hprefix tailTrace_3281810
  have hstable : (prefixWord ++ tailWord_3281810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281810).length < 2 ^ (prefixWord ++ tailWord_3281810).sum := by decide
  have hdescent : baseEnd_3281810 < baseStart_3281810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281833 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 2, 1, 3]
def baseStart_3281833 : Nat := 118140960795 + 3281833 * 2 ^ 59
def prefixEnd_3281833 : Nat := 4983230072969 + 3 ^ 40 * 3281833 * 2
def baseEnd_3281833 : Nat := 1685157756786963546994631

theorem tailTrace_3281833 : CollatzResearch.WordTrace tailWord_3281833 prefixEnd_3281833 1685157756786963546994631 := by
  unfold tailWord_3281833
  simp only [CollatzResearch.WordTrace]
  refine ⟨119698283119487008298426153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79798855412991338865617435 119698283119487008298426153)
  ·
    refine ⟨89773712339615256223819615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119698283119487008298426153 89773712339615256223819615)
    ·
      refine ⟨134660568509422884335729423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89773712339615256223819615 134660568509422884335729423)
      ·
        refine ⟨201990852764134326503594135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134660568509422884335729423 201990852764134326503594135)
        ·
          refine ⟨302986279146201489755391203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201990852764134326503594135 302986279146201489755391203)
          ·
            refine ⟨454479418719302234633086805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302986279146201489755391203 454479418719302234633086805)
            ·
              refine ⟨2662965344058411531053243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 454479418719302234633086805 2662965344058411531053243)
              ·
                refine ⟨3994448016087617296579865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662965344058411531053243 3994448016087617296579865)
                ·
                  refine ⟨2995836012065712972434899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994448016087617296579865 2995836012065712972434899)
                  ·
                    refine ⟨4493754018098569458652349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2995836012065712972434899 4493754018098569458652349)
                    ·
                      refine ⟨1685157756786963546994631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4493754018098569458652349 1685157756786963546994631)
                      ·
                        rfl

theorem cell23_3281833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 1, 3].length) (baseStart_3281833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281833 prefixEnd_3281833 := by exact prefixLift 3281833
  have htrace : WordTrace (prefixWord ++ tailWord_3281833) baseStart_3281833 baseEnd_3281833 := by
    simpa [prefixWord, tailWord_3281833, baseEnd_3281833] using wordTrace_append hprefix tailTrace_3281833
  have hstable : (prefixWord ++ tailWord_3281833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281833).length < 2 ^ (prefixWord ++ tailWord_3281833).sum := by decide
  have hdescent : baseEnd_3281833 < baseStart_3281833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281872 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_3281872 : Nat := 118140960795 + 3281872 * 2 ^ 59
def prefixEnd_3281872 : Nat := 4983230072969 + 3 ^ 40 * 3281872 * 2
def baseEnd_3281872 : Nat := 1685177782532488894406951

theorem tailTrace_3281872 : CollatzResearch.WordTrace tailWord_3281872 prefixEnd_3281872 1685177782532488894406951 := by
  unfold tailWord_3281872
  simp only [CollatzResearch.WordTrace]
  refine ⟨59849852783172858979547935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79799803710897145306063913 59849852783172858979547935)
  ·
    refine ⟨89774779174759288469321903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59849852783172858979547935 89774779174759288469321903)
    ·
      refine ⟨134662168762138932703982855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89774779174759288469321903 134662168762138932703982855)
      ·
        refine ⟨201993253143208399055974283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134662168762138932703982855 201993253143208399055974283)
        ·
          refine ⟨302989879714812598583961425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201993253143208399055974283 302989879714812598583961425)
          ·
            refine ⟨227242409786109448937971069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302989879714812598583961425 227242409786109448937971069)
            ·
              refine ⟨85215903669791043351739151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227242409786109448937971069 85215903669791043351739151)
              ·
                refine ⟨127823855504686565027608727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85215903669791043351739151 127823855504686565027608727)
                ·
                  refine ⟨191735783257029847541413091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127823855504686565027608727 191735783257029847541413091)
                  ·
                    refine ⟨287603674885544771312119637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191735783257029847541413091 287603674885544771312119637)
                    ·
                      refine ⟨1685177782532488894406951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 287603674885544771312119637 1685177782532488894406951)
                      ·
                        rfl

theorem cell23_3281872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_3281872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281872 prefixEnd_3281872 := by exact prefixLift 3281872
  have htrace : WordTrace (prefixWord ++ tailWord_3281872) baseStart_3281872 baseEnd_3281872 := by
    simpa [prefixWord, tailWord_3281872, baseEnd_3281872] using wordTrace_append hprefix tailTrace_3281872
  have hstable : (prefixWord ++ tailWord_3281872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281872).length < 2 ^ (prefixWord ++ tailWord_3281872).sum := by decide
  have hdescent : baseEnd_3281872 < baseStart_3281872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281873 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 2, 2, 2]
def baseStart_3281873 : Nat := 118140960795 + 3281873 * 2 ^ 59
def prefixEnd_3281873 : Nat := 4983230072969 + 3 ^ 40 * 3281873 * 2
def baseEnd_3281873 : Nat := 1685178296013143390494447

theorem tailTrace_3281873 : CollatzResearch.WordTrace tailWord_3281873 prefixEnd_3281873 1685178296013143390494447 := by
  unfold tailWord_3281873
  simp only [CollatzResearch.WordTrace]
  refine ⟨119699742039342095129882273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79799828026228063419921515 119699742039342095129882273)
  ·
    refine ⟨89774806529506571347411705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119699742039342095129882273 89774806529506571347411705)
    ·
      refine ⟨67331104897129928510558779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89774806529506571347411705 67331104897129928510558779)
      ·
        refine ⟨100996657345694892765838169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67331104897129928510558779 100996657345694892765838169)
        ·
          refine ⟨75747493009271169574378627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100996657345694892765838169 75747493009271169574378627)
          ·
            refine ⟨113621239513906754361567941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75747493009271169574378627 113621239513906754361567941)
            ·
              refine ⟨21303982408857516442793989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113621239513906754361567941 21303982408857516442793989)
              ·
                refine ⟨3994496701660784333023873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21303982408857516442793989 3994496701660784333023873)
                ·
                  refine ⟨2995872526245588249767905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994496701660784333023873 2995872526245588249767905)
                  ·
                    refine ⟨2246904394684191187325929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2995872526245588249767905 2246904394684191187325929)
                    ·
                      refine ⟨1685178296013143390494447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2246904394684191187325929 1685178296013143390494447)
                      ·
                        rfl

theorem cell23_3281873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_3281873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281873 prefixEnd_3281873 := by exact prefixLift 3281873
  have htrace : WordTrace (prefixWord ++ tailWord_3281873) baseStart_3281873 baseEnd_3281873 := by
    simpa [prefixWord, tailWord_3281873, baseEnd_3281873] using wordTrace_append hprefix tailTrace_3281873
  have hstable : (prefixWord ++ tailWord_3281873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281873).length < 2 ^ (prefixWord ++ tailWord_3281873).sum := by decide
  have hdescent : baseEnd_3281873 < baseStart_3281873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281889 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_3281889 : Nat := 118140960795 + 3281889 * 2 ^ 59
def prefixEnd_3281889 : Nat := 4983230072969 + 3 ^ 40 * 3281889 * 2
def baseEnd_3281889 : Nat := 1685186511703615327894373

theorem tailTrace_3281889 : CollatzResearch.WordTrace tailWord_3281889 prefixEnd_3281889 1685186511703615327894373 := by
  unfold tailWord_3281889
  simp only [CollatzResearch.WordTrace]
  refine ⟨119700325607284129862464721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79800217071522753241643147 119700325607284129862464721)
  ·
    refine ⟨89775244205463097396848541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119700325607284129862464721 89775244205463097396848541)
    ·
      refine ⟨33665716577048661523818203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89775244205463097396848541 33665716577048661523818203)
      ·
        refine ⟨50498574865572992285727305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33665716577048661523818203 50498574865572992285727305)
        ·
          refine ⟨37873931149179744214295479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50498574865572992285727305 37873931149179744214295479)
          ·
            refine ⟨56810896723769616321443219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37873931149179744214295479 56810896723769616321443219)
            ·
              refine ⟨85216345085654424482164829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56810896723769616321443219 85216345085654424482164829)
              ·
                refine ⟨31956129407120409180811811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85216345085654424482164829 31956129407120409180811811)
                ·
                  refine ⟨47934194110680613771217717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31956129407120409180811811 47934194110680613771217717)
                  ·
                    refine ⟨4493830697876307541051661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47934194110680613771217717 4493830697876307541051661)
                    ·
                      refine ⟨1685186511703615327894373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4493830697876307541051661 1685186511703615327894373)
                      ·
                        rfl

theorem cell23_3281889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_3281889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281889 prefixEnd_3281889 := by exact prefixLift 3281889
  have htrace : WordTrace (prefixWord ++ tailWord_3281889) baseStart_3281889 baseEnd_3281889 := by
    simpa [prefixWord, tailWord_3281889, baseEnd_3281889] using wordTrace_append hprefix tailTrace_3281889
  have hstable : (prefixWord ++ tailWord_3281889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281889).length < 2 ^ (prefixWord ++ tailWord_3281889).sum := by decide
  have hdescent : baseEnd_3281889 < baseStart_3281889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281930 : List Nat := [3, 1, 2, 2, 3, 3, 2, 2, 5]
def baseStart_3281930 : Nat := 118140960795 + 3281930 * 2 ^ 59
def prefixEnd_3281930 : Nat := 4983230072969 + 3 ^ 40 * 3281930 * 2
def baseEnd_3281930 : Nat := 187245284934494407497965

theorem tailTrace_3281930 : CollatzResearch.WordTrace tailWord_3281930 prefixEnd_3281930 187245284934494407497965 := by
  unfold tailWord_3281930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29925455250033898466176811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79801214000090395909804829 29925455250033898466176811)
  ·
    refine ⟨44888182875050847699265217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29925455250033898466176811 44888182875050847699265217)
    ·
      refine ⟨33666137156288135774448913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44888182875050847699265217 33666137156288135774448913)
      ·
        refine ⟨25249602867216101830836685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33666137156288135774448913 25249602867216101830836685)
        ·
          refine ⟨9468601075206038186563757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25249602867216101830836685 9468601075206038186563757)
          ·
            refine ⟨3550725403202264319961409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9468601075206038186563757 3550725403202264319961409)
            ·
              refine ⟨2663044052401698239971057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550725403202264319961409 2663044052401698239971057)
              ·
                refine ⟨1997283039301273679978293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663044052401698239971057 1997283039301273679978293)
                ·
                  refine ⟨187245284934494407497965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997283039301273679978293 187245284934494407497965)
                  ·
                    rfl

theorem cell23_3281930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_3281930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281930 prefixEnd_3281930 := by exact prefixLift 3281930
  have htrace : WordTrace (prefixWord ++ tailWord_3281930) baseStart_3281930 baseEnd_3281930 := by
    simpa [prefixWord, tailWord_3281930, baseEnd_3281930] using wordTrace_append hprefix tailTrace_3281930
  have hstable : (prefixWord ++ tailWord_3281930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281930).length < 2 ^ (prefixWord ++ tailWord_3281930).sum := by decide
  have hdescent : baseEnd_3281930 < baseStart_3281930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281969 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 8]
def baseStart_3281969 : Nat := 118140960795 + 3281969 * 2 ^ 59
def prefixEnd_3281969 : Nat := 4983230072969 + 3 ^ 40 * 3281969 * 2
def baseEnd_3281969 : Nat := 187247510017330557210445

theorem tailTrace_3281969 : CollatzResearch.WordTrace tailWord_3281969 prefixEnd_3281969 187247510017330557210445 := by
  unfold tailWord_3281969
  simp only [CollatzResearch.WordTrace]
  refine ⟨119703243446994303525376961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79802162297996202350251307 119703243446994303525376961)
  ·
    refine ⟨89777432585245727644032721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119703243446994303525376961 89777432585245727644032721)
    ·
      refine ⟨67333074438934295733024541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89777432585245727644032721 67333074438934295733024541)
      ·
        refine ⟨25249902914600360899884203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67333074438934295733024541 25249902914600360899884203)
        ·
          refine ⟨37874854371900541349826305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25249902914600360899884203 37874854371900541349826305)
          ·
            refine ⟨28406140778925406012369729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37874854371900541349826305 28406140778925406012369729)
            ·
              refine ⟨21304605584194054509277297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28406140778925406012369729 21304605584194054509277297)
              ·
                refine ⟨15978454188145540881957973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21304605584194054509277297 15978454188145540881957973)
                ·
                  refine ⟨187247510017330557210445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15978454188145540881957973 187247510017330557210445)
                  ·
                    rfl

theorem cell23_3281969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 8].length) (baseStart_3281969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281969 prefixEnd_3281969 := by exact prefixLift 3281969
  have htrace : WordTrace (prefixWord ++ tailWord_3281969) baseStart_3281969 baseEnd_3281969 := by
    simpa [prefixWord, tailWord_3281969, baseEnd_3281969] using wordTrace_append hprefix tailTrace_3281969
  have hstable : (prefixWord ++ tailWord_3281969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281969).length < 2 ^ (prefixWord ++ tailWord_3281969).sum := by decide
  have hdescent : baseEnd_3281969 < baseStart_3281969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281989 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_3281989 : Nat := 118140960795 + 3281989 * 2 ^ 59
def prefixEnd_3281989 : Nat := 4983230072969 + 3 ^ 40 * 3281989 * 2
def baseEnd_3281989 : Nat := 1685237859769064936643913

theorem tailTrace_3281989 : CollatzResearch.WordTrace tailWord_3281989 prefixEnd_3281989 1685237859769064936643913 := by
  unfold tailWord_3281989
  simp only [CollatzResearch.WordTrace]
  refine ⟨119703972906921846941105021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79802648604614564627403347 119703972906921846941105021)
  ·
    refine ⟨44888989840095692602914383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119703972906921846941105021 44888989840095692602914383)
    ·
      refine ⟨67333484760143538904371575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44888989840095692602914383 67333484760143538904371575)
      ·
        refine ⟨101000227140215308356557363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67333484760143538904371575 101000227140215308356557363)
        ·
          refine ⟨151500340710322962534836045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101000227140215308356557363 151500340710322962534836045)
          ·
            refine ⟨56812627766371110950563517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151500340710322962534836045 56812627766371110950563517)
            ·
              refine ⟨21304735412389166606461319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56812627766371110950563517 21304735412389166606461319)
              ·
                refine ⟨31957103118583749909691979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21304735412389166606461319 31957103118583749909691979)
                ·
                  refine ⟨47935654677875624864537969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31957103118583749909691979 47935654677875624864537969)
                  ·
                    refine ⟨35951741008406718648403477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47935654677875624864537969 35951741008406718648403477)
                    ·
                      refine ⟨1685237859769064936643913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35951741008406718648403477 1685237859769064936643913)
                      ·
                        rfl

theorem cell23_3281989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_3281989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281989 prefixEnd_3281989 := by exact prefixLift 3281989
  have htrace : WordTrace (prefixWord ++ tailWord_3281989) baseStart_3281989 baseEnd_3281989 := by
    simpa [prefixWord, tailWord_3281989, baseEnd_3281989] using wordTrace_append hprefix tailTrace_3281989
  have hstable : (prefixWord ++ tailWord_3281989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281989).length < 2 ^ (prefixWord ++ tailWord_3281989).sum := by decide
  have hdescent : baseEnd_3281989 < baseStart_3281989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281990 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_3281990 : Nat := 118140960795 + 3281990 * 2 ^ 59
def prefixEnd_3281990 : Nat := 4983230072969 + 3 ^ 40 * 3281990 * 2
def baseEnd_3281990 : Nat := 561746124416573144243803

theorem tailTrace_3281990 : CollatzResearch.WordTrace tailWord_3281990 prefixEnd_3281990 561746124416573144243803 := by
  unfold tailWord_3281990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740750293122444503496607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79802672919945482741260949 3740750293122444503496607)
  ·
    refine ⟨5611125439683666755244911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3740750293122444503496607 5611125439683666755244911)
    ·
      refine ⟨8416688159525500132867367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5611125439683666755244911 8416688159525500132867367)
      ·
        refine ⟨12625032239288250199301051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8416688159525500132867367 12625032239288250199301051)
        ·
          refine ⟨18937548358932375298951577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625032239288250199301051 18937548358932375298951577)
          ·
            refine ⟨14203161269199281474213683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18937548358932375298951577 14203161269199281474213683)
            ·
              refine ⟨21304741903798922211320525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14203161269199281474213683 21304741903798922211320525)
              ·
                refine ⟨7989278213924595829245197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21304741903798922211320525 7989278213924595829245197)
                ·
                  refine ⟨2995979330221723435966949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7989278213924595829245197 2995979330221723435966949)
                  ·
                    refine ⟨561746124416573144243803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2995979330221723435966949 561746124416573144243803)
                    ·
                      rfl

theorem cell23_3281990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_3281990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3281990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3281990 prefixEnd_3281990 := by exact prefixLift 3281990
  have htrace : WordTrace (prefixWord ++ tailWord_3281990) baseStart_3281990 baseEnd_3281990 := by
    simpa [prefixWord, tailWord_3281990, baseEnd_3281990] using wordTrace_append hprefix tailTrace_3281990
  have hstable : (prefixWord ++ tailWord_3281990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281990).length < 2 ^ (prefixWord ++ tailWord_3281990).sum := by decide
  have hdescent : baseEnd_3281990 < baseStart_3281990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282023 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_3282023 : Nat := 118140960795 + 3282023 * 2 ^ 59
def prefixEnd_3282023 : Nat := 4983230072969 + 3 ^ 40 * 3282023 * 2
def baseEnd_3282023 : Nat := 1685255318111317803618757

theorem tailTrace_3282023 : CollatzResearch.WordTrace tailWord_3282023 prefixEnd_3282023 1685255318111317803618757 := by
  unfold tailWord_3282023
  simp only [CollatzResearch.WordTrace]
  refine ⟨119705212988798670747842723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79803475325865780498561815 119705212988798670747842723)
  ·
    refine ⟨179557819483198006121764085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119705212988798670747842723 179557819483198006121764085)
    ·
      refine ⟨16833545576549813073915383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179557819483198006121764085 16833545576549813073915383)
      ·
        refine ⟨25250318364824719610873075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16833545576549813073915383 25250318364824719610873075)
        ·
          refine ⟨37875477547237079416309613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25250318364824719610873075 37875477547237079416309613)
          ·
            refine ⟨14203304080213904781116105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37875477547237079416309613 14203304080213904781116105)
            ·
              refine ⟨10652478060160428585837079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14203304080213904781116105 10652478060160428585837079)
              ·
                refine ⟨15978717090240642878755619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652478060160428585837079 15978717090240642878755619)
                ·
                  refine ⟨23968075635360964318133429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15978717090240642878755619 23968075635360964318133429)
                  ·
                    refine ⟨2247007090815090404825009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23968075635360964318133429 2247007090815090404825009)
                    ·
                      refine ⟨1685255318111317803618757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247007090815090404825009 1685255318111317803618757)
                      ·
                        rfl

theorem cell23_3282023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_3282023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282023 prefixEnd_3282023 := by exact prefixLift 3282023
  have htrace : WordTrace (prefixWord ++ tailWord_3282023) baseStart_3282023 baseEnd_3282023 := by
    simpa [prefixWord, tailWord_3282023, baseEnd_3282023] using wordTrace_append hprefix tailTrace_3282023
  have hstable : (prefixWord ++ tailWord_3282023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282023).length < 2 ^ (prefixWord ++ tailWord_3282023).sum := by decide
  have hdescent : baseEnd_3282023 < baseStart_3282023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282024 : List Nat := [2, 1, 4, 4, 1, 2, 1, 3, 1, 4]
def baseStart_3282024 : Nat := 118140960795 + 3282024 * 2 ^ 59
def prefixEnd_3282024 : Nat := 4983230072969 + 3 ^ 40 * 3282024 * 2
def baseEnd_3282024 : Nat := 561751943863990766568751

theorem tailTrace_3282024 : CollatzResearch.WordTrace tailWord_3282024 prefixEnd_3282024 561751943863990766568751 := by
  unfold tailWord_3282024
  simp only [CollatzResearch.WordTrace]
  refine ⟨59852624730897523959314563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79803499641196698612419417 59852624730897523959314563)
  ·
    refine ⟨89778937096346285938971845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59852624730897523959314563 89778937096346285938971845)
    ·
      refine ⟨16833550705564928613557221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89778937096346285938971845 16833550705564928613557221)
      ·
        refine ⟨3156290757293424115041979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16833550705564928613557221 3156290757293424115041979)
        ·
          refine ⟨4734436135940136172562969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156290757293424115041979 4734436135940136172562969)
          ·
            refine ⟨3550827101955102129422227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4734436135940136172562969 3550827101955102129422227)
            ·
              refine ⟨5326240652932653194133341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550827101955102129422227 5326240652932653194133341)
              ·
                refine ⟨1997340244849744947800003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5326240652932653194133341 1997340244849744947800003)
                ·
                  refine ⟨2996010367274617421700005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997340244849744947800003 2996010367274617421700005)
                  ·
                    refine ⟨561751943863990766568751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2996010367274617421700005 561751943863990766568751)
                    ·
                      rfl

theorem cell23_3282024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_3282024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282024 prefixEnd_3282024 := by exact prefixLift 3282024
  have htrace : WordTrace (prefixWord ++ tailWord_3282024) baseStart_3282024 baseEnd_3282024 := by
    simpa [prefixWord, tailWord_3282024, baseEnd_3282024] using wordTrace_append hprefix tailTrace_3282024
  have hstable : (prefixWord ++ tailWord_3282024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282024).length < 2 ^ (prefixWord ++ tailWord_3282024).sum := by decide
  have hdescent : baseEnd_3282024 < baseStart_3282024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282076 : List Nat := [2, 2, 3, 2, 1, 2, 2, 9]
def baseStart_3282076 : Nat := 118140960795 + 3282076 * 2 ^ 59
def prefixEnd_3282076 : Nat := 4983230072969 + 3 ^ 40 * 3282076 * 2
def baseEnd_3282076 : Nat := 62417871577259485046519

theorem tailTrace_3282076 : CollatzResearch.WordTrace tailWord_3282076 prefixEnd_3282076 62417871577259485046519 := by
  unfold tailWord_3282076
  simp only [CollatzResearch.WordTrace]
  refine ⟨59853573028803330399761041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79804764038404440533014721 59853573028803330399761041)
  ·
    refine ⟨44890179771602497799820781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59853573028803330399761041 44890179771602497799820781)
    ·
      refine ⟨16833817414350936674932793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44890179771602497799820781 16833817414350936674932793)
      ·
        refine ⟨12625363060763202506199595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16833817414350936674932793 12625363060763202506199595)
        ·
          refine ⟨18938044591144803759299393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625363060763202506199595 18938044591144803759299393)
          ·
            refine ⟨14203533443358602819474545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18938044591144803759299393 14203533443358602819474545)
            ·
              refine ⟨10652650082518952114605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14203533443358602819474545 10652650082518952114605909)
              ·
                refine ⟨62417871577259485046519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10652650082518952114605909 62417871577259485046519)
                ·
                  rfl

theorem cell23_3282076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 9].length) (baseStart_3282076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282076 prefixEnd_3282076 := by exact prefixLift 3282076
  have htrace : WordTrace (prefixWord ++ tailWord_3282076) baseStart_3282076 baseEnd_3282076 := by
    simpa [prefixWord, tailWord_3282076, baseEnd_3282076] using wordTrace_append hprefix tailTrace_3282076
  have hstable : (prefixWord ++ tailWord_3282076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282076).length < 2 ^ (prefixWord ++ tailWord_3282076).sum := by decide
  have hdescent : baseEnd_3282076 < baseStart_3282076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282087 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_3282087 : Nat := 118140960795 + 3282087 * 2 ^ 59
def prefixEnd_3282087 : Nat := 4983230072969 + 3 ^ 40 * 3282087 * 2
def baseEnd_3282087 : Nat := 1685288180873205553218463

theorem tailTrace_3282087 : CollatzResearch.WordTrace tailWord_3282087 prefixEnd_3282087 1685288180873205553218463 := by
  unfold tailWord_3282087
  simp only [CollatzResearch.WordTrace]
  refine ⟨119707547260566809678172515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79805031507044539785448343 119707547260566809678172515)
  ·
    refine ⟨179561320890850214517258773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119707547260566809678172515 179561320890850214517258773)
    ·
      refine ⟨8416936916758603805496505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179561320890850214517258773 8416936916758603805496505)
      ·
        refine ⟨6312702687568952854122379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8416936916758603805496505 6312702687568952854122379)
        ·
          refine ⟨9469054031353429281183569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6312702687568952854122379 9469054031353429281183569)
          ·
            refine ⟨7101790523515071960887677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9469054031353429281183569 7101790523515071960887677)
            ·
              refine ⟨2663171446318151985332879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7101790523515071960887677 2663171446318151985332879)
              ·
                refine ⟨3994757169477227977999319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663171446318151985332879 3994757169477227977999319)
                ·
                  refine ⟨5992135754215841966998979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994757169477227977999319 5992135754215841966998979)
                  ·
                    refine ⟨8988203631323762950498469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5992135754215841966998979 8988203631323762950498469)
                    ·
                      refine ⟨1685288180873205553218463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8988203631323762950498469 1685288180873205553218463)
                      ·
                        rfl

theorem cell23_3282087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_3282087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282087 prefixEnd_3282087 := by exact prefixLift 3282087
  have htrace : WordTrace (prefixWord ++ tailWord_3282087) baseStart_3282087 baseEnd_3282087 := by
    simpa [prefixWord, tailWord_3282087, baseEnd_3282087] using wordTrace_append hprefix tailTrace_3282087
  have hstable : (prefixWord ++ tailWord_3282087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282087).length < 2 ^ (prefixWord ++ tailWord_3282087).sum := by decide
  have hdescent : baseEnd_3282087 < baseStart_3282087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282090 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3282090 : Nat := 118140960795 + 3282090 * 2 ^ 59
def prefixEnd_3282090 : Nat := 4983230072969 + 3 ^ 40 * 3282090 * 2
def baseEnd_3282090 : Nat := 1685289721315169041480949

theorem tailTrace_3282090 : CollatzResearch.WordTrace tailWord_3282090 prefixEnd_3282090 1685289721315169041480949 := by
  unfold tailWord_3282090
  simp only [CollatzResearch.WordTrace]
  refine ⟨29926914169888985297632931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79805104453037294127021149 29926914169888985297632931)
  ·
    refine ⟨44890371254833477946449397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29926914169888985297632931 44890371254833477946449397)
    ·
      refine ⟨4208472305140638557479631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44890371254833477946449397 4208472305140638557479631)
      ·
        refine ⟨6312708457710957836219447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208472305140638557479631 6312708457710957836219447)
        ·
          refine ⟨9469062686566436754329171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6312708457710957836219447 9469062686566436754329171)
          ·
            refine ⟨14203594029849655131493757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9469062686566436754329171 14203594029849655131493757)
            ·
              refine ⟨5326347761193620674310159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14203594029849655131493757 5326347761193620674310159)
              ·
                refine ⟨7989521641790431011465239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326347761193620674310159 7989521641790431011465239)
                ·
                  refine ⟨11984282462685646517197859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7989521641790431011465239 11984282462685646517197859)
                  ·
                    refine ⟨17976423694028469775796789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11984282462685646517197859 17976423694028469775796789)
                    ·
                      refine ⟨1685289721315169041480949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17976423694028469775796789 1685289721315169041480949)
                      ·
                        rfl

theorem cell23_3282090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3282090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282090 prefixEnd_3282090 := by exact prefixLift 3282090
  have htrace : WordTrace (prefixWord ++ tailWord_3282090) baseStart_3282090 baseEnd_3282090 := by
    simpa [prefixWord, tailWord_3282090, baseEnd_3282090] using wordTrace_append hprefix tailTrace_3282090
  have hstable : (prefixWord ++ tailWord_3282090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282090).length < 2 ^ (prefixWord ++ tailWord_3282090).sum := by decide
  have hdescent : baseEnd_3282090 < baseStart_3282090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282093 : List Nat := [1, 5, 2, 1, 4, 10]
def baseStart_3282093 : Nat := 118140960795 + 3282093 * 2 ^ 59
def prefixEnd_3282093 : Nat := 4983230072969 + 3 ^ 40 * 3282093 * 2
def baseEnd_3282093 : Nat := 6935354986654866377545

theorem tailTrace_3282093 : CollatzResearch.WordTrace tailWord_3282093 prefixEnd_3282093 6935354986654866377545 := by
  unfold tailWord_3282093
  simp only [CollatzResearch.WordTrace]
  refine ⟨119707766098545072702890933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79805177399030048468593955 119707766098545072702890933)
  ·
    refine ⟨11222603071738600565896025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119707766098545072702890933 11222603071738600565896025)
    ·
      refine ⟨8416952303803950424422019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11222603071738600565896025 8416952303803950424422019)
      ·
        refine ⟨12625428455705925636633029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8416952303803950424422019 12625428455705925636633029)
        ·
          refine ⟨2367267835444861056868693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12625428455705925636633029 2367267835444861056868693)
          ·
            refine ⟨6935354986654866377545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2367267835444861056868693 6935354986654866377545)
            ·
              rfl

theorem cell23_3282093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 10].length) (baseStart_3282093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282093 prefixEnd_3282093 := by exact prefixLift 3282093
  have htrace : WordTrace (prefixWord ++ tailWord_3282093) baseStart_3282093 baseEnd_3282093 := by
    simpa [prefixWord, tailWord_3282093, baseEnd_3282093] using wordTrace_append hprefix tailTrace_3282093
  have hstable : (prefixWord ++ tailWord_3282093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282093).length < 2 ^ (prefixWord ++ tailWord_3282093).sum := by decide
  have hdescent : baseEnd_3282093 < baseStart_3282093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282120 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_3282120 : Nat := 118140960795 + 3282120 * 2 ^ 59
def prefixEnd_3282120 : Nat := 4983230072969 + 3 ^ 40 * 3282120 * 2
def baseEnd_3282120 : Nat := 1685305125734803924105811

theorem tailTrace_3282120 : CollatzResearch.WordTrace tailWord_3282120 prefixEnd_3282120 1685305125734803924105811 := by
  unfold tailWord_3282120
  simp only [CollatzResearch.WordTrace]
  refine ⟨59854375434723628157061907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79805833912964837542749209 59854375434723628157061907)
  ·
    refine ⟨89781563152085442235592861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59854375434723628157061907 89781563152085442235592861)
    ·
      refine ⟨33668086182032040838347323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89781563152085442235592861 33668086182032040838347323)
      ·
        refine ⟨50502129273048061257520985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33668086182032040838347323 50502129273048061257520985)
        ·
          refine ⟨37876596954786045943140739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50502129273048061257520985 37876596954786045943140739)
          ·
            refine ⟨56814895432179068914711109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37876596954786045943140739 56814895432179068914711109)
            ·
              refine ⟨10652792893533575421508333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56814895432179068914711109 10652792893533575421508333)
              ·
                refine ⟨3994797335075090783065625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10652792893533575421508333 3994797335075090783065625)
                ·
                  refine ⟨2996098001306318087299219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994797335075090783065625 2996098001306318087299219)
                  ·
                    refine ⟨4494147001959477130948829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2996098001306318087299219 4494147001959477130948829)
                    ·
                      refine ⟨1685305125734803924105811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4494147001959477130948829 1685305125734803924105811)
                      ·
                        rfl

theorem cell23_3282120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_3282120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282120 prefixEnd_3282120 := by exact prefixLift 3282120
  have htrace : WordTrace (prefixWord ++ tailWord_3282120) baseStart_3282120 baseEnd_3282120 := by
    simpa [prefixWord, tailWord_3282120, baseEnd_3282120] using wordTrace_append hprefix tailTrace_3282120
  have hstable : (prefixWord ++ tailWord_3282120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282120).length < 2 ^ (prefixWord ++ tailWord_3282120).sum := by decide
  have hdescent : baseEnd_3282120 < baseStart_3282120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282130 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_3282130 : Nat := 118140960795 + 3282130 * 2 ^ 59
def prefixEnd_3282130 : Nat := 4983230072969 + 3 ^ 40 * 3282130 * 2
def baseEnd_3282130 : Nat := 1685310260541348884980765

theorem tailTrace_3282130 : CollatzResearch.WordTrace tailWord_3282130 prefixEnd_3282130 1685310260541348884980765 := by
  unfold tailWord_3282130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29927278899852757005496961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79806077066274018681325229 29927278899852757005496961)
  ·
    refine ⟨22445459174889567754122721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29927278899852757005496961 22445459174889567754122721)
    ·
      refine ⟨16834094381167175815592041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22445459174889567754122721 16834094381167175815592041)
      ·
        refine ⟨12625570785875381861694031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16834094381167175815592041 12625570785875381861694031)
        ·
          refine ⟨18938356178813072792541047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625570785875381861694031 18938356178813072792541047)
          ·
            refine ⟨28407534268219609188811571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18938356178813072792541047 28407534268219609188811571)
            ·
              refine ⟨42611301402329413783217357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28407534268219609188811571 42611301402329413783217357)
              ·
                refine ⟨15979238025873530168706509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42611301402329413783217357 15979238025873530168706509)
                ·
                  refine ⟨5992214259702573813264941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15979238025873530168706509 5992214259702573813264941)
                  ·
                    refine ⟨2247080347388465179974353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5992214259702573813264941 2247080347388465179974353)
                    ·
                      refine ⟨1685310260541348884980765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247080347388465179974353 1685310260541348884980765)
                      ·
                        rfl

theorem cell23_3282130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_3282130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282130 prefixEnd_3282130 := by exact prefixLift 3282130
  have htrace : WordTrace (prefixWord ++ tailWord_3282130) baseStart_3282130 baseEnd_3282130 := by
    simpa [prefixWord, tailWord_3282130, baseEnd_3282130] using wordTrace_append hprefix tailTrace_3282130
  have hstable : (prefixWord ++ tailWord_3282130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282130).length < 2 ^ (prefixWord ++ tailWord_3282130).sum := by decide
  have hdescent : baseEnd_3282130 < baseStart_3282130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282141 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_3282141 : Nat := 118140960795 + 3282141 * 2 ^ 59
def prefixEnd_3282141 : Nat := 4983230072969 + 3 ^ 40 * 3282141 * 2
def baseEnd_3282141 : Nat := 1685315908828548341943215

theorem tailTrace_3282141 : CollatzResearch.WordTrace tailWord_3282141 prefixEnd_3282141 1685315908828548341943215 := by
  unfold tailWord_3282141
  simp only [CollatzResearch.WordTrace]
  refine ⟨119709516802371176900638277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79806344534914117933758851 119709516802371176900638277)
  ·
    refine ⟨22445534400444595668869677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119709516802371176900638277 22445534400444595668869677)
    ·
      refine ⟨8417075400166723375826129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22445534400444595668869677 8417075400166723375826129)
      ·
        refine ⟨6312806550125042531869597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8417075400166723375826129 6312806550125042531869597)
        ·
          refine ⟨2367302456296890949451099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6312806550125042531869597 2367302456296890949451099)
          ·
            refine ⟨3550953684445336424176649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367302456296890949451099 3550953684445336424176649)
            ·
              refine ⟨2663215263334002318132487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550953684445336424176649 2663215263334002318132487)
              ·
                refine ⟨3994822895001003477198731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663215263334002318132487 3994822895001003477198731)
                ·
                  refine ⟨5992234342501505215798097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994822895001003477198731 5992234342501505215798097)
                  ·
                    refine ⟨4494175756876128911848573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5992234342501505215798097 4494175756876128911848573)
                    ·
                      refine ⟨1685315908828548341943215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4494175756876128911848573 1685315908828548341943215)
                      ·
                        rfl

theorem cell23_3282141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_3282141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282141 prefixEnd_3282141 := by exact prefixLift 3282141
  have htrace : WordTrace (prefixWord ++ tailWord_3282141) baseStart_3282141 baseEnd_3282141 := by
    simpa [prefixWord, tailWord_3282141, baseEnd_3282141] using wordTrace_append hprefix tailTrace_3282141
  have hstable : (prefixWord ++ tailWord_3282141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282141).length < 2 ^ (prefixWord ++ tailWord_3282141).sum := by decide
  have hdescent : baseEnd_3282141 < baseStart_3282141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282177 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_3282177 : Nat := 118140960795 + 3282177 * 2 ^ 59
def prefixEnd_3282177 : Nat := 4983230072969 + 3 ^ 40 * 3282177 * 2
def baseEnd_3282177 : Nat := 1685334394132110201093049

theorem tailTrace_3282177 : CollatzResearch.WordTrace tailWord_3282177 prefixEnd_3282177 1685334394132110201093049 := by
  unfold tailWord_3282177
  simp only [CollatzResearch.WordTrace]
  refine ⟨119710829830240755048948785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79807219886827170032632523 119710829830240755048948785)
  ·
    refine ⟨89783122372680566286711589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119710829830240755048948785 89783122372680566286711589)
    ·
      refine ⟨16834335444877606178758423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89783122372680566286711589 16834335444877606178758423)
      ·
        refine ⟨25251503167316409268137635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16834335444877606178758423 25251503167316409268137635)
        ·
          refine ⟨37877254750974613902206453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25251503167316409268137635 37877254750974613902206453)
          ·
            refine ⟨3550992632903870053331855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37877254750974613902206453 3550992632903870053331855)
            ·
              refine ⟨5326488949355805079997783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550992632903870053331855 5326488949355805079997783)
              ·
                refine ⟨7989733424033707619996675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326488949355805079997783 7989733424033707619996675)
                ·
                  refine ⟨11984600136050561429995013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7989733424033707619996675 11984600136050561429995013)
                  ·
                    refine ⟨2247112525509480268124065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11984600136050561429995013 2247112525509480268124065)
                    ·
                      refine ⟨1685334394132110201093049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247112525509480268124065 1685334394132110201093049)
                      ·
                        rfl

theorem cell23_3282177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_3282177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282177 prefixEnd_3282177 := by exact prefixLift 3282177
  have htrace : WordTrace (prefixWord ++ tailWord_3282177) baseStart_3282177 baseEnd_3282177 := by
    simpa [prefixWord, tailWord_3282177, baseEnd_3282177] using wordTrace_append hprefix tailTrace_3282177
  have hstable : (prefixWord ++ tailWord_3282177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282177).length < 2 ^ (prefixWord ++ tailWord_3282177).sum := by decide
  have hdescent : baseEnd_3282177 < baseStart_3282177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282200 : List Nat := [2, 1, 2, 3, 1, 3, 3, 3, 5]
def baseStart_3282200 : Nat := 118140960795 + 3282200 * 2 ^ 59
def prefixEnd_3282200 : Nat := 4983230072969 + 3 ^ 40 * 3282200 * 2
def baseEnd_3282200 : Nat := 187260689354129290122827

theorem tailTrace_3282200 : CollatzResearch.WordTrace tailWord_3282200 prefixEnd_3282200 187260689354129290122827 := by
  unfold tailWord_3282200
  simp only [CollatzResearch.WordTrace]
  refine ⟨59855834354578714988518027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79807779139438286651357369 59855834354578714988518027)
  ·
    refine ⟨89783751531868072482777041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59855834354578714988518027 89783751531868072482777041)
    ·
      refine ⟨67337813648901054362082781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89783751531868072482777041 67337813648901054362082781)
      ·
        refine ⟨25251680118337895385781043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67337813648901054362082781 25251680118337895385781043)
        ·
          refine ⟨37877520177506843078671565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25251680118337895385781043 37877520177506843078671565)
          ·
            refine ⟨14204070066565066154501837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37877520177506843078671565 14204070066565066154501837)
            ·
              refine ⟨5326526274961899807938189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14204070066565066154501837 5326526274961899807938189)
              ·
                refine ⟨1997447353110712427976821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5326526274961899807938189 1997447353110712427976821)
                ·
                  refine ⟨187260689354129290122827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997447353110712427976821 187260689354129290122827)
                  ·
                    rfl

theorem cell23_3282200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 5].length) (baseStart_3282200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282200 prefixEnd_3282200 := by exact prefixLift 3282200
  have htrace : WordTrace (prefixWord ++ tailWord_3282200) baseStart_3282200 baseEnd_3282200 := by
    simpa [prefixWord, tailWord_3282200, baseEnd_3282200] using wordTrace_append hprefix tailTrace_3282200
  have hstable : (prefixWord ++ tailWord_3282200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282200).length < 2 ^ (prefixWord ++ tailWord_3282200).sum := by decide
  have hdescent : baseEnd_3282200 < baseStart_3282200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282203 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 7, 2]
def baseStart_3282203 : Nat := 118140960795 + 3282203 * 2 ^ 59
def prefixEnd_3282203 : Nat := 4983230072969 + 3 ^ 40 * 3282203 * 2
def baseEnd_3282203 : Nat := 1685347744629127099367929

theorem tailTrace_3282203 : CollatzResearch.WordTrace tailWord_3282203 prefixEnd_3282203 1685347744629127099367929 := by
  unfold tailWord_3282203
  simp only [CollatzResearch.WordTrace]
  refine ⟨119711778128146561489395263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79807852085431040992930175 119711778128146561489395263)
  ·
    refine ⟨179567667192219842234092895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119711778128146561489395263 179567667192219842234092895)
    ·
      refine ⟨269351500788329763351139343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179567667192219842234092895 269351500788329763351139343)
      ·
        refine ⟨404027251182494645026709015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269351500788329763351139343 404027251182494645026709015)
        ·
          refine ⟨606040876773741967540063523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404027251182494645026709015 606040876773741967540063523)
          ·
            refine ⟨909061315160612951310095285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606040876773741967540063523 909061315160612951310095285)
            ·
              refine ⟨85224498296307464185321433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 909061315160612951310095285 85224498296307464185321433)
              ·
                refine ⟨63918373722230598138991075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85224498296307464185321433 63918373722230598138991075)
                ·
                  refine ⟨95877560583345897208486613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63918373722230598138991075 95877560583345897208486613)
                  ·
                    refine ⟨2247130326172169465823905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95877560583345897208486613 2247130326172169465823905)
                    ·
                      refine ⟨1685347744629127099367929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247130326172169465823905 1685347744629127099367929)
                      ·
                        rfl

theorem cell23_3282203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7, 2].length) (baseStart_3282203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282203 prefixEnd_3282203 := by exact prefixLift 3282203
  have htrace : WordTrace (prefixWord ++ tailWord_3282203) baseStart_3282203 baseEnd_3282203 := by
    simpa [prefixWord, tailWord_3282203, baseEnd_3282203] using wordTrace_append hprefix tailTrace_3282203
  have hstable : (prefixWord ++ tailWord_3282203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282203).length < 2 ^ (prefixWord ++ tailWord_3282203).sum := by decide
  have hdescent : baseEnd_3282203 < baseStart_3282203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282213 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_3282213 : Nat := 118140960795 + 3282213 * 2 ^ 59
def prefixEnd_3282213 : Nat := 4983230072969 + 3 ^ 40 * 3282213 * 2
def baseEnd_3282213 : Nat := 561784293145224020080961

theorem tailTrace_3282213 : CollatzResearch.WordTrace tailWord_3282213 prefixEnd_3282213 561784293145224020080961 := by
  unfold tailWord_3282213
  simp only [CollatzResearch.WordTrace]
  refine ⟨119712142858110333197259293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79808095238740222131506195 119712142858110333197259293)
  ·
    refine ⟨44892053571791374948972235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119712142858110333197259293 44892053571791374948972235)
    ·
      refine ⟨67338080357687062423458353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44892053571791374948972235 67338080357687062423458353)
      ·
        refine ⟨50503560268265296817593765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67338080357687062423458353 50503560268265296817593765)
        ·
          refine ⟨9469417550299743153298831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50503560268265296817593765 9469417550299743153298831)
          ·
            refine ⟨14204126325449614729948247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9469417550299743153298831 14204126325449614729948247)
            ·
              refine ⟨21306189488174422094922371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14204126325449614729948247 21306189488174422094922371)
              ·
                refine ⟨31959284232261633142383557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21306189488174422094922371 31959284232261633142383557)
                ·
                  refine ⟨5992365793549056214196917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31959284232261633142383557 5992365793549056214196917)
                  ·
                    refine ⟨561784293145224020080961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5992365793549056214196917 561784293145224020080961)
                    ·
                      rfl

theorem cell23_3282213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_3282213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282213 prefixEnd_3282213 := by exact prefixLift 3282213
  have htrace : WordTrace (prefixWord ++ tailWord_3282213) baseStart_3282213 baseEnd_3282213 := by
    simpa [prefixWord, tailWord_3282213, baseEnd_3282213] using wordTrace_append hprefix tailTrace_3282213
  have hstable : (prefixWord ++ tailWord_3282213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282213).length < 2 ^ (prefixWord ++ tailWord_3282213).sum := by decide
  have hdescent : baseEnd_3282213 < baseStart_3282213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282243 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 5, 4]
def baseStart_3282243 : Nat := 118140960795 + 3282243 * 2 ^ 59
def prefixEnd_3282243 : Nat := 4983230072969 + 3 ^ 40 * 3282243 * 2
def baseEnd_3282243 : Nat := 561789427951768980955915

theorem tailTrace_3282243 : CollatzResearch.WordTrace tailWord_3282243 prefixEnd_3282243 561789427951768980955915 := by
  unfold tailWord_3282243
  simp only [CollatzResearch.WordTrace]
  refine ⟨119713237048001648320851383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79808824698667765547234255 119713237048001648320851383)
  ·
    refine ⟨179569855572002472481277075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119713237048001648320851383 179569855572002472481277075)
    ·
      refine ⟨269354783358003708721915613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179569855572002472481277075 269354783358003708721915613)
      ·
        refine ⟨101008043759251390770718355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269354783358003708721915613 101008043759251390770718355)
        ·
          refine ⟨151512065638877086156077533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101008043759251390770718355 151512065638877086156077533)
          ·
            refine ⟨56817024614578907308529075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151512065638877086156077533 56817024614578907308529075)
            ·
              refine ⟨85225536921868360962793613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56817024614578907308529075 85225536921868360962793613)
              ·
                refine ⟨31959576345700635361047605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85225536921868360962793613 31959576345700635361047605)
                ·
                  refine ⟨2996210282409434565098213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31959576345700635361047605 2996210282409434565098213)
                  ·
                    refine ⟨561789427951768980955915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2996210282409434565098213 561789427951768980955915)
                    ·
                      rfl

theorem cell23_3282243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 4].length) (baseStart_3282243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282243 prefixEnd_3282243 := by exact prefixLift 3282243
  have htrace : WordTrace (prefixWord ++ tailWord_3282243) baseStart_3282243 baseEnd_3282243 := by
    simpa [prefixWord, tailWord_3282243, baseEnd_3282243] using wordTrace_append hprefix tailTrace_3282243
  have hstable : (prefixWord ++ tailWord_3282243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282243).length < 2 ^ (prefixWord ++ tailWord_3282243).sum := by decide
  have hdescent : baseEnd_3282243 < baseStart_3282243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282277 : List Nat := [1, 3, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_3282277 : Nat := 118140960795 + 3282277 * 2 ^ 59
def prefixEnd_3282277 : Nat := 4983230072969 + 3 ^ 40 * 3282277 * 2
def baseEnd_3282277 : Nat := 561795247399186603280863

theorem tailTrace_3282277 : CollatzResearch.WordTrace tailWord_3282277 prefixEnd_3282277 561795247399186603280863 := by
  unfold tailWord_3282277
  simp only [CollatzResearch.WordTrace]
  refine ⟨119714477129878472127589085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79809651419918981418392723 119714477129878472127589085)
  ·
    refine ⟨44892928923704427047845907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119714477129878472127589085 44892928923704427047845907)
    ·
      refine ⟨67339393385556640571768861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44892928923704427047845907 67339393385556640571768861)
      ·
        refine ⟨25252272519583740214413323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67339393385556640571768861 25252272519583740214413323)
        ·
          refine ⟨37878408779375610321619985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25252272519583740214413323 37878408779375610321619985)
          ·
            refine ⟨28408806584531707741214989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37878408779375610321619985 28408806584531707741214989)
            ·
              refine ⟨10653302469199390402955621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28408806584531707741214989 10653302469199390402955621)
              ·
                refine ⟨1997494212974885700554179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10653302469199390402955621 1997494212974885700554179)
                ·
                  refine ⟨2996241319462328550831269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997494212974885700554179 2996241319462328550831269)
                  ·
                    refine ⟨561795247399186603280863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2996241319462328550831269 561795247399186603280863)
                    ·
                      rfl

theorem cell23_3282277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_3282277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282277 prefixEnd_3282277 := by exact prefixLift 3282277
  have htrace : WordTrace (prefixWord ++ tailWord_3282277) baseStart_3282277 baseEnd_3282277 := by
    simpa [prefixWord, tailWord_3282277, baseEnd_3282277] using wordTrace_append hprefix tailTrace_3282277
  have hstable : (prefixWord ++ tailWord_3282277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282277).length < 2 ^ (prefixWord ++ tailWord_3282277).sum := by decide
  have hdescent : baseEnd_3282277 < baseStart_3282277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282357 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3282357 : Nat := 118140960795 + 3282357 * 2 ^ 59
def prefixEnd_3282357 : Nat := 4983230072969 + 3 ^ 40 * 3282357 * 2
def baseEnd_3282357 : Nat := 1685426820649919496842221

theorem tailTrace_3282357 : CollatzResearch.WordTrace tailWord_3282357 prefixEnd_3282357 1685426820649919496842221 := by
  unfold tailWord_3282357
  simp only [CollatzResearch.WordTrace]
  refine ⟨119717394969588645790501325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79811596646392430527000883 119717394969588645790501325)
  ·
    refine ⟨44894023113595742171437997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119717394969588645790501325 44894023113595742171437997)
    ·
      refine ⟨16835258667598403314289249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44894023113595742171437997 16835258667598403314289249)
      ·
        refine ⟨12626444000698802485716937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16835258667598403314289249 12626444000698802485716937)
        ·
          refine ⟨9469833000524101864287703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12626444000698802485716937 9469833000524101864287703)
          ·
            refine ⟨14204749500786152796431555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9469833000524101864287703 14204749500786152796431555)
            ·
              refine ⟨21307124251179229194647333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14204749500786152796431555 21307124251179229194647333)
              ·
                refine ⟨3995085797096105473996375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21307124251179229194647333 3995085797096105473996375)
                ·
                  refine ⟨5992628695644158210994563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995085797096105473996375 5992628695644158210994563)
                  ·
                    refine ⟨8988943043466237316491845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5992628695644158210994563 8988943043466237316491845)
                    ·
                      refine ⟨1685426820649919496842221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8988943043466237316491845 1685426820649919496842221)
                      ·
                        rfl

theorem cell23_3282357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3282357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282357 prefixEnd_3282357 := by exact prefixLift 3282357
  have htrace : WordTrace (prefixWord ++ tailWord_3282357) baseStart_3282357 baseEnd_3282357 := by
    simpa [prefixWord, tailWord_3282357, baseEnd_3282357] using wordTrace_append hprefix tailTrace_3282357
  have hstable : (prefixWord ++ tailWord_3282357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282357).length < 2 ^ (prefixWord ++ tailWord_3282357).sum := by decide
  have hdescent : baseEnd_3282357 < baseStart_3282357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282360 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_3282360 : Nat := 118140960795 + 3282360 * 2 ^ 59
def prefixEnd_3282360 : Nat := 4983230072969 + 3 ^ 40 * 3282360 * 2
def baseEnd_3282360 : Nat := 1685428361091882985104707

theorem tailTrace_3282360 : CollatzResearch.WordTrace tailWord_3282360 prefixEnd_3282360 1685428361091882985104707 := by
  unfold tailWord_3282360
  simp only [CollatzResearch.WordTrace]
  refine ⟨59858752194288888651430267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79811669592385184868573689 59858752194288888651430267)
  ·
    refine ⟨89788128291433332977145401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59858752194288888651430267 89788128291433332977145401)
    ·
      refine ⟨67341096218574999732859051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89788128291433332977145401 67341096218574999732859051)
      ·
        refine ⟨101011644327862499599288577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67341096218574999732859051 101011644327862499599288577)
        ·
          refine ⟨75758733245896874699466433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101011644327862499599288577 75758733245896874699466433)
          ·
            refine ⟨56819049934422656024599825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75758733245896874699466433 56819049934422656024599825)
            ·
              refine ⟨42614287450816992018449869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56819049934422656024599825 42614287450816992018449869)
              ·
                refine ⟨15980357794056372006918701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42614287450816992018449869 15980357794056372006918701)
                ·
                  refine ⟨5992634172771139502594513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15980357794056372006918701 5992634172771139502594513)
                  ·
                    refine ⟨4494475629578354626945885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5992634172771139502594513 4494475629578354626945885)
                    ·
                      refine ⟨1685428361091882985104707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4494475629578354626945885 1685428361091882985104707)
                      ·
                        rfl

theorem cell23_3282360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_3282360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282360 prefixEnd_3282360 := by exact prefixLift 3282360
  have htrace : WordTrace (prefixWord ++ tailWord_3282360) baseStart_3282360 baseEnd_3282360 := by
    simpa [prefixWord, tailWord_3282360, baseEnd_3282360] using wordTrace_append hprefix tailTrace_3282360
  have hstable : (prefixWord ++ tailWord_3282360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282360).length < 2 ^ (prefixWord ++ tailWord_3282360).sum := by decide
  have hdescent : baseEnd_3282360 < baseStart_3282360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282380 : List Nat := [2, 2, 1, 4, 2, 3, 9]
def baseStart_3282380 : Nat := 118140960795 + 3282380 * 2 ^ 59
def prefixEnd_3282380 : Nat := 4983230072969 + 3 ^ 40 * 3282380 * 2
def baseEnd_3282380 : Nat := 20807884329691023541415

theorem tailTrace_3282380 : CollatzResearch.WordTrace tailWord_3282380 prefixEnd_3282380 20807884329691023541415 := by
  unfold tailWord_3282380
  simp only [CollatzResearch.WordTrace]
  refine ⟨59859116924252660359294297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79812155899003547145725729 59859116924252660359294297)
  ·
    refine ⟨44894337693189495269470723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59859116924252660359294297 44894337693189495269470723)
    ·
      refine ⟨67341506539784242904206085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44894337693189495269470723 67341506539784242904206085)
      ·
        refine ⟨12626532476209545544538641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67341506539784242904206085 12626532476209545544538641)
        ·
          refine ⟨9469899357157159158403981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12626532476209545544538641 9469899357157159158403981)
          ·
            refine ⟨3551212258933934684401493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9469899357157159158403981 3551212258933934684401493)
            ·
              refine ⟨20807884329691023541415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3551212258933934684401493 20807884329691023541415)
              ·
                rfl

theorem cell23_3282380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 9].length) (baseStart_3282380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282380 prefixEnd_3282380 := by exact prefixLift 3282380
  have htrace : WordTrace (prefixWord ++ tailWord_3282380) baseStart_3282380 baseEnd_3282380 := by
    simpa [prefixWord, tailWord_3282380, baseEnd_3282380] using wordTrace_append hprefix tailTrace_3282380
  have hstable : (prefixWord ++ tailWord_3282380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282380).length < 2 ^ (prefixWord ++ tailWord_3282380).sum := by decide
  have hdescent : baseEnd_3282380 < baseStart_3282380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282423 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 3, 8]
def baseStart_3282423 : Nat := 118140960795 + 3282423 * 2 ^ 59
def prefixEnd_3282423 : Nat := 4983230072969 + 3 ^ 40 * 3282423 * 2
def baseEnd_3282423 : Nat := 561820236791038746205639

theorem tailTrace_3282423 : CollatzResearch.WordTrace tailWord_3282423 prefixEnd_3282423 561820236791038746205639 := by
  unfold tailWord_3282423
  simp only [CollatzResearch.WordTrace]
  refine ⟨119719802187349539062403923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79813201458233026041602615 119719802187349539062403923)
  ·
    refine ⟨179579703281024308593605885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119719802187349539062403923 179579703281024308593605885)
    ·
      refine ⟨67342388730384115722602207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179579703281024308593605885 67342388730384115722602207)
      ·
        refine ⟨101013583095576173583903311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67342388730384115722602207 101013583095576173583903311)
        ·
          refine ⟨151520374643364260375854967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101013583095576173583903311 151520374643364260375854967)
          ·
            refine ⟨227280561965046390563782451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151520374643364260375854967 227280561965046390563782451)
            ·
              refine ⟨340920842947569585845673677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227280561965046390563782451 340920842947569585845673677)
              ·
                refine ⟨127845316105338594692127629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340920842947569585845673677 127845316105338594692127629)
                ·
                  refine ⟨47941993539501973009547861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127845316105338594692127629 47941993539501973009547861)
                  ·
                    refine ⟨561820236791038746205639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47941993539501973009547861 561820236791038746205639)
                    ·
                      rfl

theorem cell23_3282423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_3282423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282423 prefixEnd_3282423 := by exact prefixLift 3282423
  have htrace : WordTrace (prefixWord ++ tailWord_3282423) baseStart_3282423 baseEnd_3282423 := by
    simpa [prefixWord, tailWord_3282423, baseEnd_3282423] using wordTrace_append hprefix tailTrace_3282423
  have hstable : (prefixWord ++ tailWord_3282423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282423).length < 2 ^ (prefixWord ++ tailWord_3282423).sum := by decide
  have hdescent : baseEnd_3282423 < baseStart_3282423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282464 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3282464 : Nat := 118140960795 + 3282464 * 2 ^ 59
def prefixEnd_3282464 : Nat := 4983230072969 + 3 ^ 40 * 3282464 * 2
def baseEnd_3282464 : Nat := 1685481763079950578204229

theorem tailTrace_3282464 : CollatzResearch.WordTrace tailWord_3282464 prefixEnd_3282464 1685481763079950578204229 := by
  unfold tailWord_3282464
  simp only [CollatzResearch.WordTrace]
  refine ⟨59860648790100501532323223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79814198386800668709764297 59860648790100501532323223)
  ·
    refine ⟨89790973185150752298484835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59860648790100501532323223 89790973185150752298484835)
    ·
      refine ⟨134686459777726128447727253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89790973185150752298484835 134686459777726128447727253)
      ·
        refine ⟨6313427802080912270987215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134686459777726128447727253 6313427802080912270987215)
        ·
          refine ⟨9470141703121368406480823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6313427802080912270987215 9470141703121368406480823)
          ·
            refine ⟨14205212554682052609721235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9470141703121368406480823 14205212554682052609721235)
            ·
              refine ⟨21307818832023078914581853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14205212554682052609721235 21307818832023078914581853)
              ·
                refine ⟨7990432062008654592968195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21307818832023078914581853 7990432062008654592968195)
                ·
                  refine ⟨11985648093012981889452293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7990432062008654592968195 11985648093012981889452293)
                  ·
                    refine ⟨2247309017439934104272305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11985648093012981889452293 2247309017439934104272305)
                    ·
                      refine ⟨1685481763079950578204229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247309017439934104272305 1685481763079950578204229)
                      ·
                        rfl

theorem cell23_3282464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3282464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282464 prefixEnd_3282464 := by exact prefixLift 3282464
  have htrace : WordTrace (prefixWord ++ tailWord_3282464) baseStart_3282464 baseEnd_3282464 := by
    simpa [prefixWord, tailWord_3282464, baseEnd_3282464] using wordTrace_append hprefix tailTrace_3282464
  have hstable : (prefixWord ++ tailWord_3282464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282464).length < 2 ^ (prefixWord ++ tailWord_3282464).sum := by decide
  have hdescent : baseEnd_3282464 < baseStart_3282464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282480 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3]
def baseStart_3282480 : Nat := 118140960795 + 3282480 * 2 ^ 59
def prefixEnd_3282480 : Nat := 4983230072969 + 3 ^ 40 * 3282480 * 2
def baseEnd_3282480 : Nat := 1685489978770422515604155

theorem tailTrace_3282480 : CollatzResearch.WordTrace tailWord_3282480 prefixEnd_3282480 1685489978770422515604155 := by
  unfold tailWord_3282480
  simp only [CollatzResearch.WordTrace]
  refine ⟨59860940574071518898614447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79814587432095358531485929 59860940574071518898614447)
  ·
    refine ⟨89791410861107278347921671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59860940574071518898614447 89791410861107278347921671)
    ·
      refine ⟨134687116291660917521882507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89791410861107278347921671 134687116291660917521882507)
      ·
        refine ⟨202030674437491376282823761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134687116291660917521882507 202030674437491376282823761)
        ·
          refine ⟨151523005828118532212117821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202030674437491376282823761 151523005828118532212117821)
          ·
            refine ⟨56821127185544449579544183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151523005828118532212117821 56821127185544449579544183)
            ·
              refine ⟨85231690778316674369316275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56821127185544449579544183 85231690778316674369316275)
              ·
                refine ⟨127847536167475011553974413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85231690778316674369316275 127847536167475011553974413)
                ·
                  refine ⟨47942826062803129332740405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127847536167475011553974413 47942826062803129332740405)
                  ·
                    refine ⟨4494639943387793374944413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47942826062803129332740405 4494639943387793374944413)
                    ·
                      refine ⟨1685489978770422515604155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4494639943387793374944413 1685489978770422515604155)
                      ·
                        rfl

theorem cell23_3282480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_3282480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282480 prefixEnd_3282480 := by exact prefixLift 3282480
  have htrace : WordTrace (prefixWord ++ tailWord_3282480) baseStart_3282480 baseEnd_3282480 := by
    simpa [prefixWord, tailWord_3282480, baseEnd_3282480] using wordTrace_append hprefix tailTrace_3282480
  have hstable : (prefixWord ++ tailWord_3282480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282480).length < 2 ^ (prefixWord ++ tailWord_3282480).sum := by decide
  have hdescent : baseEnd_3282480 < baseStart_3282480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282487 : List Nat := [1, 1, 3, 1, 2, 4, 1, 5, 5]
def baseStart_3282487 : Nat := 118140960795 + 3282487 * 2 ^ 59
def prefixEnd_3282487 : Nat := 4983230072969 + 3 ^ 40 * 3282487 * 2
def baseEnd_3282487 : Nat := 187277063681667109801847

theorem tailTrace_3282487 : CollatzResearch.WordTrace tailWord_3282487 prefixEnd_3282487 187277063681667109801847 := by
  unfold tailWord_3282487
  simp only [CollatzResearch.WordTrace]
  refine ⟨119722136459117677992733715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79814757639411785328489143 119722136459117677992733715)
  ·
    refine ⟨179583204688676516989100573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119722136459117677992733715 179583204688676516989100573)
    ·
      refine ⟨67343701758253693870912715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179583204688676516989100573 67343701758253693870912715)
      ·
        refine ⟨101015552637380540806369073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67343701758253693870912715 101015552637380540806369073)
        ·
          refine ⟨75761664478035405604776805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101015552637380540806369073 75761664478035405604776805)
          ·
            refine ⟨14205312089631638550895651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75761664478035405604776805 14205312089631638550895651)
            ·
              refine ⟨21307968134447457826343477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14205312089631638550895651 21307968134447457826343477)
              ·
                refine ⟨1997622012604449171219701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21307968134447457826343477 1997622012604449171219701)
                ·
                  refine ⟨187277063681667109801847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997622012604449171219701 187277063681667109801847)
                  ·
                    rfl

theorem cell23_3282487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 5].length) (baseStart_3282487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282487 prefixEnd_3282487 := by exact prefixLift 3282487
  have htrace : WordTrace (prefixWord ++ tailWord_3282487) baseStart_3282487 baseEnd_3282487 := by
    simpa [prefixWord, tailWord_3282487, baseEnd_3282487] using wordTrace_append hprefix tailTrace_3282487
  have hstable : (prefixWord ++ tailWord_3282487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282487).length < 2 ^ (prefixWord ++ tailWord_3282487).sum := by decide
  have hdescent : baseEnd_3282487 < baseStart_3282487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282497 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3282497 : Nat := 118140960795 + 3282497 * 2 ^ 59
def prefixEnd_3282497 : Nat := 4983230072969 + 3 ^ 40 * 3282497 * 2
def baseEnd_3282497 : Nat := 1685498707941548949091577

theorem tailTrace_3282497 : CollatzResearch.WordTrace tailWord_3282497 prefixEnd_3282497 1685498707941548949091577 := by
  unfold tailWord_3282497
  simp only [CollatzResearch.WordTrace]
  refine ⟨119722501189081449700597745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79815000792720966467065163 119722501189081449700597745)
  ·
    refine ⟨89791875891811087275448309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119722501189081449700597745 89791875891811087275448309)
    ·
      refine ⟨8417988364857289432073279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89791875891811087275448309 8417988364857289432073279)
      ·
        refine ⟨12626982547285934148109919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8417988364857289432073279 12626982547285934148109919)
        ·
          refine ⟨18940473820928901222164879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12626982547285934148109919 18940473820928901222164879)
          ·
            refine ⟨28410710731393351833247319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18940473820928901222164879 28410710731393351833247319)
            ·
              refine ⟨42616066097090027749870979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28410710731393351833247319 42616066097090027749870979)
              ·
                refine ⟨63924099145635041624806469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42616066097090027749870979 63924099145635041624806469)
                ·
                  refine ⟨11985768589806570304651213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63924099145635041624806469 11985768589806570304651213)
                  ·
                    refine ⟨4494663221177463864244205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11985768589806570304651213 4494663221177463864244205)
                    ·
                      refine ⟨1685498707941548949091577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4494663221177463864244205 1685498707941548949091577)
                      ·
                        rfl

theorem cell23_3282497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3282497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282497 prefixEnd_3282497 := by exact prefixLift 3282497
  have htrace : WordTrace (prefixWord ++ tailWord_3282497) baseStart_3282497 baseEnd_3282497 := by
    simpa [prefixWord, tailWord_3282497, baseEnd_3282497] using wordTrace_append hprefix tailTrace_3282497
  have hstable : (prefixWord ++ tailWord_3282497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282497).length < 2 ^ (prefixWord ++ tailWord_3282497).sum := by decide
  have hdescent : baseEnd_3282497 < baseStart_3282497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282510 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3282510 : Nat := 118140960795 + 3282510 * 2 ^ 59
def prefixEnd_3282510 : Nat := 4983230072969 + 3 ^ 40 * 3282510 * 2
def baseEnd_3282510 : Nat := 1685505383190057398229017

theorem tailTrace_3282510 : CollatzResearch.WordTrace tailWord_3282510 prefixEnd_3282510 1685505383190057398229017 := by
  unfold tailWord_3282510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14965371917254294115102623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79815316892022901947213989 14965371917254294115102623)
  ·
    refine ⟨22448057875881441172653935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14965371917254294115102623 22448057875881441172653935)
    ·
      refine ⟨33672086813822161758980903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22448057875881441172653935 33672086813822161758980903)
      ·
        refine ⟨50508130220733242638471355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33672086813822161758980903 50508130220733242638471355)
        ·
          refine ⟨75762195331099863957707033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50508130220733242638471355 75762195331099863957707033)
          ·
            refine ⟨56821646498324897968280275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75762195331099863957707033 56821646498324897968280275)
            ·
              refine ⟨85232469747487346952420413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56821646498324897968280275 85232469747487346952420413)
              ·
                refine ⟨31962176155307755107157655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85232469747487346952420413 31962176155307755107157655)
                ·
                  refine ⟨47943264232961632660736483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31962176155307755107157655 47943264232961632660736483)
                  ·
                    refine ⟨71914896349442448991104725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47943264232961632660736483 71914896349442448991104725)
                    ·
                      refine ⟨1685505383190057398229017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71914896349442448991104725 1685505383190057398229017)
                      ·
                        rfl

theorem cell23_3282510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3282510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282510 prefixEnd_3282510 := by exact prefixLift 3282510
  have htrace : WordTrace (prefixWord ++ tailWord_3282510) baseStart_3282510 baseEnd_3282510 := by
    simpa [prefixWord, tailWord_3282510, baseEnd_3282510] using wordTrace_append hprefix tailTrace_3282510
  have hstable : (prefixWord ++ tailWord_3282510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282510).length < 2 ^ (prefixWord ++ tailWord_3282510).sum := by decide
  have hdescent : baseEnd_3282510 < baseStart_3282510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282537 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 1, 6, 2]
def baseStart_3282537 : Nat := 118140960795 + 3282537 * 2 ^ 59
def prefixEnd_3282537 : Nat := 4983230072969 + 3 ^ 40 * 3282537 * 2
def baseEnd_3282537 : Nat := 1685519247167728792591393

theorem tailTrace_3282537 : CollatzResearch.WordTrace tailWord_3282537 prefixEnd_3282537 1685519247167728792591393 := by
  unfold tailWord_3282537
  simp only [CollatzResearch.WordTrace]
  refine ⟨119723960108936536532053865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79815973405957691021369243 119723960108936536532053865)
  ·
    refine ⟨89792970081702402399040399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119723960108936536532053865 89792970081702402399040399)
    ·
      refine ⟨134689455122553603598560599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89792970081702402399040399 134689455122553603598560599)
      ·
        refine ⟨202034182683830405397840899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134689455122553603598560599 202034182683830405397840899)
        ·
          refine ⟨303051274025745608096761349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202034182683830405397840899 303051274025745608096761349)
          ·
            refine ⟨56822113879827301518142753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303051274025745608096761349 56822113879827301518142753)
            ·
              refine ⟨42616585409870476138607065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56822113879827301518142753 42616585409870476138607065)
              ·
                refine ⟨31962439057402857103955299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42616585409870476138607065 31962439057402857103955299)
                ·
                  refine ⟨47943658586104285655932949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31962439057402857103955299 47943658586104285655932949)
                  ·
                    refine ⟨2247358996223638390121857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47943658586104285655932949 2247358996223638390121857)
                    ·
                      refine ⟨1685519247167728792591393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247358996223638390121857 1685519247167728792591393)
                      ·
                        rfl

theorem cell23_3282537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 6, 2].length) (baseStart_3282537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282537 prefixEnd_3282537 := by exact prefixLift 3282537
  have htrace : WordTrace (prefixWord ++ tailWord_3282537) baseStart_3282537 baseEnd_3282537 := by
    simpa [prefixWord, tailWord_3282537, baseEnd_3282537] using wordTrace_append hprefix tailTrace_3282537
  have hstable : (prefixWord ++ tailWord_3282537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282537).length < 2 ^ (prefixWord ++ tailWord_3282537).sum := by decide
  have hdescent : baseEnd_3282537 < baseStart_3282537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282540 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3282540 : Nat := 118140960795 + 3282540 * 2 ^ 59
def prefixEnd_3282540 : Nat := 4983230072969 + 3 ^ 40 * 3282540 * 2
def baseEnd_3282540 : Nat := 1685520787609692280853879

theorem tailTrace_3282540 : CollatzResearch.WordTrace tailWord_3282540 prefixEnd_3282540 1685520787609692280853879 := by
  unfold tailWord_3282540
  simp only [CollatzResearch.WordTrace]
  refine ⟨59862034763962834022206537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79816046351950445362942049 59862034763962834022206537)
  ·
    refine ⟨44896526072972125516654903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59862034763962834022206537 44896526072972125516654903)
    ·
      refine ⟨67344789109458188274982355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44896526072972125516654903 67344789109458188274982355)
      ·
        refine ⟨101017183664187282412473533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67344789109458188274982355 101017183664187282412473533)
        ·
          refine ⟨37881443874070230904677575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101017183664187282412473533 37881443874070230904677575)
          ·
            refine ⟨56822165811105346357016363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37881443874070230904677575 56822165811105346357016363)
            ·
              refine ⟨85233248716658019535524545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56822165811105346357016363 85233248716658019535524545)
              ·
                refine ⟨63924936537493514651643409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85233248716658019535524545 63924936537493514651643409)
                ·
                  refine ⟨47943702403120135988732557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63924936537493514651643409 47943702403120135988732557)
                  ·
                    refine ⟨17978888401170050995774709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47943702403120135988732557 17978888401170050995774709)
                    ·
                      refine ⟨1685520787609692280853879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17978888401170050995774709 1685520787609692280853879)
                      ·
                        rfl

theorem cell23_3282540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3282540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282540 prefixEnd_3282540 := by exact prefixLift 3282540
  have htrace : WordTrace (prefixWord ++ tailWord_3282540) baseStart_3282540 baseEnd_3282540 := by
    simpa [prefixWord, tailWord_3282540, baseEnd_3282540] using wordTrace_append hprefix tailTrace_3282540
  have hstable : (prefixWord ++ tailWord_3282540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282540).length < 2 ^ (prefixWord ++ tailWord_3282540).sum := by decide
  have hdescent : baseEnd_3282540 < baseStart_3282540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282560 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 8]
def baseStart_3282560 : Nat := 118140960795 + 3282560 * 2 ^ 59
def prefixEnd_3282560 : Nat := 4983230072969 + 3 ^ 40 * 3282560 * 2
def baseEnd_3282560 : Nat := 187281228580309133622643

theorem tailTrace_3282560 : CollatzResearch.WordTrace tailWord_3282560 prefixEnd_3282560 187281228580309133622643 := by
  unfold tailWord_3282560
  simp only [CollatzResearch.WordTrace]
  refine ⟨59862399493926605730070567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79816532658568807640094089 59862399493926605730070567)
  ·
    refine ⟨89793599240889908595105851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59862399493926605730070567 89793599240889908595105851)
    ·
      refine ⟨134690398861334862892658777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89793599240889908595105851 134690398861334862892658777)
      ·
        refine ⟨101017799146001147169494083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134690398861334862892658777 101017799146001147169494083)
        ·
          refine ⟨151526698719001720754241125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101017799146001147169494083 151526698719001720754241125)
          ·
            refine ⟨28411256009812822641420211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151526698719001720754241125 28411256009812822641420211)
            ·
              refine ⟨42616884014719233962130317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28411256009812822641420211 42616884014719233962130317)
              ·
                refine ⟨15981331505519712735798869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42616884014719233962130317 15981331505519712735798869)
                ·
                  refine ⟨187281228580309133622643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15981331505519712735798869 187281228580309133622643)
                  ·
                    rfl

theorem cell23_3282560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_3282560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282560 prefixEnd_3282560 := by exact prefixLift 3282560
  have htrace : WordTrace (prefixWord ++ tailWord_3282560) baseStart_3282560 baseEnd_3282560 := by
    simpa [prefixWord, tailWord_3282560, baseEnd_3282560] using wordTrace_append hprefix tailTrace_3282560
  have hstable : (prefixWord ++ tailWord_3282560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282560).length < 2 ^ (prefixWord ++ tailWord_3282560).sum := by decide
  have hdescent : baseEnd_3282560 < baseStart_3282560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282661 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 5, 2, 2]
def baseStart_3282661 : Nat := 118140960795 + 3282661 * 2 ^ 59
def prefixEnd_3282661 : Nat := 4983230072969 + 3 ^ 40 * 3282661 * 2
def baseEnd_3282661 : Nat := 1685582918768886307440823

theorem tailTrace_3282661 : CollatzResearch.WordTrace tailWord_3282661 prefixEnd_3282661 1685582918768886307440823 := by
  unfold tailWord_3282661
  simp only [CollatzResearch.WordTrace]
  refine ⟨119728482760487305709567837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79818988506991537139711891 119728482760487305709567837)
  ·
    refine ⟨44898181035182739641087939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119728482760487305709567837 44898181035182739641087939)
    ·
      refine ⟨67347271552774109461631909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44898181035182739641087939 67347271552774109461631909)
      ·
        refine ⟨12627613416145145524055983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67347271552774109461631909 12627613416145145524055983)
        ·
          refine ⟨18941420124217718286083975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12627613416145145524055983 18941420124217718286083975)
          ·
            refine ⟨28412130186326577429125963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18941420124217718286083975 28412130186326577429125963)
            ·
              refine ⟨42618195279489866143688945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28412130186326577429125963 42618195279489866143688945)
              ·
                refine ⟨31963646459617399607766709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42618195279489866143688945 31963646459617399607766709)
                ·
                  refine ⟨2996591855589131213228129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31963646459617399607766709 2996591855589131213228129)
                  ·
                    refine ⟨2247443891691848409921097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2996591855589131213228129 2247443891691848409921097)
                    ·
                      refine ⟨1685582918768886307440823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247443891691848409921097 1685582918768886307440823)
                      ·
                        rfl

theorem cell23_3282661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_3282661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282661 prefixEnd_3282661 := by exact prefixLift 3282661
  have htrace : WordTrace (prefixWord ++ tailWord_3282661) baseStart_3282661 baseEnd_3282661 := by
    simpa [prefixWord, tailWord_3282661, baseEnd_3282661] using wordTrace_append hprefix tailTrace_3282661
  have hstable : (prefixWord ++ tailWord_3282661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282661).length < 2 ^ (prefixWord ++ tailWord_3282661).sum := by decide
  have hdescent : baseEnd_3282661 < baseStart_3282661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282678 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_3282678 : Nat := 118140960795 + 3282678 * 2 ^ 59
def prefixEnd_3282678 : Nat := 4983230072969 + 3 ^ 40 * 3282678 * 2
def baseEnd_3282678 : Nat := 1685591647940012740928245

theorem tailTrace_3282678 : CollatzResearch.WordTrace tailWord_3282678 prefixEnd_3282678 1685591647940012740928245 := by
  unfold tailWord_3282678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483068925089107350808543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79819401867617145075291125 7483068925089107350808543)
  ·
    refine ⟨11224603387633661026212815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7483068925089107350808543 11224603387633661026212815)
    ·
      refine ⟨16836905081450491539319223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11224603387633661026212815 16836905081450491539319223)
      ·
        refine ⟨25255357622175737308978835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16836905081450491539319223 25255357622175737308978835)
        ·
          refine ⟨37883036433263605963468253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25255357622175737308978835 37883036433263605963468253)
          ·
            refine ⟨14206138662473852236300595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37883036433263605963468253 14206138662473852236300595)
            ·
              refine ⟨21309207993710778354450893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14206138662473852236300595 21309207993710778354450893)
              ·
                refine ⟨7990952997641541882919085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21309207993710778354450893 7990952997641541882919085)
                ·
                  refine ⟨2996607374115578206094657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7990952997641541882919085 2996607374115578206094657)
                  ·
                    refine ⟨2247455530586683654570993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2996607374115578206094657 2247455530586683654570993)
                    ·
                      refine ⟨1685591647940012740928245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247455530586683654570993 1685591647940012740928245)
                      ·
                        rfl

theorem cell23_3282678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_3282678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282678 prefixEnd_3282678 := by exact prefixLift 3282678
  have htrace : WordTrace (prefixWord ++ tailWord_3282678) baseStart_3282678 baseEnd_3282678 := by
    simpa [prefixWord, tailWord_3282678, baseEnd_3282678] using wordTrace_append hprefix tailTrace_3282678
  have hstable : (prefixWord ++ tailWord_3282678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282678).length < 2 ^ (prefixWord ++ tailWord_3282678).sum := by decide
  have hdescent : baseEnd_3282678 < baseStart_3282678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282711 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3282711 : Nat := 118140960795 + 3282711 * 2 ^ 59
def prefixEnd_3282711 : Nat := 4983230072969 + 3 ^ 40 * 3282711 * 2
def baseEnd_3282711 : Nat := 1685608592801611111815593

theorem tailTrace_3282711 : CollatzResearch.WordTrace tailWord_3282711 prefixEnd_3282711 1685608592801611111815593 := by
  unfold tailWord_3282711
  simp only [CollatzResearch.WordTrace]
  refine ⟨119730306410306164248887987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79820204273537442832591991 119730306410306164248887987)
  ·
    refine ⟨179595459615459246373331981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119730306410306164248887987 179595459615459246373331981)
    ·
      refine ⟨67348297355797217389999493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179595459615459246373331981 67348297355797217389999493)
      ·
        refine ⟨12627805754211978260624905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67348297355797217389999493 12627805754211978260624905)
        ·
          refine ⟨9470854315658983695468679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12627805754211978260624905 9470854315658983695468679)
          ·
            refine ⟨14206281473488475543203019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9470854315658983695468679 14206281473488475543203019)
            ·
              refine ⟨21309422210232713314804529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14206281473488475543203019 21309422210232713314804529)
              ·
                refine ⟨15982066657674534986103397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21309422210232713314804529 15982066657674534986103397)
                ·
                  refine ⟨2996637498313975309894387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15982066657674534986103397 2996637498313975309894387)
                  ·
                    refine ⟨4494956247470962964841581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2996637498313975309894387 4494956247470962964841581)
                    ·
                      refine ⟨1685608592801611111815593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4494956247470962964841581 1685608592801611111815593)
                      ·
                        rfl

theorem cell23_3282711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3282711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282711 prefixEnd_3282711 := by exact prefixLift 3282711
  have htrace : WordTrace (prefixWord ++ tailWord_3282711) baseStart_3282711 baseEnd_3282711 := by
    simpa [prefixWord, tailWord_3282711, baseEnd_3282711] using wordTrace_append hprefix tailTrace_3282711
  have hstable : (prefixWord ++ tailWord_3282711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282711).length < 2 ^ (prefixWord ++ tailWord_3282711).sum := by decide
  have hdescent : baseEnd_3282711 < baseStart_3282711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282718 : List Nat := [4, 3, 2, 2, 1, 2, 9]
def baseStart_3282718 : Nat := 118140960795 + 3282718 * 2 ^ 59
def prefixEnd_3282718 : Nat := 4983230072969 + 3 ^ 40 * 3282718 * 2
def baseEnd_3282718 : Nat := 20810027002051760301581

theorem tailTrace_3282718 : CollatzResearch.WordTrace tailWord_3282718 prefixEnd_3282718 20810027002051760301581 := by
  unfold tailWord_3282718
  simp only [CollatzResearch.WordTrace]
  refine ⟨14966320215160100555549101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79820374480853869629595205 14966320215160100555549101)
  ·
    refine ⟨5612370080685037708330913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14966320215160100555549101 5612370080685037708330913)
    ·
      refine ⟨4209277560513778281248185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5612370080685037708330913 4209277560513778281248185)
      ·
        refine ⟨3156958170385333710936139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4209277560513778281248185 3156958170385333710936139)
        ·
          refine ⟨4735437255578000566404209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156958170385333710936139 4735437255578000566404209)
          ·
            refine ⟨3551577941683500424803157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735437255578000566404209 3551577941683500424803157)
            ·
              refine ⟨20810027002051760301581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3551577941683500424803157 20810027002051760301581)
              ·
                rfl

theorem cell23_3282718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 9].length) (baseStart_3282718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282718 prefixEnd_3282718 := by exact prefixLift 3282718
  have htrace : WordTrace (prefixWord ++ tailWord_3282718) baseStart_3282718 baseEnd_3282718 := by
    simpa [prefixWord, tailWord_3282718, baseEnd_3282718] using wordTrace_append hprefix tailTrace_3282718
  have hstable : (prefixWord ++ tailWord_3282718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282718).length < 2 ^ (prefixWord ++ tailWord_3282718).sum := by decide
  have hdescent : baseEnd_3282718 < baseStart_3282718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282745 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3282745 : Nat := 118140960795 + 3282745 * 2 ^ 59
def prefixEnd_3282745 : Nat := 4983230072969 + 3 ^ 40 * 3282745 * 2
def baseEnd_3282745 : Nat := 1685626051143863978790437

theorem tailTrace_3282745 : CollatzResearch.WordTrace tailWord_3282745 prefixEnd_3282745 1685626051143863978790437 := by
  unfold tailWord_3282745
  simp only [CollatzResearch.WordTrace]
  refine ⟨119731546492182988055625689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79821030994788658703750459 119731546492182988055625689)
  ·
    refine ⟨89798659869137241041719267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119731546492182988055625689 89798659869137241041719267)
    ·
      refine ⟨134697989803705861562578901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89798659869137241041719267 134697989803705861562578901)
      ·
        refine ⟨3156984136024356130372943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 134697989803705861562578901 3156984136024356130372943)
        ·
          refine ⟨4735476204036534195559415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156984136024356130372943 4735476204036534195559415)
          ·
            refine ⟨7103214306054801293339123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735476204036534195559415 7103214306054801293339123)
            ·
              refine ⟨10654821459082201940008685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103214306054801293339123 10654821459082201940008685)
              ·
                refine ⟨3995558047155825727503257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10654821459082201940008685 3995558047155825727503257)
                ·
                  refine ⟨2996668535366869295627443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3995558047155825727503257 2996668535366869295627443)
                  ·
                    refine ⟨4495002803050303943441165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2996668535366869295627443 4495002803050303943441165)
                    ·
                      refine ⟨1685626051143863978790437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4495002803050303943441165 1685626051143863978790437)
                      ·
                        rfl

theorem cell23_3282745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3282745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282745 prefixEnd_3282745 := by exact prefixLift 3282745
  have htrace : WordTrace (prefixWord ++ tailWord_3282745) baseStart_3282745 baseEnd_3282745 := by
    simpa [prefixWord, tailWord_3282745, baseEnd_3282745] using wordTrace_append hprefix tailTrace_3282745
  have hstable : (prefixWord ++ tailWord_3282745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282745).length < 2 ^ (prefixWord ++ tailWord_3282745).sum := by decide
  have hdescent : baseEnd_3282745 < baseStart_3282745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282757 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 9]
def baseStart_3282757 : Nat := 118140960795 + 3282757 * 2 ^ 59
def prefixEnd_3282757 : Nat := 4983230072969 + 3 ^ 40 * 3282757 * 2
def baseEnd_3282757 : Nat := 187292468101301992426709

theorem tailTrace_3282757 : CollatzResearch.WordTrace tailWord_3282757 prefixEnd_3282757 187292468101301992426709 := by
  unfold tailWord_3282757
  simp only [CollatzResearch.WordTrace]
  refine ⟨119731984168139514105062525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79821322778759676070041683 119731984168139514105062525)
  ·
    refine ⟨44899494063052317789398447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119731984168139514105062525 44899494063052317789398447)
    ·
      refine ⟨67349241094578476684097671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44899494063052317789398447 67349241094578476684097671)
      ·
        refine ⟨101023861641867715026146507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67349241094578476684097671 101023861641867715026146507)
        ·
          refine ⟨151535792462801572539219761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101023861641867715026146507 151535792462801572539219761)
          ·
            refine ⟨113651844347101179404414821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151535792462801572539219761 113651844347101179404414821)
            ·
              refine ⟨21309720815081471138327779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113651844347101179404414821 21309720815081471138327779)
              ·
                refine ⟨31964581222622206707491669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21309720815081471138327779 31964581222622206707491669)
                ·
                  refine ⟨187292468101301992426709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31964581222622206707491669 187292468101301992426709)
                  ·
                    rfl

theorem cell23_3282757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_3282757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282757 prefixEnd_3282757 := by exact prefixLift 3282757
  have htrace : WordTrace (prefixWord ++ tailWord_3282757) baseStart_3282757 baseEnd_3282757 := by
    simpa [prefixWord, tailWord_3282757, baseEnd_3282757] using wordTrace_append hprefix tailTrace_3282757
  have hstable : (prefixWord ++ tailWord_3282757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282757).length < 2 ^ (prefixWord ++ tailWord_3282757).sum := by decide
  have hdescent : baseEnd_3282757 < baseStart_3282757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282791 : List Nat := [1, 1, 5, 1, 2, 1, 3, 4, 5]
def baseStart_3282791 : Nat := 118140960795 + 3282791 * 2 ^ 59
def prefixEnd_3282791 : Nat := 4983230072969 + 3 ^ 40 * 3282791 * 2
def baseEnd_3282791 : Nat := 187294407917107866535025

theorem tailTrace_3282791 : CollatzResearch.WordTrace tailWord_3282791 prefixEnd_3282791 187294407917107866535025 := by
  unfold tailWord_3282791
  simp only [CollatzResearch.WordTrace]
  refine ⟨119733224250016337911800227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79822149500010891941200151 119733224250016337911800227)
  ·
    refine ⟨179599836375024506867700341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119733224250016337911800227 179599836375024506867700341)
    ·
      refine ⟨16837484660158547518846907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179599836375024506867700341 16837484660158547518846907)
      ·
        refine ⟨25256226990237821278270361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16837484660158547518846907 25256226990237821278270361)
        ·
          refine ⟨18942170242678365958702771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25256226990237821278270361 18942170242678365958702771)
          ·
            refine ⟨28413255364017548938054157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18942170242678365958702771 28413255364017548938054157)
            ·
              refine ⟨10654970761506580851770309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28413255364017548938054157 10654970761506580851770309)
              ·
                refine ⟨1997807017782483909706933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10654970761506580851770309 1997807017782483909706933)
                ·
                  refine ⟨187294407917107866535025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997807017782483909706933 187294407917107866535025)
                  ·
                    rfl

theorem cell23_3282791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 5].length) (baseStart_3282791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282791 prefixEnd_3282791 := by exact prefixLift 3282791
  have htrace : WordTrace (prefixWord ++ tailWord_3282791) baseStart_3282791 baseEnd_3282791 := by
    simpa [prefixWord, tailWord_3282791, baseEnd_3282791] using wordTrace_append hprefix tailTrace_3282791
  have hstable : (prefixWord ++ tailWord_3282791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282791).length < 2 ^ (prefixWord ++ tailWord_3282791).sum := by decide
  have hdescent : baseEnd_3282791 < baseStart_3282791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282841 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 2, 4, 2]
def baseStart_3282841 : Nat := 118140960795 + 3282841 * 2 ^ 59
def prefixEnd_3282841 : Nat := 4983230072969 + 3 ^ 40 * 3282841 * 2
def baseEnd_3282841 : Nat := 1685675345286695603189995

theorem tailTrace_3282841 : CollatzResearch.WordTrace tailWord_3282841 prefixEnd_3282841 1685675345286695603189995 := by
  unfold tailWord_3282841
  simp only [CollatzResearch.WordTrace]
  refine ⟨119735047899835196451120377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79823365266556797634080251 119735047899835196451120377)
  ·
    refine ⟨89801285924876397338340283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119735047899835196451120377 89801285924876397338340283)
    ·
      refine ⟨134701928887314596007510425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89801285924876397338340283 134701928887314596007510425)
      ·
        refine ⟨101026446665485947005632819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134701928887314596007510425 101026446665485947005632819)
        ·
          refine ⟨151539669998228920508449229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101026446665485947005632819 151539669998228920508449229)
          ·
            refine ⟨56827376249335845190668461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151539669998228920508449229 56827376249335845190668461)
            ·
              refine ⟨21310266093500941946500673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56827376249335845190668461 21310266093500941946500673)
              ·
                refine ⟨15982699570125706459875505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21310266093500941946500673 15982699570125706459875505)
                ·
                  refine ⟨11987024677594279844906629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15982699570125706459875505 11987024677594279844906629)
                  ·
                    refine ⟨2247567127048927470919993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11987024677594279844906629 2247567127048927470919993)
                    ·
                      refine ⟨1685675345286695603189995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247567127048927470919993 1685675345286695603189995)
                      ·
                        rfl

theorem cell23_3282841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_3282841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282841 prefixEnd_3282841 := by exact prefixLift 3282841
  have htrace : WordTrace (prefixWord ++ tailWord_3282841) baseStart_3282841 baseEnd_3282841 := by
    simpa [prefixWord, tailWord_3282841, baseEnd_3282841] using wordTrace_append hprefix tailTrace_3282841
  have hstable : (prefixWord ++ tailWord_3282841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282841).length < 2 ^ (prefixWord ++ tailWord_3282841).sum := by decide
  have hdescent : baseEnd_3282841 < baseStart_3282841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282902 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3282902 : Nat := 118140960795 + 3282902 * 2 ^ 59
def prefixEnd_3282902 : Nat := 4983230072969 + 3 ^ 40 * 3282902 * 2
def baseEnd_3282902 : Nat := 561902222535539954842405

theorem tailTrace_3282902 : CollatzResearch.WordTrace tailWord_3282902 prefixEnd_3282902 561902222535539954842405 := by
  unfold tailWord_3282902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483579547038387741818185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79824848501742802579393973 7483579547038387741818185)
  ·
    refine ⟨5612684660278790806363639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7483579547038387741818185 5612684660278790806363639)
    ·
      refine ⟨8419026990418186209545459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5612684660278790806363639 8419026990418186209545459)
      ·
        refine ⟨12628540485627279314318189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8419026990418186209545459 12628540485627279314318189)
        ·
          refine ⟨4735702682110229742869321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12628540485627279314318189 4735702682110229742869321)
          ·
            refine ⟨3551777011582672307151991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735702682110229742869321 3551777011582672307151991)
            ·
              refine ⟨5327665517374008460727987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3551777011582672307151991 5327665517374008460727987)
              ·
                refine ⟨7991498276061012691091981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5327665517374008460727987 7991498276061012691091981)
                ·
                  refine ⟨2996811853522879759159493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7991498276061012691091981 2996811853522879759159493)
                  ·
                    refine ⟨561902222535539954842405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2996811853522879759159493 561902222535539954842405)
                    ·
                      rfl

theorem cell23_3282902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3282902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282902 prefixEnd_3282902 := by exact prefixLift 3282902
  have htrace : WordTrace (prefixWord ++ tailWord_3282902) baseStart_3282902 baseEnd_3282902 := by
    simpa [prefixWord, tailWord_3282902, baseEnd_3282902] using wordTrace_append hprefix tailTrace_3282902
  have hstable : (prefixWord ++ tailWord_3282902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282902).length < 2 ^ (prefixWord ++ tailWord_3282902).sum := by decide
  have hdescent : baseEnd_3282902 < baseStart_3282902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282924 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_3282924 : Nat := 118140960795 + 3282924 * 2 ^ 59
def prefixEnd_3282924 : Nat := 4983230072969 + 3 ^ 40 * 3282924 * 2
def baseEnd_3282924 : Nat := 561905988060339592817371

theorem tailTrace_3282924 : CollatzResearch.WordTrace tailWord_3282924 prefixEnd_3282924 561905988060339592817371 := by
  unfold tailWord_3282924
  simp only [CollatzResearch.WordTrace]
  refine ⟨59869037579267250813195913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79825383439023001084261217 59869037579267250813195913)
  ·
    refine ⟨44901778184450438109896935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59869037579267250813195913 44901778184450438109896935)
    ·
      refine ⟨67352667276675657164845403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44901778184450438109896935 67352667276675657164845403)
      ·
        refine ⟨101029000915013485747268105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67352667276675657164845403 101029000915013485747268105)
        ·
          refine ⟨75771750686260114310451079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101029000915013485747268105 75771750686260114310451079)
          ·
            refine ⟨113657626029390171465676619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75771750686260114310451079 113657626029390171465676619)
            ·
              refine ⟨170486439044085257198514929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113657626029390171465676619 170486439044085257198514929)
              ·
                refine ⟨127864829283063942898886197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170486439044085257198514929 127864829283063942898886197)
                ·
                  refine ⟨11987327745287244646770581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127864829283063942898886197 11987327745287244646770581)
                  ·
                    refine ⟨561905988060339592817371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11987327745287244646770581 561905988060339592817371)
                    ·
                      rfl

theorem cell23_3282924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_3282924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282924 prefixEnd_3282924 := by exact prefixLift 3282924
  have htrace : WordTrace (prefixWord ++ tailWord_3282924) baseStart_3282924 baseEnd_3282924 := by
    simpa [prefixWord, tailWord_3282924, baseEnd_3282924] using wordTrace_append hprefix tailTrace_3282924
  have hstable : (prefixWord ++ tailWord_3282924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282924).length < 2 ^ (prefixWord ++ tailWord_3282924).sum := by decide
  have hdescent : baseEnd_3282924 < baseStart_3282924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282931 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 2, 6, 2]
def baseStart_3282931 : Nat := 118140960795 + 3282931 * 2 ^ 59
def prefixEnd_3282931 : Nat := 4983230072969 + 3 ^ 40 * 3282931 * 2
def baseEnd_3282931 : Nat := 1685721558545600251064581

theorem tailTrace_3282931 : CollatzResearch.WordTrace tailWord_3282931 prefixEnd_3282931 1685721558545600251064581 := by
  unfold tailWord_3282931
  simp only [CollatzResearch.WordTrace]
  refine ⟨119738330469509141821896647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79825553646339427881264431 119738330469509141821896647)
  ·
    refine ⟨179607495704263712732844971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119738330469509141821896647 179607495704263712732844971)
    ·
      refine ⟨269411243556395569099267457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179607495704263712732844971 269411243556395569099267457)
      ·
        refine ⟨202058432667296676824450593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269411243556395569099267457 202058432667296676824450593)
        ·
          refine ⟨151543824500472507618337945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202058432667296676824450593 151543824500472507618337945)
          ·
            refine ⟨113657868375354380713753459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151543824500472507618337945 113657868375354380713753459)
            ·
              refine ⟨170486802563031571070630189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113657868375354380713753459 170486802563031571070630189)
              ·
                refine ⟨63932550961136839151486321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170486802563031571070630189 63932550961136839151486321)
                ·
                  refine ⟨47949413220852629363614741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63932550961136839151486321 47949413220852629363614741)
                  ·
                    refine ⟨2247628744727467001419441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47949413220852629363614741 2247628744727467001419441)
                    ·
                      refine ⟨1685721558545600251064581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247628744727467001419441 1685721558545600251064581)
                      ·
                        rfl

theorem cell23_3282931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6, 2].length) (baseStart_3282931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282931 prefixEnd_3282931 := by exact prefixLift 3282931
  have htrace : WordTrace (prefixWord ++ tailWord_3282931) baseStart_3282931 baseEnd_3282931 := by
    simpa [prefixWord, tailWord_3282931, baseEnd_3282931] using wordTrace_append hprefix tailTrace_3282931
  have hstable : (prefixWord ++ tailWord_3282931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282931).length < 2 ^ (prefixWord ++ tailWord_3282931).sum := by decide
  have hdescent : baseEnd_3282931 < baseStart_3282931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282941 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_3282941 : Nat := 118140960795 + 3282941 * 2 ^ 59
def prefixEnd_3282941 : Nat := 4983230072969 + 3 ^ 40 * 3282941 * 2
def baseEnd_3282941 : Nat := 561908897784048403979845

theorem tailTrace_3282941 : CollatzResearch.WordTrace tailWord_3282941 prefixEnd_3282941 561908897784048403979845 := by
  unfold tailWord_3282941
  simp only [CollatzResearch.WordTrace]
  refine ⟨119738695199472913529760677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79825796799648609019840451 119738695199472913529760677)
  ·
    refine ⟨22451005349901171286830127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119738695199472913529760677 22451005349901171286830127)
    ·
      refine ⟨33676508024851756930245191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22451005349901171286830127 33676508024851756930245191)
      ·
        refine ⟨50514762037277635395367787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33676508024851756930245191 50514762037277635395367787)
        ·
          refine ⟨75772143055916453093051681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50514762037277635395367787 75772143055916453093051681)
          ·
            refine ⟨56829107291937339819788761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75772143055916453093051681 56829107291937339819788761)
            ·
              refine ⟨42621830468953004864841571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56829107291937339819788761 42621830468953004864841571)
              ·
                refine ⟨63932745703429507297262357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42621830468953004864841571 63932745703429507297262357)
                ·
                  refine ⟨2996847454848258154559173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63932745703429507297262357 2996847454848258154559173)
                  ·
                    refine ⟨561908897784048403979845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2996847454848258154559173 561908897784048403979845)
                    ·
                      rfl

theorem cell23_3282941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_3282941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282941 prefixEnd_3282941 := by exact prefixLift 3282941
  have htrace : WordTrace (prefixWord ++ tailWord_3282941) baseStart_3282941 baseEnd_3282941 := by
    simpa [prefixWord, tailWord_3282941, baseEnd_3282941] using wordTrace_append hprefix tailTrace_3282941
  have hstable : (prefixWord ++ tailWord_3282941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282941).length < 2 ^ (prefixWord ++ tailWord_3282941).sum := by decide
  have hdescent : baseEnd_3282941 < baseStart_3282941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282944 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_3282944 : Nat := 118140960795 + 3282944 * 2 ^ 59
def prefixEnd_3282944 : Nat := 4983230072969 + 3 ^ 40 * 3282944 * 2
def baseEnd_3282944 : Nat := 1685728233794108700202021

theorem tailTrace_3282944 : CollatzResearch.WordTrace tailWord_3282944 prefixEnd_3282944 1685728233794108700202021 := by
  unfold tailWord_3282944
  simp only [CollatzResearch.WordTrace]
  refine ⟨59869402309231022521059943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79825869745641363361413257 59869402309231022521059943)
  ·
    refine ⟨89804103463846533781589915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59869402309231022521059943 89804103463846533781589915)
    ·
      refine ⟨134706155195769800672384873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89804103463846533781589915 134706155195769800672384873)
      ·
        refine ⟨101029616396827350504288655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134706155195769800672384873 101029616396827350504288655)
        ·
          refine ⟨151544424595241025756432983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101029616396827350504288655 151544424595241025756432983)
          ·
            refine ⟨227316636892861538634649475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151544424595241025756432983 227316636892861538634649475)
            ·
              refine ⟨340974955339292307951974213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227316636892861538634649475 340974955339292307951974213)
              ·
                refine ⟨63932804126117307740995165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340974955339292307951974213 63932804126117307740995165)
                ·
                  refine ⟨23974801547293990402873187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63932804126117307740995165 23974801547293990402873187)
                  ·
                    refine ⟨35962202320940985604309781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23974801547293990402873187 35962202320940985604309781)
                    ·
                      refine ⟨1685728233794108700202021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35962202320940985604309781 1685728233794108700202021)
                      ·
                        rfl

theorem cell23_3282944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_3282944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282944 prefixEnd_3282944 := by exact prefixLift 3282944
  have htrace : WordTrace (prefixWord ++ tailWord_3282944) baseStart_3282944 baseEnd_3282944 := by
    simpa [prefixWord, tailWord_3282944, baseEnd_3282944] using wordTrace_append hprefix tailTrace_3282944
  have hstable : (prefixWord ++ tailWord_3282944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282944).length < 2 ^ (prefixWord ++ tailWord_3282944).sum := by decide
  have hdescent : baseEnd_3282944 < baseStart_3282944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282954 : List Nat := [3, 1, 2, 2, 15]
def baseStart_3282954 : Nat := 118140960795 + 3282954 * 2 ^ 59
def prefixEnd_3282954 : Nat := 4983230072969 + 3 ^ 40 * 3282954 * 2
def baseEnd_3282954 : Nat := 2312391452127096928775

theorem tailTrace_3282954 : CollatzResearch.WordTrace tailWord_3282954 prefixEnd_3282954 2312391452127096928775 := by
  unfold tailWord_3282954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29934792337106454187495979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79826112898950544499989277 29934792337106454187495979)
  ·
    refine ⟨44902188505659681281243969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29934792337106454187495979 44902188505659681281243969)
    ·
      refine ⟨33676641379244760960932977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44902188505659681281243969 33676641379244760960932977)
      ·
        refine ⟨25257481034433570720699733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33676641379244760960932977 25257481034433570720699733)
        ·
          refine ⟨2312391452127096928775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 25257481034433570720699733 2312391452127096928775)
          ·
            rfl

theorem cell23_3282954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 15].length) (baseStart_3282954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282954 prefixEnd_3282954 := by exact prefixLift 3282954
  have htrace : WordTrace (prefixWord ++ tailWord_3282954) baseStart_3282954 baseEnd_3282954 := by
    simpa [prefixWord, tailWord_3282954, baseEnd_3282954] using wordTrace_append hprefix tailTrace_3282954
  have hstable : (prefixWord ++ tailWord_3282954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282954).length < 2 ^ (prefixWord ++ tailWord_3282954).sum := by decide
  have hdescent : baseEnd_3282954 < baseStart_3282954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282978 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_3282978 : Nat := 118140960795 + 3282978 * 2 ^ 59
def prefixEnd_3282978 : Nat := 4983230072969 + 3 ^ 40 * 3282978 * 2
def baseEnd_3282978 : Nat := 1685745692136361567176865

theorem tailTrace_3282978 : CollatzResearch.WordTrace tailWord_3282978 prefixEnd_3282978 1685745692136361567176865 := by
  unfold tailWord_3282978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29935011175084717212214397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79826696466892579232571725 29935011175084717212214397)
  ·
    refine ⟨11225629190656768954580399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29935011175084717212214397 11225629190656768954580399)
    ·
      refine ⟨16838443785985153431870599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11225629190656768954580399 16838443785985153431870599)
      ·
        refine ⟨25257665678977730147805899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16838443785985153431870599 25257665678977730147805899)
        ·
          refine ⟨37886498518466595221708849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25257665678977730147805899 37886498518466595221708849)
          ·
            refine ⟨28414873888849946416281637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37886498518466595221708849 28414873888849946416281637)
            ·
              refine ⟨5327788854159364953052807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28414873888849946416281637 5327788854159364953052807)
              ·
                refine ⟨7991683281239047429579211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5327788854159364953052807 7991683281239047429579211)
                ·
                  refine ⟨11987524921858571144368817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7991683281239047429579211 11987524921858571144368817)
                  ·
                    refine ⟨8990643691393928358276613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11987524921858571144368817 8990643691393928358276613)
                    ·
                      refine ⟨1685745692136361567176865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8990643691393928358276613 1685745692136361567176865)
                      ·
                        rfl

theorem cell23_3282978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_3282978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3282978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3282978 prefixEnd_3282978 := by exact prefixLift 3282978
  have htrace : WordTrace (prefixWord ++ tailWord_3282978) baseStart_3282978 baseEnd_3282978 := by
    simpa [prefixWord, tailWord_3282978, baseEnd_3282978] using wordTrace_append hprefix tailTrace_3282978
  have hstable : (prefixWord ++ tailWord_3282978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282978).length < 2 ^ (prefixWord ++ tailWord_3282978).sum := by decide
  have hdescent : baseEnd_3282978 < baseStart_3282978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283031 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 2, 6]
def baseStart_3283031 : Nat := 118140960795 + 3283031 * 2 ^ 59
def prefixEnd_3283031 : Nat := 4983230072969 + 3 ^ 40 * 3283031 * 2
def baseEnd_3283031 : Nat := 561924302203683286604707

theorem tailTrace_3283031 : CollatzResearch.WordTrace tailWord_3283031 prefixEnd_3283031 561924302203683286604707 := by
  unfold tailWord_3283031
  simp only [CollatzResearch.WordTrace]
  refine ⟨119741977769146858900536947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79827985179431239267024631 119741977769146858900536947)
  ·
    refine ⟨179612966653720288350805421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119741977769146858900536947 179612966653720288350805421)
    ·
      refine ⟨67354862495145108131552033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179612966653720288350805421 67354862495145108131552033)
      ·
        refine ⟨50516146871358831098664025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67354862495145108131552033 50516146871358831098664025)
        ·
          refine ⟨37887110153519123323998019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50516146871358831098664025 37887110153519123323998019)
          ·
            refine ⟨56830665230278684985997029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37887110153519123323998019 56830665230278684985997029)
            ·
              refine ⟨10655749730677253434874443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56830665230278684985997029 10655749730677253434874443)
              ·
                refine ⟨15983624596015880152311665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10655749730677253434874443 15983624596015880152311665)
                ·
                  refine ⟨11987718447011910114233749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15983624596015880152311665 11987718447011910114233749)
                  ·
                    refine ⟨561924302203683286604707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11987718447011910114233749 561924302203683286604707)
                    ·
                      rfl

theorem cell23_3283031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_3283031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283031 prefixEnd_3283031 := by exact prefixLift 3283031
  have htrace : WordTrace (prefixWord ++ tailWord_3283031) baseStart_3283031 baseEnd_3283031 := by
    simpa [prefixWord, tailWord_3283031, baseEnd_3283031] using wordTrace_append hprefix tailTrace_3283031
  have hstable : (prefixWord ++ tailWord_3283031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283031).length < 2 ^ (prefixWord ++ tailWord_3283031).sum := by decide
  have hdescent : baseEnd_3283031 < baseStart_3283031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283032 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 2, 1, 3]
def baseStart_3283032 : Nat := 118140960795 + 3283032 * 2 ^ 59
def prefixEnd_3283032 : Nat := 4983230072969 + 3 ^ 40 * 3283032 * 2
def baseEnd_3283032 : Nat := 1685773420091704355901617

theorem tailTrace_3283032 : CollatzResearch.WordTrace tailWord_3283032 prefixEnd_3283032 1685773420091704355901617 := by
  unfold tailWord_3283032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59871007121071618035661675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79828009494762157380882233 59871007121071618035661675)
  ·
    refine ⟨89806510681607427053492513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59871007121071618035661675 89806510681607427053492513)
    ·
      refine ⟨67354883011205570290119385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89806510681607427053492513 67354883011205570290119385)
      ·
        refine ⟨50516162258404177717589539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67354883011205570290119385 50516162258404177717589539)
        ·
          refine ⟨75774243387606266576384309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50516162258404177717589539 75774243387606266576384309)
          ·
            refine ⟨7103835317588087491536029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75774243387606266576384309 7103835317588087491536029)
            ·
              refine ⟨2663938244095532809326011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7103835317588087491536029 2663938244095532809326011)
              ·
                refine ⟨3995907366143299213989017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663938244095532809326011 3995907366143299213989017)
                ·
                  refine ⟨2996930524607474410491763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3995907366143299213989017 2996930524607474410491763)
                  ·
                    refine ⟨4495395786911211615737645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2996930524607474410491763 4495395786911211615737645)
                    ·
                      refine ⟨1685773420091704355901617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4495395786911211615737645 1685773420091704355901617)
                      ·
                        rfl

theorem cell23_3283032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_3283032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283032 prefixEnd_3283032 := by exact prefixLift 3283032
  have htrace : WordTrace (prefixWord ++ tailWord_3283032) baseStart_3283032 baseEnd_3283032 := by
    simpa [prefixWord, tailWord_3283032, baseEnd_3283032] using wordTrace_append hprefix tailTrace_3283032
  have hstable : (prefixWord ++ tailWord_3283032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283032).length < 2 ^ (prefixWord ++ tailWord_3283032).sum := by decide
  have hdescent : baseEnd_3283032 < baseStart_3283032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283041 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_3283041 : Nat := 118140960795 + 3283041 * 2 ^ 59
def prefixEnd_3283041 : Nat := 4983230072969 + 3 ^ 40 * 3283041 * 2
def baseEnd_3283041 : Nat := 1685778041417594820689075

theorem tailTrace_3283041 : CollatzResearch.WordTrace tailWord_3283041 prefixEnd_3283041 1685778041417594820689075 := by
  unfold tailWord_3283041
  simp only [CollatzResearch.WordTrace]
  refine ⟨119742342499110630608400977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79828228332740420405600651 119742342499110630608400977)
  ·
    refine ⟨89806756874332972956300733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119742342499110630608400977 89806756874332972956300733)
    ·
      refine ⟨33677533827874864858612775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89806756874332972956300733 33677533827874864858612775)
      ·
        refine ⟨50516300741812297287919163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33677533827874864858612775 50516300741812297287919163)
        ·
          refine ⟨75774451112718445931878745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50516300741812297287919163 75774451112718445931878745)
          ·
            refine ⟨56830838334538834448909059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75774451112718445931878745 56830838334538834448909059)
            ·
              refine ⟨85246257501808251673363589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56830838334538834448909059 85246257501808251673363589)
              ·
                refine ⟨15983673281589047188755673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85246257501808251673363589 15983673281589047188755673)
                ·
                  refine ⟨11987754961191785391566755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15983673281589047188755673 11987754961191785391566755)
                  ·
                    refine ⟨17981632441787678087350133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11987754961191785391566755 17981632441787678087350133)
                    ·
                      refine ⟨1685778041417594820689075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17981632441787678087350133 1685778041417594820689075)
                      ·
                        rfl

theorem cell23_3283041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_3283041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283041 prefixEnd_3283041 := by exact prefixLift 3283041
  have htrace : WordTrace (prefixWord ++ tailWord_3283041) baseStart_3283041 baseEnd_3283041 := by
    simpa [prefixWord, tailWord_3283041, baseEnd_3283041] using wordTrace_append hprefix tailTrace_3283041
  have hstable : (prefixWord ++ tailWord_3283041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283041).length < 2 ^ (prefixWord ++ tailWord_3283041).sum := by decide
  have hdescent : baseEnd_3283041 < baseStart_3283041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283055 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 4, 2, 2]
def baseStart_3283055 : Nat := 118140960795 + 3283055 * 2 ^ 59
def prefixEnd_3283055 : Nat := 4983230072969 + 3 ^ 40 * 3283055 * 2
def baseEnd_3283055 : Nat := 1685785230146757765914011

theorem tailTrace_3283055 : CollatzResearch.WordTrace tailWord_3283055 prefixEnd_3283055 1685785230146757765914011 := by
  unfold tailWord_3283055
  simp only [CollatzResearch.WordTrace]
  refine ⟨119742853121059910999410619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79828568747373273999607079 119742853121059910999410619)
  ·
    refine ⟨179614279681589866499115929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119742853121059910999410619 179614279681589866499115929)
    ·
      refine ⟨134710709761192399874336947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179614279681589866499115929 134710709761192399874336947)
      ·
        refine ⟨202066064641788599811505421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134710709761192399874336947 202066064641788599811505421)
        ·
          refine ⟨75774774240670724929314533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202066064641788599811505421 75774774240670724929314533)
          ·
            refine ⟨14207770170125760924246475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75774774240670724929314533 14207770170125760924246475)
            ·
              refine ⟨21311655255188641386369713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14207770170125760924246475 21311655255188641386369713)
              ·
                refine ⟨15983741441391481039777285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21311655255188641386369713 15983741441391481039777285)
                ·
                  refine ⟨2996951520260902694958241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15983741441391481039777285 2996951520260902694958241)
                  ·
                    refine ⟨2247713640195677021218681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2996951520260902694958241 2247713640195677021218681)
                    ·
                      refine ⟨1685785230146757765914011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247713640195677021218681 1685785230146757765914011)
                      ·
                        rfl

theorem cell23_3283055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 2, 2].length) (baseStart_3283055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283055 prefixEnd_3283055 := by exact prefixLift 3283055
  have htrace : WordTrace (prefixWord ++ tailWord_3283055) baseStart_3283055 baseEnd_3283055 := by
    simpa [prefixWord, tailWord_3283055, baseEnd_3283055] using wordTrace_append hprefix tailTrace_3283055
  have hstable : (prefixWord ++ tailWord_3283055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283055).length < 2 ^ (prefixWord ++ tailWord_3283055).sum := by decide
  have hdescent : baseEnd_3283055 < baseStart_3283055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283058 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3283058 : Nat := 118140960795 + 3283058 * 2 ^ 59
def prefixEnd_3283058 : Nat := 4983230072969 + 3 ^ 40 * 3283058 * 2
def baseEnd_3283058 : Nat := 1685786770588721254176497

theorem tailTrace_3283058 : CollatzResearch.WordTrace tailWord_3283058 prefixEnd_3283058 1685786770588721254176497 := by
  unfold tailWord_3283058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29935740635012260627942457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79828641693366028341179885 29935740635012260627942457)
  ·
    refine ⟨22451805476259195470956843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29935740635012260627942457 22451805476259195470956843)
    ·
      refine ⟨33677708214388793206435265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22451805476259195470956843 33677708214388793206435265)
      ·
        refine ⟨25258281160791594904826449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33677708214388793206435265 25258281160791594904826449)
        ·
          refine ⟨18943710870593696178619837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25258281160791594904826449 18943710870593696178619837)
          ·
            refine ⟨7103891576472636066982439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18943710870593696178619837 7103891576472636066982439)
            ·
              refine ⟨10655837364708954100473659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103891576472636066982439 10655837364708954100473659)
              ·
                refine ⟨15983756047063431150710489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10655837364708954100473659 15983756047063431150710489)
                ·
                  refine ⟨11987817035297573363032867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15983756047063431150710489 11987817035297573363032867)
                  ·
                    refine ⟨17981725552946360044549301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11987817035297573363032867 17981725552946360044549301)
                    ·
                      refine ⟨1685786770588721254176497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17981725552946360044549301 1685786770588721254176497)
                      ·
                        rfl

theorem cell23_3283058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3283058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283058 prefixEnd_3283058 := by exact prefixLift 3283058
  have htrace : WordTrace (prefixWord ++ tailWord_3283058) baseStart_3283058 baseEnd_3283058 := by
    simpa [prefixWord, tailWord_3283058, baseEnd_3283058] using wordTrace_append hprefix tailTrace_3283058
  have hstable : (prefixWord ++ tailWord_3283058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283058).length < 2 ^ (prefixWord ++ tailWord_3283058).sum := by decide
  have hdescent : baseEnd_3283058 < baseStart_3283058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283091 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 6, 5]
def baseStart_3283091 : Nat := 118140960795 + 3283091 * 2 ^ 59
def prefixEnd_3283091 : Nat := 4983230072969 + 3 ^ 40 * 3283091 * 2
def baseEnd_3283091 : Nat := 561934571816773208354615

theorem tailTrace_3283091 : CollatzResearch.WordTrace tailWord_3283091 prefixEnd_3283091 561934571816773208354615 := by
  unfold tailWord_3283091
  simp only [CollatzResearch.WordTrace]
  refine ⟨119744166148929489147721127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79829444099286326098480751 119744166148929489147721127)
  ·
    refine ⟨179616249223394233721581691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119744166148929489147721127 179616249223394233721581691)
    ·
      refine ⟨269424373835091350582372537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179616249223394233721581691 269424373835091350582372537)
      ·
        refine ⟨202068280376318512936779403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269424373835091350582372537 202068280376318512936779403)
        ·
          refine ⟨303102420564477769405169105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202068280376318512936779403 303102420564477769405169105)
          ·
            refine ⟨227326815423358327053876829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303102420564477769405169105 227326815423358327053876829)
            ·
              refine ⟨85247555783759372645203811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227326815423358327053876829 85247555783759372645203811)
              ·
                refine ⟨127871333675639058967805717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85247555783759372645203811 127871333675639058967805717)
                ·
                  refine ⟨5993968766045580889115893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127871333675639058967805717 5993968766045580889115893)
                  ·
                    refine ⟨561934571816773208354615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5993968766045580889115893 561934571816773208354615)
                    ·
                      rfl

theorem cell23_3283091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 5].length) (baseStart_3283091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283091 prefixEnd_3283091 := by exact prefixLift 3283091
  have htrace : WordTrace (prefixWord ++ tailWord_3283091) baseStart_3283091 baseEnd_3283091 := by
    simpa [prefixWord, tailWord_3283091, baseEnd_3283091] using wordTrace_append hprefix tailTrace_3283091
  have hstable : (prefixWord ++ tailWord_3283091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283091).length < 2 ^ (prefixWord ++ tailWord_3283091).sum := by decide
  have hdescent : baseEnd_3283091 < baseStart_3283091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283128 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_3283128 : Nat := 118140960795 + 3283128 * 2 ^ 59
def prefixEnd_3283128 : Nat := 4983230072969 + 3 ^ 40 * 3283128 * 2
def baseEnd_3283128 : Nat := 1685822714234535980301175

theorem tailTrace_3283128 : CollatzResearch.WordTrace tailWord_3283128 prefixEnd_3283128 1685822714234535980301175 := by
  unfold tailWord_3283128
  simp only [CollatzResearch.WordTrace]
  refine ⟨59872757824897722233409019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79830343766530296311212025 59872757824897722233409019)
  ·
    refine ⟨89809136737346583350113529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59872757824897722233409019 89809136737346583350113529)
    ·
      refine ⟨67356852553009937512585147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89809136737346583350113529 67356852553009937512585147)
      ·
        refine ⟨101035278829514906268877721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67356852553009937512585147 101035278829514906268877721)
        ·
          refine ⟨75776459122136179701658291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101035278829514906268877721 75776459122136179701658291)
          ·
            refine ⟨113664688683204269552487437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75776459122136179701658291 113664688683204269552487437)
            ·
              refine ⟨42624258256201601082182789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113664688683204269552487437 42624258256201601082182789)
              ·
                refine ⟨7992048423037800202909273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42624258256201601082182789 7992048423037800202909273)
                ·
                  refine ⟨5994036317278350152181955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7992048423037800202909273 5994036317278350152181955)
                  ·
                    refine ⟨8991054475917525228272933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5994036317278350152181955 8991054475917525228272933)
                    ·
                      refine ⟨1685822714234535980301175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8991054475917525228272933 1685822714234535980301175)
                      ·
                        rfl

theorem cell23_3283128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_3283128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283128 prefixEnd_3283128 := by exact prefixLift 3283128
  have htrace : WordTrace (prefixWord ++ tailWord_3283128) baseStart_3283128 baseEnd_3283128 := by
    simpa [prefixWord, tailWord_3283128, baseEnd_3283128] using wordTrace_append hprefix tailTrace_3283128
  have hstable : (prefixWord ++ tailWord_3283128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283128).length < 2 ^ (prefixWord ++ tailWord_3283128).sum := by decide
  have hdescent : baseEnd_3283128 < baseStart_3283128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283131 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5]
def baseStart_3283131 : Nat := 118140960795 + 3283131 * 2 ^ 59
def prefixEnd_3283131 : Nat := 4983230072969 + 3 ^ 40 * 3283131 * 2
def baseEnd_3283131 : Nat := 1685824254676499468563661

theorem tailTrace_3283131 : CollatzResearch.WordTrace tailWord_3283131 prefixEnd_3283131 1685824254676499468563661 := by
  unfold tailWord_3283131
  simp only [CollatzResearch.WordTrace]
  refine ⟨119745625068784575979177247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79830416712523050652784831 119745625068784575979177247)
  ·
    refine ⟨179618437603176863968765871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119745625068784575979177247 179618437603176863968765871)
    ·
      refine ⟨269427656404765295953148807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179618437603176863968765871 269427656404765295953148807)
      ·
        refine ⟨404141484607147943929723211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269427656404765295953148807 404141484607147943929723211)
        ·
          refine ⟨606212226910721915894584817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404141484607147943929723211 606212226910721915894584817)
          ·
            refine ⟨454659170183041436920938613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606212226910721915894584817 454659170183041436920938613)
            ·
              refine ⟨42624297204660134711337995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 454659170183041436920938613 42624297204660134711337995)
              ·
                refine ⟨63936445806990202067006993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42624297204660134711337995 63936445806990202067006993)
                ·
                  refine ⟨47952334355242651550255245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63936445806990202067006993 47952334355242651550255245)
                  ·
                    refine ⟨17982125383215994331345717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47952334355242651550255245 17982125383215994331345717)
                    ·
                      refine ⟨1685824254676499468563661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17982125383215994331345717 1685824254676499468563661)
                      ·
                        rfl

theorem cell23_3283131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_3283131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283131 prefixEnd_3283131 := by exact prefixLift 3283131
  have htrace : WordTrace (prefixWord ++ tailWord_3283131) baseStart_3283131 baseEnd_3283131 := by
    simpa [prefixWord, tailWord_3283131, baseEnd_3283131] using wordTrace_append hprefix tailTrace_3283131
  have hstable : (prefixWord ++ tailWord_3283131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283131).length < 2 ^ (prefixWord ++ tailWord_3283131).sum := by decide
  have hdescent : baseEnd_3283131 < baseStart_3283131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283205 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 6, 3, 2]
def baseStart_3283205 : Nat := 118140960795 + 3283205 * 2 ^ 59
def prefixEnd_3283205 : Nat := 4983230072969 + 3 ^ 40 * 3283205 * 2
def baseEnd_3283205 : Nat := 1685862252244932179038321

theorem tailTrace_3283205 : CollatzResearch.WordTrace tailWord_3283205 prefixEnd_3283205 1685862252244932179038321 := by
  unfold tailWord_3283205
  simp only [CollatzResearch.WordTrace]
  refine ⟨119748324070516486617371069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79832216047010991078247379 119748324070516486617371069)
  ·
    refine ⟨44905621526443682481514151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119748324070516486617371069 44905621526443682481514151)
    ·
      refine ⟨67358432289665523722271227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44905621526443682481514151 67358432289665523722271227)
      ·
        refine ⟨101037648434498285583406841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67358432289665523722271227 101037648434498285583406841)
        ·
          refine ⟨75778236325873714187555131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101037648434498285583406841 75778236325873714187555131)
          ·
            refine ⟨113667354488810571281332697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75778236325873714187555131 113667354488810571281332697)
            ·
              refine ⟨85250515866607928460999523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113667354488810571281332697 85250515866607928460999523)
              ·
                refine ⟨127875773799911892691499285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85250515866607928460999523 127875773799911892691499285)
                ·
                  refine ⟨5994176896870869969914029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127875773799911892691499285 5994176896870869969914029)
                  ·
                    refine ⟨2247816336326576238717761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5994176896870869969914029 2247816336326576238717761)
                    ·
                      refine ⟨1685862252244932179038321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247816336326576238717761 1685862252244932179038321)
                      ·
                        rfl

theorem cell23_3283205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_3283205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283205 prefixEnd_3283205 := by exact prefixLift 3283205
  have htrace : WordTrace (prefixWord ++ tailWord_3283205) baseStart_3283205 baseEnd_3283205 := by
    simpa [prefixWord, tailWord_3283205, baseEnd_3283205] using wordTrace_append hprefix tailTrace_3283205
  have hstable : (prefixWord ++ tailWord_3283205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283205).length < 2 ^ (prefixWord ++ tailWord_3283205).sum := by decide
  have hdescent : baseEnd_3283205 < baseStart_3283205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283228 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3283228 : Nat := 118140960795 + 3283228 * 2 ^ 59
def prefixEnd_3283228 : Nat := 4983230072969 + 3 ^ 40 * 3283228 * 2
def baseEnd_3283228 : Nat := 561958020766661863016905

theorem tailTrace_3283228 : CollatzResearch.WordTrace tailWord_3283228 prefixEnd_3283228 561958020766661863016905 := by
  unfold tailWord_3283228
  simp only [CollatzResearch.WordTrace]
  refine ⟨59874581474716580772729169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79832775299622107696972225 59874581474716580772729169)
  ·
    refine ⟨44905936106037435579546877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59874581474716580772729169 44905936106037435579546877)
    ·
      refine ⟨16839726039764038342330079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44905936106037435579546877 16839726039764038342330079)
      ·
        refine ⟨25259589059646057513495119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16839726039764038342330079 25259589059646057513495119)
        ·
          refine ⟨37889383589469086270242679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25259589059646057513495119 37889383589469086270242679)
          ·
            refine ⟨56834075384203629405364019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37889383589469086270242679 56834075384203629405364019)
            ·
              refine ⟨85251113076305444108046029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56834075384203629405364019 85251113076305444108046029)
              ·
                refine ⟨31969167403614541540517261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85251113076305444108046029 31969167403614541540517261)
                ·
                  refine ⟨11988437776355453077693973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31969167403614541540517261 11988437776355453077693973)
                  ·
                    refine ⟨561958020766661863016905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11988437776355453077693973 561958020766661863016905)
                    ·
                      rfl

theorem cell23_3283228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3283228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283228 prefixEnd_3283228 := by exact prefixLift 3283228
  have htrace : WordTrace (prefixWord ++ tailWord_3283228) baseStart_3283228 baseEnd_3283228 := by
    simpa [prefixWord, tailWord_3283228, baseEnd_3283228] using wordTrace_append hprefix tailTrace_3283228
  have hstable : (prefixWord ++ tailWord_3283228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283228).length < 2 ^ (prefixWord ++ tailWord_3283228).sum := by decide
  have hdescent : baseEnd_3283228 < baseStart_3283228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283235 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 4]
def baseStart_3283235 : Nat := 118140960795 + 3283235 * 2 ^ 59
def prefixEnd_3283235 : Nat := 4983230072969 + 3 ^ 40 * 3283235 * 2
def baseEnd_3283235 : Nat := 1685877656664567061663183

theorem tailTrace_3283235 : CollatzResearch.WordTrace tailWord_3283235 prefixEnd_3283235 1685877656664567061663183 := by
  unfold tailWord_3283235
  simp only [CollatzResearch.WordTrace]
  refine ⟨119749418260407801740963159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79832945506938534493975439 119749418260407801740963159)
  ·
    refine ⟨179624127390611702611444739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119749418260407801740963159 179624127390611702611444739)
    ·
      refine ⟨269436191085917553917167109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179624127390611702611444739 269436191085917553917167109)
      ·
        refine ⟨50519285828609541359468833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269436191085917553917167109 50519285828609541359468833)
        ·
          refine ⟨37889464371457156019601625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50519285828609541359468833 37889464371457156019601625)
          ·
            refine ⟨28417098278592867014701219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37889464371457156019601625 28417098278592867014701219)
            ·
              refine ⟨42625647417889300522051829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28417098278592867014701219 42625647417889300522051829)
              ·
                refine ⟨3996154445427121923942359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42625647417889300522051829 3996154445427121923942359)
                ·
                  refine ⟨5994231668140682885913539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996154445427121923942359 5994231668140682885913539)
                  ·
                    refine ⟨8991347502211024328870309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5994231668140682885913539 8991347502211024328870309)
                    ·
                      refine ⟨1685877656664567061663183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8991347502211024328870309 1685877656664567061663183)
                      ·
                        rfl

theorem cell23_3283235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_3283235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283235 prefixEnd_3283235 := by exact prefixLift 3283235
  have htrace : WordTrace (prefixWord ++ tailWord_3283235) baseStart_3283235 baseEnd_3283235 := by
    simpa [prefixWord, tailWord_3283235, baseEnd_3283235] using wordTrace_append hprefix tailTrace_3283235
  have hstable : (prefixWord ++ tailWord_3283235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283235).length < 2 ^ (prefixWord ++ tailWord_3283235).sum := by decide
  have hdescent : baseEnd_3283235 < baseStart_3283235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283248 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_3283248 : Nat := 118140960795 + 3283248 * 2 ^ 59
def prefixEnd_3283248 : Nat := 4983230072969 + 3 ^ 40 * 3283248 * 2
def baseEnd_3283248 : Nat := 1685884331913075510800623

theorem tailTrace_3283248 : CollatzResearch.WordTrace tailWord_3283248 prefixEnd_3283248 1685884331913075510800623 := by
  unfold tailWord_3283248
  simp only [CollatzResearch.WordTrace]
  refine ⟨59874946204680352480593199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79833261606240469974124265 59874946204680352480593199)
  ·
    refine ⟨89812419307020528720889799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59874946204680352480593199 89812419307020528720889799)
    ·
      refine ⟨134718628960530793081334699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89812419307020528720889799 134718628960530793081334699)
      ·
        refine ⟨202077943440796189622002049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134718628960530793081334699 202077943440796189622002049)
        ·
          refine ⟨151558457580597142216501537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202077943440796189622002049 151558457580597142216501537)
          ·
            refine ⟨113668843185447856662376153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151558457580597142216501537 113668843185447856662376153)
            ·
              refine ⟨85251632389085892496782115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113668843185447856662376153 85251632389085892496782115)
              ·
                refine ⟨127877448583628838745173173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85251632389085892496782115 127877448583628838745173173)
                ·
                  refine ⟨11988510804715203632359985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127877448583628838745173173 11988510804715203632359985)
                  ·
                    refine ⟨8991383103536402724269989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11988510804715203632359985 8991383103536402724269989)
                    ·
                      refine ⟨1685884331913075510800623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8991383103536402724269989 1685884331913075510800623)
                      ·
                        rfl

theorem cell23_3283248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_3283248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283248 prefixEnd_3283248 := by exact prefixLift 3283248
  have htrace : WordTrace (prefixWord ++ tailWord_3283248) baseStart_3283248 baseEnd_3283248 := by
    simpa [prefixWord, tailWord_3283248, baseEnd_3283248] using wordTrace_append hprefix tailTrace_3283248
  have hstable : (prefixWord ++ tailWord_3283248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283248).length < 2 ^ (prefixWord ++ tailWord_3283248).sum := by decide
  have hdescent : baseEnd_3283248 < baseStart_3283248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283258 : List Nat := [3, 1, 1, 1, 4, 2, 1, 10]
def baseStart_3283258 : Nat := 118140960795 + 3283258 * 2 ^ 59
def prefixEnd_3283258 : Nat := 4983230072969 + 3 ^ 40 * 3283258 * 2
def baseEnd_3283258 : Nat := 62440350619245202654651

theorem tailTrace_3283258 : CollatzResearch.WordTrace tailWord_3283258 prefixEnd_3283258 62440350619245202654651 := by
  unfold tailWord_3283258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29937564284831119167262607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79833504759549651112700285 29937564284831119167262607)
  ·
    refine ⟨44906346427246678750893911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29937564284831119167262607 44906346427246678750893911)
    ·
      refine ⟨67359519640870018126340867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44906346427246678750893911 67359519640870018126340867)
      ·
        refine ⟨101039279461305027189511301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67359519640870018126340867 101039279461305027189511301)
        ·
          refine ⟨18944864898994692598033369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101039279461305027189511301 18944864898994692598033369)
          ·
            refine ⟨14208648674246019448525027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18944864898994692598033369 14208648674246019448525027)
            ·
              refine ⟨21312973011369029172787541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14208648674246019448525027 21312973011369029172787541)
              ·
                refine ⟨62440350619245202654651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21312973011369029172787541 62440350619245202654651)
                ·
                  rfl

theorem cell23_3283258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_3283258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283258 prefixEnd_3283258 := by exact prefixLift 3283258
  have htrace : WordTrace (prefixWord ++ tailWord_3283258) baseStart_3283258 baseEnd_3283258 := by
    simpa [prefixWord, tailWord_3283258, baseEnd_3283258] using wordTrace_append hprefix tailTrace_3283258
  have hstable : (prefixWord ++ tailWord_3283258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283258).length < 2 ^ (prefixWord ++ tailWord_3283258).sum := by decide
  have hdescent : baseEnd_3283258 < baseStart_3283258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283272 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_3283272 : Nat := 118140960795 + 3283272 * 2 ^ 59
def prefixEnd_3283272 : Nat := 4983230072969 + 3 ^ 40 * 3283272 * 2
def baseEnd_3283272 : Nat := 1685896655448783416900513

theorem tailTrace_3283272 : CollatzResearch.WordTrace tailWord_3283272 prefixEnd_3283272 1685896655448783416900513 := by
  unfold tailWord_3283272
  simp only [CollatzResearch.WordTrace]
  refine ⟨59875383880636878530030035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79833845174182504706706713 59875383880636878530030035)
  ·
    refine ⟨89813075820955317795045053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59875383880636878530030035 89813075820955317795045053)
    ·
      refine ⟨33679903432858244173141895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89813075820955317795045053 33679903432858244173141895)
      ·
        refine ⟨50519855149287366259712843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33679903432858244173141895 50519855149287366259712843)
        ·
          refine ⟨75779782723931049389569265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50519855149287366259712843 75779782723931049389569265)
          ·
            refine ⟨56834837042948287042176949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75779782723931049389569265 56834837042948287042176949)
            ·
              refine ⟨5328265972776401910204089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56834837042948287042176949 5328265972776401910204089)
              ·
                refine ⟨3996199479582301432653067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328265972776401910204089 3996199479582301432653067)
                ·
                  refine ⟨5994299219373452148979601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996199479582301432653067 5994299219373452148979601)
                  ·
                    refine ⟨4495724414530089111734701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5994299219373452148979601 4495724414530089111734701)
                    ·
                      refine ⟨1685896655448783416900513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4495724414530089111734701 1685896655448783416900513)
                      ·
                        rfl

theorem cell23_3283272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_3283272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283272 prefixEnd_3283272 := by exact prefixLift 3283272
  have htrace : WordTrace (prefixWord ++ tailWord_3283272) baseStart_3283272 baseEnd_3283272 := by
    simpa [prefixWord, tailWord_3283272, baseEnd_3283272] using wordTrace_append hprefix tailTrace_3283272
  have hstable : (prefixWord ++ tailWord_3283272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283272).length < 2 ^ (prefixWord ++ tailWord_3283272).sum := by decide
  have hdescent : baseEnd_3283272 < baseStart_3283272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283292 : List Nat := [2, 2, 4, 3, 2, 10]
def baseStart_3283292 : Nat := 118140960795 + 3283292 * 2 ^ 59
def prefixEnd_3283292 : Nat := 4983230072969 + 3 ^ 40 * 3283292 * 2
def baseEnd_3283292 : Nat := 6937888580501536373047

theorem tailTrace_3283292 : CollatzResearch.WordTrace tailWord_3283292 prefixEnd_3283292 6937888580501536373047 := by
  unfold tailWord_3283292
  simp only [CollatzResearch.WordTrace]
  refine ⟨59875748610600650237894065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79834331480800866983858753 59875748610600650237894065)
  ·
    refine ⟨44906811457950487678420549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59875748610600650237894065 44906811457950487678420549)
    ·
      refine ⟨8420027148365716439703853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44906811457950487678420549 8420027148365716439703853)
      ·
        refine ⟨3157510180637143664888945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8420027148365716439703853 3157510180637143664888945)
        ·
          refine ⟨2368132635477857748666709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3157510180637143664888945 2368132635477857748666709)
          ·
            refine ⟨6937888580501536373047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2368132635477857748666709 6937888580501536373047)
            ·
              rfl

theorem cell23_3283292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 10].length) (baseStart_3283292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283292 prefixEnd_3283292 := by exact prefixLift 3283292
  have htrace : WordTrace (prefixWord ++ tailWord_3283292) baseStart_3283292 baseEnd_3283292 := by
    simpa [prefixWord, tailWord_3283292, baseEnd_3283292] using wordTrace_append hprefix tailTrace_3283292
  have hstable : (prefixWord ++ tailWord_3283292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283292).length < 2 ^ (prefixWord ++ tailWord_3283292).sum := by decide
  have hdescent : baseEnd_3283292 < baseStart_3283292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283303 : List Nat := [1, 1, 5, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_3283303 : Nat := 118140960795 + 3283303 * 2 ^ 59
def prefixEnd_3283303 : Nat := 4983230072969 + 3 ^ 40 * 3283303 * 2
def baseEnd_3283303 : Nat := 1685912573349072795612871

theorem tailTrace_3283303 : CollatzResearch.WordTrace tailWord_3283303 prefixEnd_3283303 1685912573349072795612871 := by
  unfold tailWord_3283303
  simp only [CollatzResearch.WordTrace]
  refine ⟨119751898424161449354438563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79834598949440966236292375 119751898424161449354438563)
  ·
    refine ⟨179627847636242174031657845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119751898424161449354438563 179627847636242174031657845)
    ·
      refine ⟨16840110715897703815467923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179627847636242174031657845 16840110715897703815467923)
      ·
        refine ⟨25260166073846555723201885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16840110715897703815467923 25260166073846555723201885)
        ·
          refine ⟨9472562277692458396200707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25260166073846555723201885 9472562277692458396200707)
          ·
            refine ⟨14208843416538687594301061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9472562277692458396200707 14208843416538687594301061)
            ·
              refine ⟨2664158140601003923931449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14208843416538687594301061 2664158140601003923931449)
              ·
                refine ⟨1998118605450752942948587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664158140601003923931449 1998118605450752942948587)
                ·
                  refine ⟨2997177908176129414422881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998118605450752942948587 2997177908176129414422881)
                  ·
                    refine ⟨2247883431132097060817161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2997177908176129414422881 2247883431132097060817161)
                    ·
                      refine ⟨1685912573349072795612871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247883431132097060817161 1685912573349072795612871)
                      ·
                        rfl

theorem cell23_3283303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_3283303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283303 prefixEnd_3283303 := by exact prefixLift 3283303
  have htrace : WordTrace (prefixWord ++ tailWord_3283303) baseStart_3283303 baseEnd_3283303 := by
    simpa [prefixWord, tailWord_3283303, baseEnd_3283303] using wordTrace_append hprefix tailTrace_3283303
  have hstable : (prefixWord ++ tailWord_3283303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283303).length < 2 ^ (prefixWord ++ tailWord_3283303).sum := by decide
  have hdescent : baseEnd_3283303 < baseStart_3283303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283312 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 3, 3, 2]
def baseStart_3283312 : Nat := 118140960795 + 3283312 * 2 ^ 59
def prefixEnd_3283312 : Nat := 4983230072969 + 3 ^ 40 * 3283312 * 2
def baseEnd_3283312 : Nat := 1685917194674963260400329

theorem tailTrace_3283312 : CollatzResearch.WordTrace tailWord_3283312 prefixEnd_3283312 1685917194674963260400329 := by
  unfold tailWord_3283312
  simp only [CollatzResearch.WordTrace]
  refine ⟨59876113340564421945758095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79834817787419229261010793 59876113340564421945758095)
  ·
    refine ⟨89814170010846632918637143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59876113340564421945758095 89814170010846632918637143)
    ·
      refine ⟨134721255016269949377955715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89814170010846632918637143 134721255016269949377955715)
      ·
        refine ⟨202081882524404924066933573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134721255016269949377955715 202081882524404924066933573)
        ·
          refine ⟨37890352973325923262550045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202081882524404924066933573 37890352973325923262550045)
          ·
            refine ⟨14208882364997221223456267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37890352973325923262550045 14208882364997221223456267)
            ·
              refine ⟨21313323547495831835184401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14208882364997221223456267 21313323547495831835184401)
              ·
                refine ⟨15984992660621873876388301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21313323547495831835184401 15984992660621873876388301)
                ·
                  refine ⟨5994372247733202703645613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15984992660621873876388301 5994372247733202703645613)
                  ·
                    refine ⟨2247889592899951013867105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5994372247733202703645613 2247889592899951013867105)
                    ·
                      refine ⟨1685917194674963260400329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247889592899951013867105 1685917194674963260400329)
                      ·
                        rfl

theorem cell23_3283312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 3, 2].length) (baseStart_3283312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283312 prefixEnd_3283312 := by exact prefixLift 3283312
  have htrace : WordTrace (prefixWord ++ tailWord_3283312) baseStart_3283312 baseEnd_3283312 := by
    simpa [prefixWord, tailWord_3283312, baseEnd_3283312] using wordTrace_append hprefix tailTrace_3283312
  have hstable : (prefixWord ++ tailWord_3283312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283312).length < 2 ^ (prefixWord ++ tailWord_3283312).sum := by decide
  have hdescent : baseEnd_3283312 < baseStart_3283312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283329 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_3283329 : Nat := 118140960795 + 3283329 * 2 ^ 59
def prefixEnd_3283329 : Nat := 4983230072969 + 3 ^ 40 * 3283329 * 2
def baseEnd_3283329 : Nat := 1685925923846089693887751

theorem tailTrace_3283329 : CollatzResearch.WordTrace tailWord_3283329 prefixEnd_3283329 1685925923846089693887751 := by
  unfold tailWord_3283329
  simp only [CollatzResearch.WordTrace]
  refine ⟨119752846722067255794885041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79835231148044837196590027 119752846722067255794885041)
  ·
    refine ⟨89814635041550441846163781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119752846722067255794885041 89814635041550441846163781)
    ·
      refine ⟨16840244070290707846155709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89814635041550441846163781 16840244070290707846155709)
      ·
        refine ⟨6315091526359015442308391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16840244070290707846155709 6315091526359015442308391)
        ·
          refine ⟨9472637289538523163462587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315091526359015442308391 9472637289538523163462587)
          ·
            refine ⟨14208955934307784745193881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9472637289538523163462587 14208955934307784745193881)
            ·
              refine ⟨10656716950730838558895411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14208955934307784745193881 10656716950730838558895411)
              ·
                refine ⟨15985075426096257838343117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10656716950730838558895411 15985075426096257838343117)
                ·
                  refine ⟨5994403284786096689378669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15985075426096257838343117 5994403284786096689378669)
                  ·
                    refine ⟨2247901231794786258517001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5994403284786096689378669 2247901231794786258517001)
                    ·
                      refine ⟨1685925923846089693887751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247901231794786258517001 1685925923846089693887751)
                      ·
                        rfl

theorem cell23_3283329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_3283329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283329 prefixEnd_3283329 := by exact prefixLift 3283329
  have htrace : WordTrace (prefixWord ++ tailWord_3283329) baseStart_3283329 baseEnd_3283329 := by
    simpa [prefixWord, tailWord_3283329, baseEnd_3283329] using wordTrace_append hprefix tailTrace_3283329
  have hstable : (prefixWord ++ tailWord_3283329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283329).length < 2 ^ (prefixWord ++ tailWord_3283329).sum := by decide
  have hdescent : baseEnd_3283329 < baseStart_3283329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283359 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 4, 2, 2]
def baseStart_3283359 : Nat := 118140960795 + 3283359 * 2 ^ 59
def prefixEnd_3283359 : Nat := 4983230072969 + 3 ^ 40 * 3283359 * 2
def baseEnd_3283359 : Nat := 1685941328265724576512613

theorem tailTrace_3283359 : CollatzResearch.WordTrace tailWord_3283359 prefixEnd_3283359 1685941328265724576512613 := by
  unfold tailWord_3283359
  simp only [CollatzResearch.WordTrace]
  refine ⟨119753940911958570918477131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79835960607972380612318087 119753940911958570918477131)
  ·
    refine ⟨179630911367937856377715697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119753940911958570918477131 179630911367937856377715697)
    ·
      refine ⟨134723183525953392283286773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179630911367937856377715697 134723183525953392283286773)
      ·
        refine ⟨12630298455558130526558135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134723183525953392283286773 12630298455558130526558135)
        ·
          refine ⟨18945447683337195789837203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12630298455558130526558135 18945447683337195789837203)
          ·
            refine ⟨28418171525005793684755805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18945447683337195789837203 28418171525005793684755805)
            ·
              refine ⟨10656814321877172631783427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28418171525005793684755805 10656814321877172631783427)
              ·
                refine ⟨15985221482815758947675141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10656814321877172631783427 15985221482815758947675141)
                ·
                  refine ⟨2997229028027954802689089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15985221482815758947675141 2997229028027954802689089)
                  ·
                    refine ⟨2247921771020966102016817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2997229028027954802689089 2247921771020966102016817)
                    ·
                      refine ⟨1685941328265724576512613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247921771020966102016817 1685941328265724576512613)
                      ·
                        rfl

theorem cell23_3283359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_3283359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283359 prefixEnd_3283359 := by exact prefixLift 3283359
  have htrace : WordTrace (prefixWord ++ tailWord_3283359) baseStart_3283359 baseEnd_3283359 := by
    simpa [prefixWord, tailWord_3283359, baseEnd_3283359] using wordTrace_append hprefix tailTrace_3283359
  have hstable : (prefixWord ++ tailWord_3283359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283359).length < 2 ^ (prefixWord ++ tailWord_3283359).sum := by decide
  have hdescent : baseEnd_3283359 < baseStart_3283359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283365 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 7]
def baseStart_3283365 : Nat := 118140960795 + 3283365 * 2 ^ 59
def prefixEnd_3283365 : Nat := 4983230072969 + 3 ^ 40 * 3283365 * 2
def baseEnd_3283365 : Nat := 187327156572183505893065

theorem tailTrace_3283365 : CollatzResearch.WordTrace tailWord_3283365 prefixEnd_3283365 187327156572183505893065 := by
  unfold tailWord_3283365
  simp only [CollatzResearch.WordTrace]
  refine ⟨119754159749936833943195549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79836106499957889295463699 119754159749936833943195549)
  ·
    refine ⟨44907809906226312728698331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119754159749936833943195549 44907809906226312728698331)
    ·
      refine ⟨67361714859339469093047497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44907809906226312728698331 67361714859339469093047497)
      ·
        refine ⟨50521286144504601819785623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67361714859339469093047497 50521286144504601819785623)
        ·
          refine ⟨75781929216756902729678435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50521286144504601819785623 75781929216756902729678435)
          ·
            refine ⟨113672893825135354094517653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75781929216756902729678435 113672893825135354094517653)
            ·
              refine ⟨5328416898053219723180515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113672893825135354094517653 5328416898053219723180515)
              ·
                refine ⟨7992625347079829584770773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328416898053219723180515 7992625347079829584770773)
                ·
                  refine ⟨187327156572183505893065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7992625347079829584770773 187327156572183505893065)
                  ·
                    rfl

theorem cell23_3283365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_3283365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283365 prefixEnd_3283365 := by exact prefixLift 3283365
  have htrace : WordTrace (prefixWord ++ tailWord_3283365) baseStart_3283365 baseEnd_3283365 := by
    simpa [prefixWord, tailWord_3283365, baseEnd_3283365] using wordTrace_append hprefix tailTrace_3283365
  have hstable : (prefixWord ++ tailWord_3283365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283365).length < 2 ^ (prefixWord ++ tailWord_3283365).sum := by decide
  have hdescent : baseEnd_3283365 < baseStart_3283365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283370 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3283370 : Nat := 118140960795 + 3283370 * 2 ^ 59
def prefixEnd_3283370 : Nat := 4983230072969 + 3 ^ 40 * 3283370 * 2
def baseEnd_3283370 : Nat := 1685946976552924033475063

theorem tailTrace_3283370 : CollatzResearch.WordTrace tailWord_3283370 prefixEnd_3283370 1685946976552924033475063 := by
  unfold tailWord_3283370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29938585528729679949281891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79836228076612479864751709 29938585528729679949281891)
  ·
    refine ⟨44907878293094519923922837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29938585528729679949281891 44907878293094519923922837)
    ·
      refine ⟨2105056794988805621433883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44907878293094519923922837 2105056794988805621433883)
      ·
        refine ⟨3157585192483208432150825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105056794988805621433883 3157585192483208432150825)
        ·
          refine ⟨2368188894362406324113119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3157585192483208432150825 2368188894362406324113119)
          ·
            refine ⟨3552283341543609486169679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368188894362406324113119 3552283341543609486169679)
            ·
              refine ⟨5328425012315414229254519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552283341543609486169679 5328425012315414229254519)
              ·
                refine ⟨7992637518473121343881779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328425012315414229254519 7992637518473121343881779)
                ·
                  refine ⟨11988956277709682015822669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7992637518473121343881779 11988956277709682015822669)
                  ·
                    refine ⟨4495858604141130755933501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11988956277709682015822669 4495858604141130755933501)
                    ·
                      refine ⟨1685946976552924033475063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4495858604141130755933501 1685946976552924033475063)
                      ·
                        rfl

theorem cell23_3283370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3283370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283370 prefixEnd_3283370 := by exact prefixLift 3283370
  have htrace : WordTrace (prefixWord ++ tailWord_3283370) baseStart_3283370 baseEnd_3283370 := by
    simpa [prefixWord, tailWord_3283370, baseEnd_3283370] using wordTrace_append hprefix tailTrace_3283370
  have hstable : (prefixWord ++ tailWord_3283370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283370).length < 2 ^ (prefixWord ++ tailWord_3283370).sum := by decide
  have hdescent : baseEnd_3283370 < baseStart_3283370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283380 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3283380 : Nat := 118140960795 + 3283380 * 2 ^ 59
def prefixEnd_3283380 : Nat := 4983230072969 + 3 ^ 40 * 3283380 * 2
def baseEnd_3283380 : Nat := 1685952111359468994350017

theorem tailTrace_3283380 : CollatzResearch.WordTrace tailWord_3283380 prefixEnd_3283380 1685952111359468994350017 := by
  unfold tailWord_3283380
  simp only [CollatzResearch.WordTrace]
  refine ⟨59877353422441245752495797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79836471229921661003327729 59877353422441245752495797)
  ·
    refine ⟨5613501883353866789296481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59877353422441245752495797 5613501883353866789296481)
    ·
      refine ⟨4210126412515400091972361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5613501883353866789296481 4210126412515400091972361)
      ·
        refine ⟨3157594809386550068979271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4210126412515400091972361 3157594809386550068979271)
        ·
          refine ⟨4736392214079825103468907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157594809386550068979271 4736392214079825103468907)
          ·
            refine ⟨7104588321119737655203361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736392214079825103468907 7104588321119737655203361)
            ·
              refine ⟨5328441240839803241402521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104588321119737655203361 5328441240839803241402521)
              ·
                refine ⟨3996330930629852431051891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328441240839803241402521 3996330930629852431051891)
                ·
                  refine ⟨5994496395944778646577837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996330930629852431051891 5994496395944778646577837)
                  ·
                    refine ⟨2247936148479291992466689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5994496395944778646577837 2247936148479291992466689)
                    ·
                      refine ⟨1685952111359468994350017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2247936148479291992466689 1685952111359468994350017)
                      ·
                        rfl

theorem cell23_3283380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3283380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283380 prefixEnd_3283380 := by exact prefixLift 3283380
  have htrace : WordTrace (prefixWord ++ tailWord_3283380) baseStart_3283380 baseEnd_3283380 := by
    simpa [prefixWord, tailWord_3283380, baseEnd_3283380] using wordTrace_append hprefix tailTrace_3283380
  have hstable : (prefixWord ++ tailWord_3283380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283380).length < 2 ^ (prefixWord ++ tailWord_3283380).sum := by decide
  have hdescent : baseEnd_3283380 < baseStart_3283380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283395 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 2, 5]
def baseStart_3283395 : Nat := 118140960795 + 3283395 * 2 ^ 59
def prefixEnd_3283395 : Nat := 4983230072969 + 3 ^ 40 * 3283395 * 2
def baseEnd_3283395 : Nat := 561986604523095478554149

theorem tailTrace_3283395 : CollatzResearch.WordTrace tailWord_3283395 prefixEnd_3283395 561986604523095478554149 := by
  unfold tailWord_3283395
  simp only [CollatzResearch.WordTrace]
  refine ⟨119755253939828149066787639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79836835959885432711191759 119755253939828149066787639)
  ·
    refine ⟨179632880909742223600181459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119755253939828149066787639 179632880909742223600181459)
    ·
      refine ⟨269449321364613335400272189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179632880909742223600181459 269449321364613335400272189)
      ·
        refine ⟨101043495511730000775102071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269449321364613335400272189 101043495511730000775102071)
        ·
          refine ⟨151565243267595001162653107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101043495511730000775102071 151565243267595001162653107)
          ·
            refine ⟨227347864901392501743979661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151565243267595001162653107 227347864901392501743979661)
            ·
              refine ⟨85255449338022188153992373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227347864901392501743979661 85255449338022188153992373)
              ·
                refine ⟨7992698375439580139436785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85255449338022188153992373 7992698375439580139436785)
                ·
                  refine ⟨5994523781579685104577589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7992698375439580139436785 5994523781579685104577589)
                  ·
                    refine ⟨561986604523095478554149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5994523781579685104577589 561986604523095478554149)
                    ·
                      rfl

theorem cell23_3283395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 5].length) (baseStart_3283395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283395 prefixEnd_3283395 := by exact prefixLift 3283395
  have htrace : WordTrace (prefixWord ++ tailWord_3283395) baseStart_3283395 baseEnd_3283395 := by
    simpa [prefixWord, tailWord_3283395, baseEnd_3283395] using wordTrace_append hprefix tailTrace_3283395
  have hstable : (prefixWord ++ tailWord_3283395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283395).length < 2 ^ (prefixWord ++ tailWord_3283395).sum := by decide
  have hdescent : baseEnd_3283395 < baseStart_3283395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283399 : List Nat := [1, 1, 4, 1, 1, 6, 1, 3, 5]
def baseStart_3283399 : Nat := 118140960795 + 3283399 * 2 ^ 59
def prefixEnd_3283399 : Nat := 4983230072969 + 3 ^ 40 * 3283399 * 2
def baseEnd_3283399 : Nat := 187329096387989380001381

theorem tailTrace_3283399 : CollatzResearch.WordTrace tailWord_3283399 prefixEnd_3283399 187329096387989380001381 := by
  unfold tailWord_3283399
  simp only [CollatzResearch.WordTrace]
  refine ⟨119755399831813657749933251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79836933221209105166622167 119755399831813657749933251)
  ·
    refine ⟨179633099747720486624899877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119755399831813657749933251 179633099747720486624899877)
    ·
      refine ⟨33681206202697591242168727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179633099747720486624899877 33681206202697591242168727)
      ·
        refine ⟨50521809304046386863253091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33681206202697591242168727 50521809304046386863253091)
        ·
          refine ⟨75782713956069580294879637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50521809304046386863253091 75782713956069580294879637)
          ·
            refine ⟨3552314716690761576322483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75782713956069580294879637 3552314716690761576322483)
            ·
              refine ⟨5328472075036142364483725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552314716690761576322483 5328472075036142364483725)
              ·
                refine ⟨1998177028138553386681397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5328472075036142364483725 1998177028138553386681397)
                ·
                  refine ⟨187329096387989380001381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998177028138553386681397 187329096387989380001381)
                  ·
                    rfl

theorem cell23_3283399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 5].length) (baseStart_3283399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283399 prefixEnd_3283399 := by exact prefixLift 3283399
  have htrace : WordTrace (prefixWord ++ tailWord_3283399) baseStart_3283399 baseEnd_3283399 := by
    simpa [prefixWord, tailWord_3283399, baseEnd_3283399] using wordTrace_append hprefix tailTrace_3283399
  have hstable : (prefixWord ++ tailWord_3283399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283399).length < 2 ^ (prefixWord ++ tailWord_3283399).sum := by decide
  have hdescent : baseEnd_3283399 < baseStart_3283399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283412 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3283412 : Nat := 118140960795 + 3283412 * 2 ^ 59
def prefixEnd_3283412 : Nat := 4983230072969 + 3 ^ 40 * 3283412 * 2
def baseEnd_3283412 : Nat := 561989514246804289716623

theorem tailTrace_3283412 : CollatzResearch.WordTrace tailWord_3283412 prefixEnd_3283412 561989514246804289716623 := by
  unfold tailWord_3283412
  simp only [CollatzResearch.WordTrace]
  refine ⟨59877936990383280485078245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79837249320511040646770993 59877936990383280485078245)
  ·
    refine ⟨11227113185696865090952171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59877936990383280485078245 11227113185696865090952171)
    ·
      refine ⟨16840669778545297636428257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11227113185696865090952171 16840669778545297636428257)
      ·
        refine ⟨12630502333908973227321193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16840669778545297636428257 12630502333908973227321193)
        ·
          refine ⟨9472876750431729920490895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12630502333908973227321193 9472876750431729920490895)
          ·
            refine ⟨14209315125647594880736343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9472876750431729920490895 14209315125647594880736343)
            ·
              refine ⟨21313972688471392321104515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14209315125647594880736343 21313972688471392321104515)
              ·
                refine ⟨31970959032707088481656773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21313972688471392321104515 31970959032707088481656773)
                ·
                  refine ⟨5994554818632579090310645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31970959032707088481656773 5994554818632579090310645)
                  ·
                    refine ⟨561989514246804289716623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5994554818632579090310645 561989514246804289716623)
                    ·
                      rfl

theorem cell23_3283412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3283412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283412 prefixEnd_3283412 := by exact prefixLift 3283412
  have htrace : WordTrace (prefixWord ++ tailWord_3283412) baseStart_3283412 baseEnd_3283412 := by
    simpa [prefixWord, tailWord_3283412, baseEnd_3283412] using wordTrace_append hprefix tailTrace_3283412
  have hstable : (prefixWord ++ tailWord_3283412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283412).length < 2 ^ (prefixWord ++ tailWord_3283412).sum := by decide
  have hdescent : baseEnd_3283412 < baseStart_3283412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283459 : List Nat := [1, 1, 1, 3, 2, 1, 4, 5, 1, 4]
def baseStart_3283459 : Nat := 118140960795 + 3283459 * 2 ^ 59
def prefixEnd_3283459 : Nat := 4983230072969 + 3 ^ 40 * 3283459 * 2
def baseEnd_3283459 : Nat := 561997558777058061754051

theorem tailTrace_3283459 : CollatzResearch.WordTrace tailWord_3283459 prefixEnd_3283459 561997558777058061754051 := by
  unfold tailWord_3283459
  simp only [CollatzResearch.WordTrace]
  refine ⟨119757588211596287997117431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79838392141064191998078287 119757588211596287997117431)
  ·
    refine ⟨179636382317394431995676147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119757588211596287997117431 179636382317394431995676147)
    ·
      refine ⟨269454573476091647993514221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179636382317394431995676147 269454573476091647993514221)
      ·
        refine ⟨101045465053534367997567833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269454573476091647993514221 101045465053534367997567833)
        ·
          refine ⟨75784098790150775998175875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101045465053534367997567833 75784098790150775998175875)
          ·
            refine ⟨113676148185226163997263813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75784098790150775998175875 113676148185226163997263813)
            ·
              refine ⟨21314277784729905749486965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113676148185226163997263813 21314277784729905749486965)
              ·
                refine ⟨1998213542318428664014403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21314277784729905749486965 1998213542318428664014403)
                ·
                  refine ⟨2997320313477642996021605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998213542318428664014403 2997320313477642996021605)
                  ·
                    refine ⟨561997558777058061754051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2997320313477642996021605 561997558777058061754051)
                    ·
                      rfl

theorem cell23_3283459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 4].length) (baseStart_3283459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283459 prefixEnd_3283459 := by exact prefixLift 3283459
  have htrace : WordTrace (prefixWord ++ tailWord_3283459) baseStart_3283459 baseEnd_3283459 := by
    simpa [prefixWord, tailWord_3283459, baseEnd_3283459] using wordTrace_append hprefix tailTrace_3283459
  have hstable : (prefixWord ++ tailWord_3283459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283459).length < 2 ^ (prefixWord ++ tailWord_3283459).sum := by decide
  have hdescent : baseEnd_3283459 < baseStart_3283459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283475 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6]
def baseStart_3283475 : Nat := 118140960795 + 3283475 * 2 ^ 59
def prefixEnd_3283475 : Nat := 4983230072969 + 3 ^ 40 * 3283475 * 2
def baseEnd_3283475 : Nat := 1686000892021646122662079

theorem tailTrace_3283475 : CollatzResearch.WordTrace tailWord_3283475 prefixEnd_3283475 1686000892021646122662079 := by
  unfold tailWord_3283475
  simp only [CollatzResearch.WordTrace]
  refine ⟨119758171779538322729699879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79838781186358881819799919 119758171779538322729699879)
  ·
    refine ⟨179637257669307484094549819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119758171779538322729699879 179637257669307484094549819)
    ·
      refine ⟨269455886503961226141824729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179637257669307484094549819 269455886503961226141824729)
      ·
        refine ⟨202091914877970919606368547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269455886503961226141824729 202091914877970919606368547)
        ·
          refine ⟨303137872316956379409552821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202091914877970919606368547 303137872316956379409552821)
          ·
            refine ⟨28419175529714660569645577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303137872316956379409552821 28419175529714660569645577)
            ·
              refine ⟨21314381647285995427234183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28419175529714660569645577 21314381647285995427234183)
              ·
                refine ⟨31971572470928993140851275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21314381647285995427234183 31971572470928993140851275)
                ·
                  refine ⟨47957358706393489711276913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31971572470928993140851275 47957358706393489711276913)
                  ·
                    refine ⟨35968019029795117283457685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47957358706393489711276913 35968019029795117283457685)
                    ·
                      refine ⟨1686000892021646122662079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35968019029795117283457685 1686000892021646122662079)
                      ·
                        rfl

theorem cell23_3283475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_3283475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283475 prefixEnd_3283475 := by exact prefixLift 3283475
  have htrace : WordTrace (prefixWord ++ tailWord_3283475) baseStart_3283475 baseEnd_3283475 := by
    simpa [prefixWord, tailWord_3283475, baseEnd_3283475] using wordTrace_append hprefix tailTrace_3283475
  have hstable : (prefixWord ++ tailWord_3283475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283475).length < 2 ^ (prefixWord ++ tailWord_3283475).sum := by decide
  have hdescent : baseEnd_3283475 < baseStart_3283475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283509 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_3283509 : Nat := 118140960795 + 3283509 * 2 ^ 59
def prefixEnd_3283509 : Nat := 4983230072969 + 3 ^ 40 * 3283509 * 2
def baseEnd_3283509 : Nat := 1686018350363898989636923

theorem tailTrace_3283509 : CollatzResearch.WordTrace tailWord_3283509 prefixEnd_3283509 1686018350363898989636923 := by
  unfold tailWord_3283509
  simp only [CollatzResearch.WordTrace]
  refine ⟨119759411861415146536437581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79839607907610097690958387 119759411861415146536437581)
  ·
    refine ⟨44909779448030679951164093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119759411861415146536437581 44909779448030679951164093)
    ·
      refine ⟨16841167293011504981686535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44909779448030679951164093 16841167293011504981686535)
      ·
        refine ⟨25261750939517257472529803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16841167293011504981686535 25261750939517257472529803)
        ·
          refine ⟨37892626409275886208794705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25261750939517257472529803 37892626409275886208794705)
          ·
            refine ⟨28419469806956914656596029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37892626409275886208794705 28419469806956914656596029)
            ·
              refine ⟨10657301177608842996223511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28419469806956914656596029 10657301177608842996223511)
              ·
                refine ⟨15985951766413264494335267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10657301177608842996223511 15985951766413264494335267)
                ·
                  refine ⟨23978927649619896741502901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15985951766413264494335267 23978927649619896741502901)
                  ·
                    refine ⟨2248024467151865319515897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23978927649619896741502901 2248024467151865319515897)
                    ·
                      refine ⟨1686018350363898989636923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248024467151865319515897 1686018350363898989636923)
                      ·
                        rfl

theorem cell23_3283509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_3283509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283509 prefixEnd_3283509 := by exact prefixLift 3283509
  have htrace : WordTrace (prefixWord ++ tailWord_3283509) baseStart_3283509 baseEnd_3283509 := by
    simpa [prefixWord, tailWord_3283509, baseEnd_3283509] using wordTrace_append hprefix tailTrace_3283509
  have hstable : (prefixWord ++ tailWord_3283509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283509).length < 2 ^ (prefixWord ++ tailWord_3283509).sum := by decide
  have hdescent : baseEnd_3283509 < baseStart_3283509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283515 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 7, 6]
def baseStart_3283515 : Nat := 118140960795 + 3283515 * 2 ^ 59
def prefixEnd_3283515 : Nat := 4983230072969 + 3 ^ 40 * 3283515 * 2
def baseEnd_3283515 : Nat := 562007143749275322053965

theorem tailTrace_3283515 : CollatzResearch.WordTrace tailWord_3283515 prefixEnd_3283515 562007143749275322053965 := by
  unfold tailWord_3283515
  simp only [CollatzResearch.WordTrace]
  refine ⟨119759630699393409561155999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79839753799595606374103999 119759630699393409561155999)
  ·
    refine ⟨179639446049090114341733999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119759630699393409561155999 179639446049090114341733999)
    ·
      refine ⟨269459169073635171512600999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179639446049090114341733999 269459169073635171512600999)
      ·
        refine ⟨404188753610452757268901499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269459169073635171512600999 404188753610452757268901499)
        ·
          refine ⟨606283130415679135903352249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404188753610452757268901499 606283130415679135903352249)
          ·
            refine ⟨454712347811759351927514187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606283130415679135903352249 454712347811759351927514187)
            ·
              refine ⟨682068521717639027891271281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454712347811759351927514187 682068521717639027891271281)
              ·
                refine ⟨511551391288229270918453461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682068521717639027891271281 511551391288229270918453461)
                ·
                  refine ⟨11989485733317873537151253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 511551391288229270918453461 11989485733317873537151253)
                  ·
                    refine ⟨562007143749275322053965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11989485733317873537151253 562007143749275322053965)
                    ·
                      rfl

theorem cell23_3283515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 6].length) (baseStart_3283515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283515 prefixEnd_3283515 := by exact prefixLift 3283515
  have htrace : WordTrace (prefixWord ++ tailWord_3283515) baseStart_3283515 baseEnd_3283515 := by
    simpa [prefixWord, tailWord_3283515, baseEnd_3283515] using wordTrace_append hprefix tailTrace_3283515
  have hstable : (prefixWord ++ tailWord_3283515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283515).length < 2 ^ (prefixWord ++ tailWord_3283515).sum := by decide
  have hdescent : baseEnd_3283515 < baseStart_3283515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283533 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3283533 : Nat := 118140960795 + 3283533 * 2 ^ 59
def prefixEnd_3283533 : Nat := 4983230072969 + 3 ^ 40 * 3283533 * 2
def baseEnd_3283533 : Nat := 1686030673899606895736813

theorem tailTrace_3283533 : CollatzResearch.WordTrace tailWord_3283533 prefixEnd_3283533 1686030673899606895736813 := by
  unfold tailWord_3283533
  simp only [CollatzResearch.WordTrace]
  refine ⟨119760287213328198635311253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79840191475552132423540835 119760287213328198635311253)
  ·
    refine ⟨5613763463124759311030215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119760287213328198635311253 5613763463124759311030215)
    ·
      refine ⟨8420645194687138966545323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5613763463124759311030215 8420645194687138966545323)
      ·
        refine ⟨12630967792030708449817985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8420645194687138966545323 12630967792030708449817985)
        ·
          refine ⟨9473225844023031337363489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12630967792030708449817985 9473225844023031337363489)
          ·
            refine ⟨7104919383017273503022617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9473225844023031337363489 7104919383017273503022617)
            ·
              refine ⟨5328689537262955127266963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104919383017273503022617 5328689537262955127266963)
              ·
                refine ⟨7993034305894432690900445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328689537262955127266963 7993034305894432690900445)
                ·
                  refine ⟨2997387864710412259087667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7993034305894432690900445 2997387864710412259087667)
                  ·
                    refine ⟨4496081797065618388631501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2997387864710412259087667 4496081797065618388631501)
                    ·
                      refine ⟨1686030673899606895736813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4496081797065618388631501 1686030673899606895736813)
                      ·
                        rfl

theorem cell23_3283533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3283533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283533 prefixEnd_3283533 := by exact prefixLift 3283533
  have htrace : WordTrace (prefixWord ++ tailWord_3283533) baseStart_3283533 baseEnd_3283533 := by
    simpa [prefixWord, tailWord_3283533, baseEnd_3283533] using wordTrace_append hprefix tailTrace_3283533
  have hstable : (prefixWord ++ tailWord_3283533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283533).length < 2 ^ (prefixWord ++ tailWord_3283533).sum := by decide
  have hdescent : baseEnd_3283533 < baseStart_3283533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283556 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_3283556 : Nat := 118140960795 + 3283556 * 2 ^ 59
def prefixEnd_3283556 : Nat := 4983230072969 + 3 ^ 40 * 3283556 * 2
def baseEnd_3283556 : Nat := 1686042483954660305749207

theorem tailTrace_3283556 : CollatzResearch.WordTrace tailWord_3283556 prefixEnd_3283556 1686042483954660305749207 := by
  unfold tailWord_3283556
  simp only [CollatzResearch.WordTrace]
  refine ⟨59880563046122436781699261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79840750728163249042265681 59880563046122436781699261)
  ·
    refine ⟨22455211142295913793137223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59880563046122436781699261 22455211142295913793137223)
    ·
      refine ⟨33682816713443870689705835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22455211142295913793137223 33682816713443870689705835)
      ·
        refine ⟨50524225070165806034558753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33682816713443870689705835 50524225070165806034558753)
        ·
          refine ⟨37893168802624354525919065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50524225070165806034558753 37893168802624354525919065)
          ·
            refine ⟨28419876601968265894439299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37893168802624354525919065 28419876601968265894439299)
            ·
              refine ⟨42629814902952398841658949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28419876601968265894439299 42629814902952398841658949)
              ·
                refine ⟨7993090294303574782811053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42629814902952398841658949 7993090294303574782811053)
                ·
                  refine ⟨2997408860363840543554145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7993090294303574782811053 2997408860363840543554145)
                  ·
                    refine ⟨2248056645272880407665609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2997408860363840543554145 2248056645272880407665609)
                    ·
                      refine ⟨1686042483954660305749207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248056645272880407665609 1686042483954660305749207)
                      ·
                        rfl

theorem cell23_3283556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_3283556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283556 prefixEnd_3283556 := by exact prefixLift 3283556
  have htrace : WordTrace (prefixWord ++ tailWord_3283556) baseStart_3283556 baseEnd_3283556 := by
    simpa [prefixWord, tailWord_3283556, baseEnd_3283556] using wordTrace_append hprefix tailTrace_3283556
  have hstable : (prefixWord ++ tailWord_3283556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283556).length < 2 ^ (prefixWord ++ tailWord_3283556).sum := by decide
  have hdescent : baseEnd_3283556 < baseStart_3283556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283562 : List Nat := [3, 1, 3, 2, 1, 1, 3, 9]
def baseStart_3283562 : Nat := 118140960795 + 3283562 * 2 ^ 59
def prefixEnd_3283562 : Nat := 4983230072969 + 3 ^ 40 * 3283562 * 2
def baseEnd_3283562 : Nat := 62446132031058788232377

theorem tailTrace_3283562 : CollatzResearch.WordTrace tailWord_3283562 prefixEnd_3283562 62446132031058788232377 := by
  unfold tailWord_3283562
  simp only [CollatzResearch.WordTrace]
  refine ⟨29940336232555784147029235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79840896620148757725411293 29940336232555784147029235)
  ·
    refine ⟨44910504348833676220543853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29940336232555784147029235 44910504348833676220543853)
    ·
      refine ⟨16841439130812628582703945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44910504348833676220543853 16841439130812628582703945)
      ·
        refine ⟨12631079348109471437027959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16841439130812628582703945 12631079348109471437027959)
        ·
          refine ⟨18946619022164207155541939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12631079348109471437027959 18946619022164207155541939)
          ·
            refine ⟨28419928533246310733312909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18946619022164207155541939 28419928533246310733312909)
            ·
              refine ⟨10657473199967366524992341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28419928533246310733312909 10657473199967366524992341)
              ·
                refine ⟨62446132031058788232377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10657473199967366524992341 62446132031058788232377)
                ·
                  rfl

theorem cell23_3283562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_3283562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283562 prefixEnd_3283562 := by exact prefixLift 3283562
  have htrace : WordTrace (prefixWord ++ tailWord_3283562) baseStart_3283562 baseEnd_3283562 := by
    simpa [prefixWord, tailWord_3283562, baseEnd_3283562] using wordTrace_append hprefix tailTrace_3283562
  have hstable : (prefixWord ++ tailWord_3283562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283562).length < 2 ^ (prefixWord ++ tailWord_3283562).sum := by decide
  have hdescent : baseEnd_3283562 < baseStart_3283562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283599 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 5, 3, 2]
def baseStart_3283599 : Nat := 118140960795 + 3283599 * 2 ^ 59
def prefixEnd_3283599 : Nat := 4983230072969 + 3 ^ 40 * 3283599 * 2
def baseEnd_3283599 : Nat := 1686064563622803637511509

theorem tailTrace_3283599 : CollatzResearch.WordTrace tailWord_3283599 prefixEnd_3283599 1686064563622803637511509 := by
  unfold tailWord_3283599
  simp only [CollatzResearch.WordTrace]
  refine ⟨119762694431089091907213851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79841796287392727938142567 119762694431089091907213851)
  ·
    refine ⟨179644041646633637860820777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119762694431089091907213851 179644041646633637860820777)
    ·
      refine ⟨134733031234975228395615583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179644041646633637860820777 134733031234975228395615583)
      ·
        refine ⟨202099546852462842593423375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134733031234975228395615583 202099546852462842593423375)
        ·
          refine ⟨303149320278694263890135063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202099546852462842593423375 303149320278694263890135063)
          ·
            refine ⟨454723980418041395835202595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303149320278694263890135063 454723980418041395835202595)
            ·
              refine ⟨682085970627062093752803893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454723980418041395835202595 682085970627062093752803893)
              ·
                refine ⟨63945559746287071289325365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 682085970627062093752803893 63945559746287071289325365)
                ·
                  refine ⟨5994896226214412933374253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63945559746287071289325365 5994896226214412933374253)
                  ·
                    refine ⟨2248086084830404850015345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5994896226214412933374253 2248086084830404850015345)
                    ·
                      refine ⟨1686064563622803637511509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248086084830404850015345 1686064563622803637511509)
                      ·
                        rfl

theorem cell23_3283599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3, 2].length) (baseStart_3283599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283599 prefixEnd_3283599 := by exact prefixLift 3283599
  have htrace : WordTrace (prefixWord ++ tailWord_3283599) baseStart_3283599 baseEnd_3283599 := by
    simpa [prefixWord, tailWord_3283599, baseEnd_3283599] using wordTrace_append hprefix tailTrace_3283599
  have hstable : (prefixWord ++ tailWord_3283599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283599).length < 2 ^ (prefixWord ++ tailWord_3283599).sum := by decide
  have hdescent : baseEnd_3283599 < baseStart_3283599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283610 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3283610 : Nat := 118140960795 + 3283610 * 2 ^ 59
def prefixEnd_3283610 : Nat := 4983230072969 + 3 ^ 40 * 3283610 * 2
def baseEnd_3283610 : Nat := 1686070211910003094473959

theorem tailTrace_3283610 : CollatzResearch.WordTrace tailWord_3283610 prefixEnd_3283610 1686070211910003094473959 := by
  unfold tailWord_3283610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29940773908512310196466071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79842063756032827190576189 29940773908512310196466071)
  ·
    refine ⟨44911160862768465294699107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29940773908512310196466071 44911160862768465294699107)
    ·
      refine ⟨67366741294152697942048661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44911160862768465294699107 67366741294152697942048661)
      ·
        refine ⟨3157815998163407716033531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67366741294152697942048661 3157815998163407716033531)
        ·
          refine ⟨4736723997245111574050297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157815998163407716033531 4736723997245111574050297)
          ·
            refine ⟨3552542997933833680537723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4736723997245111574050297 3552542997933833680537723)
            ·
              refine ⟨5328814496900750520806585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552542997933833680537723 5328814496900750520806585)
              ·
                refine ⟨3996610872675562890604939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328814496900750520806585 3996610872675562890604939)
                ·
                  refine ⟨5994916309013344335907409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996610872675562890604939 5994916309013344335907409)
                  ·
                    refine ⟨4496187231760008251930557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5994916309013344335907409 4496187231760008251930557)
                    ·
                      refine ⟨1686070211910003094473959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4496187231760008251930557 1686070211910003094473959)
                      ·
                        rfl

theorem cell23_3283610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3283610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283610 prefixEnd_3283610 := by exact prefixLift 3283610
  have htrace : WordTrace (prefixWord ++ tailWord_3283610) baseStart_3283610 baseEnd_3283610 := by
    simpa [prefixWord, tailWord_3283610, baseEnd_3283610] using wordTrace_append hprefix tailTrace_3283610
  have hstable : (prefixWord ++ tailWord_3283610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283610).length < 2 ^ (prefixWord ++ tailWord_3283610).sum := by decide
  have hdescent : baseEnd_3283610 < baseStart_3283610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283623 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3283623 : Nat := 118140960795 + 3283623 * 2 ^ 59
def prefixEnd_3283623 : Nat := 4983230072969 + 3 ^ 40 * 3283623 * 2
def baseEnd_3283623 : Nat := 1686076887158511543611399

theorem tailTrace_3283623 : CollatzResearch.WordTrace tailWord_3283623 prefixEnd_3283623 1686076887158511543611399 := by
  unfold tailWord_3283623
  simp only [CollatzResearch.WordTrace]
  refine ⟨119763569783002144006087523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79842379855334762670725015 119763569783002144006087523)
  ·
    refine ⟨179645354674503216009131285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119763569783002144006087523 179645354674503216009131285)
    ·
      refine ⟨8420876000367338250428029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179645354674503216009131285 8420876000367338250428029)
      ·
        refine ⟨3157828500137751843910511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8420876000367338250428029 3157828500137751843910511)
        ·
          refine ⟨4736742750206627765865767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157828500137751843910511 4736742750206627765865767)
          ·
            refine ⟨7105114125309941648798651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736742750206627765865767 7105114125309941648798651)
            ·
              refine ⟨10657671187964912473197977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7105114125309941648798651 10657671187964912473197977)
              ·
                refine ⟨7993253390973684354898483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10657671187964912473197977 7993253390973684354898483)
                ·
                  refine ⟨11989880086460526532347725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993253390973684354898483 11989880086460526532347725)
                  ·
                    refine ⟨4496205032422697449630397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11989880086460526532347725 4496205032422697449630397)
                    ·
                      refine ⟨1686076887158511543611399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4496205032422697449630397 1686076887158511543611399)
                      ·
                        rfl

theorem cell23_3283623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3283623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283623 prefixEnd_3283623 := by exact prefixLift 3283623
  have htrace : WordTrace (prefixWord ++ tailWord_3283623) baseStart_3283623 baseEnd_3283623 := by
    simpa [prefixWord, tailWord_3283623, baseEnd_3283623] using wordTrace_append hprefix tailTrace_3283623
  have hstable : (prefixWord ++ tailWord_3283623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283623).length < 2 ^ (prefixWord ++ tailWord_3283623).sum := by decide
  have hdescent : baseEnd_3283623 < baseStart_3283623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283646 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_3283646 : Nat := 118140960795 + 3283646 * 2 ^ 59
def prefixEnd_3283646 : Nat := 4983230072969 + 3 ^ 40 * 3283646 * 2
def baseEnd_3283646 : Nat := 1686088697213564953623793

theorem tailTrace_3283646 : CollatzResearch.WordTrace tailWord_3283646 prefixEnd_3283646 1686088697213564953623793 := by
  unfold tailWord_3283646
  simp only [CollatzResearch.WordTrace]
  refine ⟨14970551082739852366771849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79842939107945879289449861 14970551082739852366771849)
  ·
    refine ⟨11227913312054889275078887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14970551082739852366771849 11227913312054889275078887)
    ·
      refine ⟨16841869968082333912618331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11227913312054889275078887 16841869968082333912618331)
      ·
        refine ⟨25262804952123500868927497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16841869968082333912618331 25262804952123500868927497)
        ·
          refine ⟨18947103714092625651695623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25262804952123500868927497 18947103714092625651695623)
          ·
            refine ⟨28420655571138938477543435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18947103714092625651695623 28420655571138938477543435)
            ·
              refine ⟨42630983356708407716315153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28420655571138938477543435 42630983356708407716315153)
              ·
                refine ⟨31973237517531305787236365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42630983356708407716315153 31973237517531305787236365)
                ·
                  refine ⟨11989964069074239670213637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31973237517531305787236365 11989964069074239670213637)
                  ·
                    refine ⟨2248118262951419938165057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11989964069074239670213637 2248118262951419938165057)
                    ·
                      refine ⟨1686088697213564953623793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248118262951419938165057 1686088697213564953623793)
                      ·
                        rfl

theorem cell23_3283646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_3283646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283646 prefixEnd_3283646 := by exact prefixLift 3283646
  have htrace : WordTrace (prefixWord ++ tailWord_3283646) baseStart_3283646 baseEnd_3283646 := by
    simpa [prefixWord, tailWord_3283646, baseEnd_3283646] using wordTrace_append hprefix tailTrace_3283646
  have hstable : (prefixWord ++ tailWord_3283646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283646).length < 2 ^ (prefixWord ++ tailWord_3283646).sum := by decide
  have hdescent : baseEnd_3283646 < baseStart_3283646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283712 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 4, 8]
def baseStart_3283712 : Nat := 118140960795 + 3283712 * 2 ^ 59
def prefixEnd_3283712 : Nat := 4983230072969 + 3 ^ 40 * 3283712 * 2
def baseEnd_3283712 : Nat := 562040862312253898466163

theorem tailTrace_3283712 : CollatzResearch.WordTrace tailWord_3283712 prefixEnd_3283712 562040862312253898466163 := by
  unfold tailWord_3283712
  simp only [CollatzResearch.WordTrace]
  refine ⟨59883407939839856103038695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79844543919786474804051593 59883407939839856103038695)
  ·
    refine ⟨89825111909759784154558043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59883407939839856103038695 89825111909759784154558043)
    ·
      refine ⟨134737667864639676231837065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89825111909759784154558043 134737667864639676231837065)
      ·
        refine ⟨101053250898479757173877799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134737667864639676231837065 101053250898479757173877799)
        ·
          refine ⟨151579876347719635760816699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101053250898479757173877799 151579876347719635760816699)
          ·
            refine ⟨227369814521579453641225049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151579876347719635760816699 227369814521579453641225049)
            ·
              refine ⟨170527360891184590230918787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227369814521579453641225049 170527360891184590230918787)
              ·
                refine ⟨255791041336776885346378181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170527360891184590230918787 255791041336776885346378181)
                ·
                  refine ⟨47960820250645666002445909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255791041336776885346378181 47960820250645666002445909)
                  ·
                    refine ⟨562040862312253898466163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47960820250645666002445909 562040862312253898466163)
                    ·
                      rfl

theorem cell23_3283712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_3283712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283712 prefixEnd_3283712 := by exact prefixLift 3283712
  have htrace : WordTrace (prefixWord ++ tailWord_3283712) baseStart_3283712 baseEnd_3283712 := by
    simpa [prefixWord, tailWord_3283712, baseEnd_3283712] using wordTrace_append hprefix tailTrace_3283712
  have hstable : (prefixWord ++ tailWord_3283712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283712).length < 2 ^ (prefixWord ++ tailWord_3283712).sum := by decide
  have hdescent : baseEnd_3283712 < baseStart_3283712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283756 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_3283756 : Nat := 118140960795 + 3283756 * 2 ^ 59
def prefixEnd_3283756 : Nat := 4983230072969 + 3 ^ 40 * 3283756 * 2
def baseEnd_3283756 : Nat := 1686145180085559523248287

theorem tailTrace_3283756 : CollatzResearch.WordTrace tailWord_3283756 prefixEnd_3283756 1686145180085559523248287 := by
  unfold tailWord_3283756
  simp only [CollatzResearch.WordTrace]
  refine ⟨59884210345760153860339561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79845613794346871813786081 59884210345760153860339561)
  ·
    refine ⟨44913157759320115395254671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59884210345760153860339561 44913157759320115395254671)
    ·
      refine ⟨67369736638980173092882007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44913157759320115395254671 67369736638980173092882007)
      ·
        refine ⟨101054604958470259639323011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67369736638980173092882007 101054604958470259639323011)
        ·
          refine ⟨151581907437705389458984517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101054604958470259639323011 151581907437705389458984517)
          ·
            refine ⟨28421607644569760523559597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151581907437705389458984517 28421607644569760523559597)
            ·
              refine ⟨10658102866713660196334849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28421607644569760523559597 10658102866713660196334849)
              ·
                refine ⟨7993577150035245147251137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10658102866713660196334849 7993577150035245147251137)
                ·
                  refine ⟨5995182862526433860438353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993577150035245147251137 5995182862526433860438353)
                  ·
                    refine ⟨4496387146894825395328765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995182862526433860438353 4496387146894825395328765)
                    ·
                      refine ⟨1686145180085559523248287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4496387146894825395328765 1686145180085559523248287)
                      ·
                        rfl

theorem cell23_3283756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_3283756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283756 prefixEnd_3283756 := by exact prefixLift 3283756
  have htrace : WordTrace (prefixWord ++ tailWord_3283756) baseStart_3283756 baseEnd_3283756 := by
    simpa [prefixWord, tailWord_3283756, baseEnd_3283756] using wordTrace_append hprefix tailTrace_3283756
  have hstable : (prefixWord ++ tailWord_3283756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283756).length < 2 ^ (prefixWord ++ tailWord_3283756).sum := by decide
  have hdescent : baseEnd_3283756 < baseStart_3283756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283763 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 3, 4]
def baseStart_3283763 : Nat := 118140960795 + 3283763 * 2 ^ 59
def prefixEnd_3283763 : Nat := 4983230072969 + 3 ^ 40 * 3283763 * 2
def baseEnd_3283763 : Nat := 562049591483380331953585

theorem tailTrace_3283763 : CollatzResearch.WordTrace tailWord_3283763 prefixEnd_3283763 562049591483380331953585 := by
  unfold tailWord_3283763
  simp only [CollatzResearch.WordTrace]
  refine ⟨119768676002494947916183943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79845784001663298610789295 119768676002494947916183943)
  ·
    refine ⟨179653014003742421874275915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119768676002494947916183943 179653014003742421874275915)
    ·
      refine ⟨269479521005613632811413873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179653014003742421874275915 269479521005613632811413873)
      ·
        refine ⟨202109640754210224608560405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269479521005613632811413873 202109640754210224608560405)
        ·
          refine ⟨9473889410353604278526269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202109640754210224608560405 9473889410353604278526269)
          ·
            refine ⟨3552708528882601604447351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9473889410353604278526269 3552708528882601604447351)
            ·
              refine ⟨5329062793323902406671027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552708528882601604447351 5329062793323902406671027)
              ·
                refine ⟨7993594189985853610006541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329062793323902406671027 7993594189985853610006541)
                ·
                  refine ⟨2997597821244695103752453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7993594189985853610006541 2997597821244695103752453)
                  ·
                    refine ⟨562049591483380331953585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2997597821244695103752453 562049591483380331953585)
                    ·
                      rfl

theorem cell23_3283763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 4].length) (baseStart_3283763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283763 prefixEnd_3283763 := by exact prefixLift 3283763
  have htrace : WordTrace (prefixWord ++ tailWord_3283763) baseStart_3283763 baseEnd_3283763 := by
    simpa [prefixWord, tailWord_3283763, baseEnd_3283763] using wordTrace_append hprefix tailTrace_3283763
  have hstable : (prefixWord ++ tailWord_3283763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283763).length < 2 ^ (prefixWord ++ tailWord_3283763).sum := by decide
  have hdescent : baseEnd_3283763 < baseStart_3283763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283813 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 2, 3, 2]
def baseStart_3283813 : Nat := 118140960795 + 3283813 * 2 ^ 59
def prefixEnd_3283813 : Nat := 4983230072969 + 3 ^ 40 * 3283813 * 2
def baseEnd_3283813 : Nat := 1686174448482865800235525

theorem tailTrace_3283813 : CollatzResearch.WordTrace tailWord_3283813 prefixEnd_3283813 1686174448482865800235525 := by
  unfold tailWord_3283813
  simp only [CollatzResearch.WordTrace]
  refine ⟨119770499652313806455504093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79846999768209204303669395 119770499652313806455504093)
  ·
    refine ⟨44913937369617677420814035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119770499652313806455504093 44913937369617677420814035)
    ·
      refine ⟨67370906054426516131221053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44913937369617677420814035 67370906054426516131221053)
      ·
        refine ⟨25264089770409943549207895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67370906054426516131221053 25264089770409943549207895)
        ·
          refine ⟨37896134655614915323811843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25264089770409943549207895 37896134655614915323811843)
          ·
            refine ⟨56844201983422372985717765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37896134655614915323811843 56844201983422372985717765)
            ·
              refine ⟨10658287871891694934822081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56844201983422372985717765 10658287871891694934822081)
              ·
                refine ⟨7993715903918771201116561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10658287871891694934822081 7993715903918771201116561)
                ·
                  refine ⟨5995286927939078400837421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993715903918771201116561 5995286927939078400837421)
                  ·
                    refine ⟨2248232597977154400314033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5995286927939078400837421 2248232597977154400314033)
                    ·
                      refine ⟨1686174448482865800235525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248232597977154400314033 1686174448482865800235525)
                      ·
                        rfl

theorem cell23_3283813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_3283813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283813 prefixEnd_3283813 := by exact prefixLift 3283813
  have htrace : WordTrace (prefixWord ++ tailWord_3283813) baseStart_3283813 baseEnd_3283813 := by
    simpa [prefixWord, tailWord_3283813, baseEnd_3283813] using wordTrace_append hprefix tailTrace_3283813
  have hstable : (prefixWord ++ tailWord_3283813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283813).length < 2 ^ (prefixWord ++ tailWord_3283813).sum := by decide
  have hdescent : baseEnd_3283813 < baseStart_3283813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283820 : List Nat := [2, 2, 1, 1, 4, 1, 3, 4, 1, 1, 3]
def baseStart_3283820 : Nat := 118140960795 + 3283820 * 2 ^ 59
def prefixEnd_3283820 : Nat := 4983230072969 + 3 ^ 40 * 3283820 * 2
def baseEnd_3283820 : Nat := 1686178042847447272847993

theorem tailTrace_3283820 : CollatzResearch.WordTrace tailWord_3283820 prefixEnd_3283820 1686178042847447272847993 := by
  unfold tailWord_3283820
  simp only [CollatzResearch.WordTrace]
  refine ⟨59885377481644223325504457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79847169975525631100672609 59885377481644223325504457)
  ·
    refine ⟨44914033111233167494128343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59885377481644223325504457 44914033111233167494128343)
    ·
      refine ⟨67371049666849751241192515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44914033111233167494128343 67371049666849751241192515)
      ·
        refine ⟨101056574500274626861788773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67371049666849751241192515 101056574500274626861788773)
        ·
          refine ⟨18948107718801492536585395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101056574500274626861788773 18948107718801492536585395)
          ·
            refine ⟨28422161578202238804878093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18948107718801492536585395 28422161578202238804878093)
            ·
              refine ⟨10658310591825839551829285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28422161578202238804878093 10658310591825839551829285)
              ·
                refine ⟨1998433235967344915967991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10658310591825839551829285 1998433235967344915967991)
                ·
                  refine ⟨2997649853951017373951987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998433235967344915967991 2997649853951017373951987)
                  ·
                    refine ⟨4496474780926526060927981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2997649853951017373951987 4496474780926526060927981)
                    ·
                      refine ⟨1686178042847447272847993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4496474780926526060927981 1686178042847447272847993)
                      ·
                        rfl

theorem cell23_3283820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_3283820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283820 prefixEnd_3283820 := by exact prefixLift 3283820
  have htrace : WordTrace (prefixWord ++ tailWord_3283820) baseStart_3283820 baseEnd_3283820 := by
    simpa [prefixWord, tailWord_3283820, baseEnd_3283820] using wordTrace_append hprefix tailTrace_3283820
  have hstable : (prefixWord ++ tailWord_3283820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283820).length < 2 ^ (prefixWord ++ tailWord_3283820).sum := by decide
  have hdescent : baseEnd_3283820 < baseStart_3283820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283826 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3283826 : Nat := 118140960795 + 3283826 * 2 ^ 59
def prefixEnd_3283826 : Nat := 4983230072969 + 3 ^ 40 * 3283826 * 2
def baseEnd_3283826 : Nat := 1686181123731374249372965

theorem tailTrace_3283826 : CollatzResearch.WordTrace tailWord_3283826 prefixEnd_3283826 1686181123731374249372965 := by
  unfold tailWord_3283826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29942743450316677418931833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79847315867511139783818221 29942743450316677418931833)
  ·
    refine ⟨22457057587737508064198875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29942743450316677418931833 22457057587737508064198875)
    ·
      refine ⟨33685586381606262096298313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22457057587737508064198875 33685586381606262096298313)
      ·
        refine ⟨25264189786204696572223735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33685586381606262096298313 25264189786204696572223735)
        ·
          refine ⟨37896284679307044858335603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25264189786204696572223735 37896284679307044858335603)
          ·
            refine ⟨56844427018960567287503405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37896284679307044858335603 56844427018960567287503405)
            ·
              refine ⟨21316660132110212732813777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56844427018960567287503405 21316660132110212732813777)
              ·
                refine ⟨15987495099082659549610333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21316660132110212732813777 15987495099082659549610333)
                ·
                  refine ⟨5995310662155997331103875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15987495099082659549610333 5995310662155997331103875)
                  ·
                    refine ⟨8992965993233995996655813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5995310662155997331103875 8992965993233995996655813)
                    ·
                      refine ⟨1686181123731374249372965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8992965993233995996655813 1686181123731374249372965)
                      ·
                        rfl

theorem cell23_3283826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3283826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283826 prefixEnd_3283826 := by exact prefixLift 3283826
  have htrace : WordTrace (prefixWord ++ tailWord_3283826) baseStart_3283826 baseEnd_3283826 := by
    simpa [prefixWord, tailWord_3283826, baseEnd_3283826] using wordTrace_append hprefix tailTrace_3283826
  have hstable : (prefixWord ++ tailWord_3283826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283826).length < 2 ^ (prefixWord ++ tailWord_3283826).sum := by decide
  have hdescent : baseEnd_3283826 < baseStart_3283826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283839 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_3283839 : Nat := 118140960795 + 3283839 * 2 ^ 59
def prefixEnd_3283839 : Nat := 4983230072969 + 3 ^ 40 * 3283839 * 2
def baseEnd_3283839 : Nat := 1686187798979882698510405

theorem tailTrace_3283839 : CollatzResearch.WordTrace tailWord_3283839 prefixEnd_3283839 1686187798979882698510405 := by
  unfold tailWord_3283839
  simp only [CollatzResearch.WordTrace]
  refine ⟨119771447950219612895950571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79847631966813075263967047 119771447950219612895950571)
  ·
    refine ⟨179657171925329419343925857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119771447950219612895950571 179657171925329419343925857)
    ·
      refine ⟨134742878943997064507944393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179657171925329419343925857 134742878943997064507944393)
      ·
        refine ⟨101057159207997798380958295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134742878943997064507944393 101057159207997798380958295)
        ·
          refine ⟨151585738811996697571437443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101057159207997798380958295 151585738811996697571437443)
          ·
            refine ⟨227378608217995046357156165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151585738811996697571437443 227378608217995046357156165)
            ·
              refine ⟨42633489040874071191966781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227378608217995046357156165 42633489040874071191966781)
              ·
                refine ⟨15987558390327776696987543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42633489040874071191966781 15987558390327776696987543)
                ·
                  refine ⟨23981337585491665045481315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15987558390327776696987543 23981337585491665045481315)
                  ·
                    refine ⟨35972006378237497568221973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23981337585491665045481315 35972006378237497568221973)
                    ·
                      refine ⟨1686187798979882698510405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35972006378237497568221973 1686187798979882698510405)
                      ·
                        rfl

theorem cell23_3283839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_3283839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283839 prefixEnd_3283839 := by exact prefixLift 3283839
  have htrace : WordTrace (prefixWord ++ tailWord_3283839) baseStart_3283839 baseEnd_3283839 := by
    simpa [prefixWord, tailWord_3283839, baseEnd_3283839] using wordTrace_append hprefix tailTrace_3283839
  have hstable : (prefixWord ++ tailWord_3283839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283839).length < 2 ^ (prefixWord ++ tailWord_3283839).sum := by decide
  have hdescent : baseEnd_3283839 < baseStart_3283839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283860 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_3283860 : Nat := 118140960795 + 3283860 * 2 ^ 59
def prefixEnd_3283860 : Nat := 4983230072969 + 3 ^ 40 * 3283860 * 2
def baseEnd_3283860 : Nat := 1686198582073627116347809

theorem tailTrace_3283860 : CollatzResearch.WordTrace tailWord_3283860 prefixEnd_3283860 1686198582073627116347809 := by
  unfold tailWord_3283860
  simp only [CollatzResearch.WordTrace]
  refine ⟨59886106941571766741232517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79848142588762355654976689 59886106941571766741232517)
  ·
    refine ⟨11228645051544706263981097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59886106941571766741232517 11228645051544706263981097)
    ·
      refine ⟨8421483788658529697985823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11228645051544706263981097 8421483788658529697985823)
      ·
        refine ⟨12632225682987794546978735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8421483788658529697985823 12632225682987794546978735)
        ·
          refine ⟨18948338524481691820468103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12632225682987794546978735 18948338524481691820468103)
          ·
            refine ⟨28422507786722537730702155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18948338524481691820468103 28422507786722537730702155)
            ·
              refine ⟨42633761680083806596053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28422507786722537730702155 42633761680083806596053233)
              ·
                refine ⟨31975321260062854947039925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42633761680083806596053233 31975321260062854947039925)
                ·
                  refine ⟨2997686368130892651284993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31975321260062854947039925 2997686368130892651284993)
                  ·
                    refine ⟨2248264776098169488463745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2997686368130892651284993 2248264776098169488463745)
                    ·
                      refine ⟨1686198582073627116347809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248264776098169488463745 1686198582073627116347809)
                      ·
                        rfl

theorem cell23_3283860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_3283860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283860 prefixEnd_3283860 := by exact prefixLift 3283860
  have htrace : WordTrace (prefixWord ++ tailWord_3283860) baseStart_3283860 baseEnd_3283860 := by
    simpa [prefixWord, tailWord_3283860, baseEnd_3283860] using wordTrace_append hprefix tailTrace_3283860
  have hstable : (prefixWord ++ tailWord_3283860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283860).length < 2 ^ (prefixWord ++ tailWord_3283860).sum := by decide
  have hdescent : baseEnd_3283860 < baseStart_3283860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283863 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_3283863 : Nat := 118140960795 + 3283863 * 2 ^ 59
def prefixEnd_3283863 : Nat := 4983230072969 + 3 ^ 40 * 3283863 * 2
def baseEnd_3283863 : Nat := 1686200122515590604610295

theorem tailTrace_3283863 : CollatzResearch.WordTrace tailWord_3283863 prefixEnd_3283863 1686200122515590604610295 := by
  unfold tailWord_3283863
  simp only [CollatzResearch.WordTrace]
  refine ⟨119772323302132664994824243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79848215534755109996549495 119772323302132664994824243)
  ·
    refine ⟨179658484953198997492236365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119772323302132664994824243 179658484953198997492236365)
    ·
      refine ⟨67371931857449624059588637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179658484953198997492236365 67371931857449624059588637)
      ·
        refine ⟨25264474446543609022345739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67371931857449624059588637 25264474446543609022345739)
        ·
          refine ⟨37896711669815413533518609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25264474446543609022345739 37896711669815413533518609)
          ·
            refine ⟨28422533752361560150138957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37896711669815413533518609 28422533752361560150138957)
            ·
              refine ⟨10658450157135585056302109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28422533752361560150138957 10658450157135585056302109)
              ·
                refine ⟨3996918808925844396113291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10658450157135585056302109 3996918808925844396113291)
                ·
                  refine ⟨5995378213388766594169937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996918808925844396113291 5995378213388766594169937)
                  ·
                    refine ⟨4496533660041574945627453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995378213388766594169937 4496533660041574945627453)
                    ·
                      refine ⟨1686200122515590604610295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4496533660041574945627453 1686200122515590604610295)
                      ·
                        rfl

theorem cell23_3283863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_3283863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283863 prefixEnd_3283863 := by exact prefixLift 3283863
  have htrace : WordTrace (prefixWord ++ tailWord_3283863) baseStart_3283863 baseEnd_3283863 := by
    simpa [prefixWord, tailWord_3283863, baseEnd_3283863] using wordTrace_append hprefix tailTrace_3283863
  have hstable : (prefixWord ++ tailWord_3283863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283863).length < 2 ^ (prefixWord ++ tailWord_3283863).sum := by decide
  have hdescent : baseEnd_3283863 < baseStart_3283863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283866 : List Nat := [3, 1, 1, 4, 3, 1, 10]
def baseStart_3283866 : Nat := 118140960795 + 3283866 * 2 ^ 59
def prefixEnd_3283866 : Nat := 4983230072969 + 3 ^ 40 * 3283866 * 2
def baseEnd_3283866 : Nat := 20817304480957457936701

theorem tailTrace_3283866 : CollatzResearch.WordTrace tailWord_3283866 prefixEnd_3283866 20817304480957457936701 := by
  unfold tailWord_3283866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29943108180280449126795863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79848288480747864338122301 29943108180280449126795863)
  ·
    refine ⟨44914662270420673690193795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29943108180280449126795863 44914662270420673690193795)
    ·
      refine ⟨67371993405631010535290693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44914662270420673690193795 67371993405631010535290693)
      ·
        refine ⟨12632248763555814475367005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67371993405631010535290693 12632248763555814475367005)
        ·
          refine ⟨4737093286333430428262627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12632248763555814475367005 4737093286333430428262627)
          ·
            refine ⟨7105639929500145642393941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4737093286333430428262627 7105639929500145642393941)
            ·
              refine ⟨20817304480957457936701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7105639929500145642393941 20817304480957457936701)
              ·
                rfl

theorem cell23_3283866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 10].length) (baseStart_3283866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283866 prefixEnd_3283866 := by exact prefixLift 3283866
  have htrace : WordTrace (prefixWord ++ tailWord_3283866) baseStart_3283866 baseEnd_3283866 := by
    simpa [prefixWord, tailWord_3283866, baseEnd_3283866] using wordTrace_append hprefix tailTrace_3283866
  have hstable : (prefixWord ++ tailWord_3283866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283866).length < 2 ^ (prefixWord ++ tailWord_3283866).sum := by decide
  have hdescent : baseEnd_3283866 < baseStart_3283866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283917 : List Nat := [1, 6, 3, 1, 1, 2, 9]
def baseStart_3283917 : Nat := 118140960795 + 3283917 * 2 ^ 59
def prefixEnd_3283917 : Nat := 4983230072969 + 3 ^ 40 * 3283917 * 2
def baseEnd_3283917 : Nat := 20817627783591770288087

theorem tailTrace_3283917 : CollatzResearch.WordTrace tailWord_3283917 prefixEnd_3283917 20817627783591770288087 := by
  unfold tailWord_3283917
  simp only [CollatzResearch.WordTrace]
  refine ⟨119774292843937032217290005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79849528562624688144860003 119774292843937032217290005)
  ·
    refine ⟨5614419977059548385185469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119774292843937032217290005 5614419977059548385185469)
    ·
      refine ⟨2105407491397330644444551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5614419977059548385185469 2105407491397330644444551)
      ·
        refine ⟨3158111237095995966666827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105407491397330644444551 3158111237095995966666827)
        ·
          refine ⟨4737166855643993950000241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3158111237095995966666827 4737166855643993950000241)
          ·
            refine ⟨3552875141732995462500181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4737166855643993950000241 3552875141732995462500181)
            ·
              refine ⟨20817627783591770288087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3552875141732995462500181 20817627783591770288087)
              ·
                rfl

theorem cell23_3283917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 9].length) (baseStart_3283917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283917 prefixEnd_3283917 := by exact prefixLift 3283917
  have htrace : WordTrace (prefixWord ++ tailWord_3283917) baseStart_3283917 baseEnd_3283917 := by
    simpa [prefixWord, tailWord_3283917, baseEnd_3283917] using wordTrace_append hprefix tailTrace_3283917
  have hstable : (prefixWord ++ tailWord_3283917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283917).length < 2 ^ (prefixWord ++ tailWord_3283917).sum := by decide
  have hdescent : baseEnd_3283917 < baseStart_3283917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283973 : List Nat := [1, 3, 1, 1, 2, 3, 2, 5, 5]
def baseStart_3283973 : Nat := 118140960795 + 3283973 * 2 ^ 59
def prefixEnd_3283973 : Nat := 4983230072969 + 3 ^ 40 * 3283973 * 2
def baseEnd_3283973 : Nat := 187361845043065019359421

theorem tailTrace_3283973 : CollatzResearch.WordTrace tailWord_3283973 prefixEnd_3283973 187361845043065019359421 := by
  unfold tailWord_3283973
  simp only [CollatzResearch.WordTrace]
  refine ⟨119776335331734153781328573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79850890221156102520885715 119776335331734153781328573)
  ·
    refine ⟨44916125749400307667998215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119776335331734153781328573 44916125749400307667998215)
    ·
      refine ⟨67374188624100461501997323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44916125749400307667998215 67374188624100461501997323)
      ·
        refine ⟨101061282936150692252995985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67374188624100461501997323 101061282936150692252995985)
        ·
          refine ⟨75795962202113019189746989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101061282936150692252995985 75795962202113019189746989)
          ·
            refine ⟨28423485825792382196155121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75795962202113019189746989 28423485825792382196155121)
            ·
              refine ⟨21317614369344286647116341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28423485825792382196155121 21317614369344286647116341)
              ·
                refine ⟨1998526347126026873167157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21317614369344286647116341 1998526347126026873167157)
                ·
                  refine ⟨187361845043065019359421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998526347126026873167157 187361845043065019359421)
                  ·
                    rfl

theorem cell23_3283973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_3283973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283973 prefixEnd_3283973 := by exact prefixLift 3283973
  have htrace : WordTrace (prefixWord ++ tailWord_3283973) baseStart_3283973 baseEnd_3283973 := by
    simpa [prefixWord, tailWord_3283973, baseEnd_3283973] using wordTrace_append hprefix tailTrace_3283973
  have hstable : (prefixWord ++ tailWord_3283973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283973).length < 2 ^ (prefixWord ++ tailWord_3283973).sum := by decide
  have hdescent : baseEnd_3283973 < baseStart_3283973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283993 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 2, 5, 2]
def baseStart_3283993 : Nat := 118140960795 + 3283993 * 2 ^ 59
def prefixEnd_3283993 : Nat := 4983230072969 + 3 ^ 40 * 3283993 * 2
def baseEnd_3283993 : Nat := 1686266875000675095984697

theorem tailTrace_3283993 : CollatzResearch.WordTrace tailWord_3283993 prefixEnd_3283993 1686266875000675095984697 := by
  unfold tailWord_3283993
  simp only [CollatzResearch.WordTrace]
  refine ⟨119777064791661697197056633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79851376527774464798037755 119777064791661697197056633)
  ·
    refine ⟨89832798593746272897792475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119777064791661697197056633 89832798593746272897792475)
    ·
      refine ⟨134749197890619409346688713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89832798593746272897792475 134749197890619409346688713)
      ·
        refine ⟨101061898417964557010016535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134749197890619409346688713 101061898417964557010016535)
        ·
          refine ⟨151592847626946835515024803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101061898417964557010016535 151592847626946835515024803)
          ·
            refine ⟨227389271440420253272537205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151592847626946835515024803 227389271440420253272537205)
            ·
              refine ⟨21317744197539398744300363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227389271440420253272537205 21317744197539398744300363)
              ·
                refine ⟨31976616296309098116450545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21317744197539398744300363 31976616296309098116450545)
                ·
                  refine ⟨23982462222231823587337909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31976616296309098116450545 23982462222231823587337909)
                  ·
                    refine ⟨2248355833334233461312929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23982462222231823587337909 2248355833334233461312929)
                    ·
                      refine ⟨1686266875000675095984697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248355833334233461312929 1686266875000675095984697)
                      ·
                        rfl

theorem cell23_3283993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_3283993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3283993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3283993 prefixEnd_3283993 := by exact prefixLift 3283993
  have htrace : WordTrace (prefixWord ++ tailWord_3283993) baseStart_3283993 baseEnd_3283993 := by
    simpa [prefixWord, tailWord_3283993, baseEnd_3283993] using wordTrace_append hprefix tailTrace_3283993
  have hstable : (prefixWord ++ tailWord_3283993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283993).length < 2 ^ (prefixWord ++ tailWord_3283993).sum := by decide
  have hdescent : baseEnd_3283993 < baseStart_3283993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284020 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3284020 : Nat := 118140960795 + 3284020 * 2 ^ 59
def prefixEnd_3284020 : Nat := 4983230072969 + 3 ^ 40 * 3284020 * 2
def baseEnd_3284020 : Nat := 562093579659448830115691

theorem tailTrace_3284020 : CollatzResearch.WordTrace tailWord_3284020 prefixEnd_3284020 562093579659448830115691 := by
  unfold tailWord_3284020
  simp only [CollatzResearch.WordTrace]
  refine ⟨59889024781281940404144757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79852033041709253872193009 59889024781281940404144757)
  ·
    refine ⟨5614596073245181912888571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59889024781281940404144757 5614596073245181912888571)
    ·
      refine ⟨8421894109867772869332857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5614596073245181912888571 8421894109867772869332857)
      ·
        refine ⟨6316420582400829651999643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8421894109867772869332857 6316420582400829651999643)
        ·
          refine ⟨9474630873601244477999465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6316420582400829651999643 9474630873601244477999465)
          ·
            refine ⟨7105973155200933358499599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9474630873601244477999465 7105973155200933358499599)
            ·
              refine ⟨10658959732801400037749399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7105973155200933358499599 10658959732801400037749399)
              ·
                refine ⟨15988439599202100056624099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10658959732801400037749399 15988439599202100056624099)
                ·
                  refine ⟨23982659398803150084936149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15988439599202100056624099 23982659398803150084936149)
                  ·
                    refine ⟨562093579659448830115691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23982659398803150084936149 562093579659448830115691)
                    ·
                      rfl

theorem cell23_3284020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3284020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284020 prefixEnd_3284020 := by exact prefixLift 3284020
  have htrace : WordTrace (prefixWord ++ tailWord_3284020) baseStart_3284020 baseEnd_3284020 := by
    simpa [prefixWord, tailWord_3284020, baseEnd_3284020] using wordTrace_append hprefix tailTrace_3284020
  have hstable : (prefixWord ++ tailWord_3284020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284020).length < 2 ^ (prefixWord ++ tailWord_3284020).sum := by decide
  have hdescent : baseEnd_3284020 < baseStart_3284020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284023 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 3, 6, 2]
def baseStart_3284023 : Nat := 118140960795 + 3284023 * 2 ^ 59
def prefixEnd_3284023 : Nat := 4983230072969 + 3 ^ 40 * 3284023 * 2
def baseEnd_3284023 : Nat := 1686282279420309978609559

theorem tailTrace_3284023 : CollatzResearch.WordTrace tailWord_3284023 prefixEnd_3284023 1686282279420309978609559 := by
  unfold tailWord_3284023
  simp only [CollatzResearch.WordTrace]
  refine ⟨119778158981553012320648723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79852105987702008213765815 119778158981553012320648723)
  ·
    refine ⟨179667238472329518480973085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119778158981553012320648723 179667238472329518480973085)
    ·
      refine ⟨67375214427123569430364907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179667238472329518480973085 67375214427123569430364907)
      ·
        refine ⟨101062821640685354145547361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67375214427123569430364907 101062821640685354145547361)
        ·
          refine ⟨75797116230514015609160521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101062821640685354145547361 75797116230514015609160521)
          ·
            refine ⟨56847837172885511706870391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75797116230514015609160521 56847837172885511706870391)
            ·
              refine ⟨85271755759328267560305587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56847837172885511706870391 85271755759328267560305587)
              ·
                refine ⟨127907633638992401340458381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85271755759328267560305587 127907633638992401340458381)
                ·
                  refine ⟨47965362614622150502671893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127907633638992401340458381 47965362614622150502671893)
                  ·
                    refine ⟨2248376372560413304812745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47965362614622150502671893 2248376372560413304812745)
                    ·
                      refine ⟨1686282279420309978609559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248376372560413304812745 1686282279420309978609559)
                      ·
                        rfl

theorem cell23_3284023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_3284023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284023 prefixEnd_3284023 := by exact prefixLift 3284023
  have htrace : WordTrace (prefixWord ++ tailWord_3284023) baseStart_3284023 baseEnd_3284023 := by
    simpa [prefixWord, tailWord_3284023, baseEnd_3284023] using wordTrace_append hprefix tailTrace_3284023
  have hstable : (prefixWord ++ tailWord_3284023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284023).length < 2 ^ (prefixWord ++ tailWord_3284023).sum := by decide
  have hdescent : baseEnd_3284023 < baseStart_3284023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284050 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3284050 : Nat := 118140960795 + 3284050 * 2 ^ 59
def prefixEnd_3284050 : Nat := 4983230072969 + 3 ^ 40 * 3284050 * 2
def baseEnd_3284050 : Nat := 562098714465993790990645

theorem tailTrace_3284050 : CollatzResearch.WordTrace tailWord_3284050 prefixEnd_3284050 562098714465993790990645 := by
  unfold tailWord_3284050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29944785938113798982970401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79852762501636797287921069 29944785938113798982970401)
  ·
    refine ⟨22458589453585349237227801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29944785938113798982970401 22458589453585349237227801)
    ·
      refine ⟨16843942090189011927920851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22458589453585349237227801 16843942090189011927920851)
      ·
        refine ⟨25265913135283517891881277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16843942090189011927920851 25265913135283517891881277)
        ·
          refine ⟨9474717425731319209455479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25265913135283517891881277 9474717425731319209455479)
          ·
            refine ⟨14212076138596978814183219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9474717425731319209455479 14212076138596978814183219)
            ·
              refine ⟨21318114207895468221274829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14212076138596978814183219 21318114207895468221274829)
              ·
                refine ⟨7994292827960800582978061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21318114207895468221274829 7994292827960800582978061)
                ·
                  refine ⟨2997859810485300218616773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7994292827960800582978061 2997859810485300218616773)
                  ·
                    refine ⟨562098714465993790990645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2997859810485300218616773 562098714465993790990645)
                    ·
                      rfl

theorem cell23_3284050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3284050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284050 prefixEnd_3284050 := by exact prefixLift 3284050
  have htrace : WordTrace (prefixWord ++ tailWord_3284050) baseStart_3284050 baseEnd_3284050 := by
    simpa [prefixWord, tailWord_3284050, baseEnd_3284050] using wordTrace_append hprefix tailTrace_3284050
  have hstable : (prefixWord ++ tailWord_3284050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284050).length < 2 ^ (prefixWord ++ tailWord_3284050).sum := by decide
  have hdescent : baseEnd_3284050 < baseStart_3284050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284107 : List Nat := [1, 1, 1, 1, 4, 1, 1, 8, 1, 1, 3]
def baseStart_3284107 : Nat := 118140960795 + 3284107 * 2 ^ 59
def prefixEnd_3284107 : Nat := 4983230072969 + 3 ^ 40 * 3284107 * 2
def baseEnd_3284107 : Nat := 1686325411795287649959173

theorem tailTrace_3284107 : CollatzResearch.WordTrace tailWord_3284107 prefixEnd_3284107 1686325411795287649959173 := by
  unfold tailWord_3284107
  simp only [CollatzResearch.WordTrace]
  refine ⟨119781222713248694666706575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79854148475499129777804383 119781222713248694666706575)
  ·
    refine ⟨179671834069873042000059863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119781222713248694666706575 179671834069873042000059863)
    ·
      refine ⟨269507751104809563000089795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179671834069873042000059863 269507751104809563000089795)
      ·
        refine ⟨404261626657214344500134693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269507751104809563000089795 404261626657214344500134693)
        ·
          refine ⟨75799054998227689593775255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404261626657214344500134693 75799054998227689593775255)
          ·
            refine ⟨113698582497341534390662883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75799054998227689593775255 113698582497341534390662883)
            ·
              refine ⟨170547873746012301585994325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113698582497341534390662883 170547873746012301585994325)
              ·
                refine ⟨1998607895461081659210871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 170547873746012301585994325 1998607895461081659210871)
                ·
                  refine ⟨2997911843191622488816307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998607895461081659210871 2997911843191622488816307)
                  ·
                    refine ⟨4496867764787433733224461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2997911843191622488816307 4496867764787433733224461)
                    ·
                      refine ⟨1686325411795287649959173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4496867764787433733224461 1686325411795287649959173)
                      ·
                        rfl

theorem cell23_3284107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 1, 3].length) (baseStart_3284107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284107 prefixEnd_3284107 := by exact prefixLift 3284107
  have htrace : WordTrace (prefixWord ++ tailWord_3284107) baseStart_3284107 baseEnd_3284107 := by
    simpa [prefixWord, tailWord_3284107, baseEnd_3284107] using wordTrace_append hprefix tailTrace_3284107
  have hstable : (prefixWord ++ tailWord_3284107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284107).length < 2 ^ (prefixWord ++ tailWord_3284107).sum := by decide
  have hdescent : baseEnd_3284107 < baseStart_3284107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284123 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 8, 4]
def baseStart_3284123 : Nat := 118140960795 + 3284123 * 2 ^ 59
def prefixEnd_3284123 : Nat := 4983230072969 + 3 ^ 40 * 3284123 * 2
def baseEnd_3284123 : Nat := 562111209161919862453033

theorem tailTrace_3284123 : CollatzResearch.WordTrace tailWord_3284123 prefixEnd_3284123 562111209161919862453033 := by
  unfold tailWord_3284123
  simp only [CollatzResearch.WordTrace]
  refine ⟨119781806281190729399289023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79854537520793819599526015 119781806281190729399289023)
  ·
    refine ⟨179672709421786094098933535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119781806281190729399289023 179672709421786094098933535)
    ·
      refine ⟨269509064132679141148400303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179672709421786094098933535 269509064132679141148400303)
      ·
        refine ⟨404263596199018711722600455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269509064132679141148400303 404263596199018711722600455)
        ·
          refine ⟨606395394298528067583900683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404263596199018711722600455 606395394298528067583900683)
          ·
            refine ⟨909593091447792101375851025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606395394298528067583900683 909593091447792101375851025)
            ·
              refine ⟨682194818585844076031888269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909593091447792101375851025 682194818585844076031888269)
              ·
                refine ⟨255823056969691528511958101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 682194818585844076031888269 255823056969691528511958101)
                ·
                  refine ⟨2997926448863572599749509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 255823056969691528511958101 2997926448863572599749509)
                  ·
                    refine ⟨562111209161919862453033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2997926448863572599749509 562111209161919862453033)
                    ·
                      rfl

theorem cell23_3284123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 4].length) (baseStart_3284123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284123 prefixEnd_3284123 := by exact prefixLift 3284123
  have htrace : WordTrace (prefixWord ++ tailWord_3284123) baseStart_3284123 baseEnd_3284123 := by
    simpa [prefixWord, tailWord_3284123, baseEnd_3284123] using wordTrace_append hprefix tailTrace_3284123
  have hstable : (prefixWord ++ tailWord_3284123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284123).length < 2 ^ (prefixWord ++ tailWord_3284123).sum := by decide
  have hdescent : baseEnd_3284123 < baseStart_3284123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284143 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_3284143 : Nat := 118140960795 + 3284143 * 2 ^ 59
def prefixEnd_3284143 : Nat := 4983230072969 + 3 ^ 40 * 3284143 * 2
def baseEnd_3284143 : Nat := 1686343897098849509109007

theorem tailTrace_3284143 : CollatzResearch.WordTrace tailWord_3284143 prefixEnd_3284143 1686343897098849509109007 := by
  unfold tailWord_3284143
  simp only [CollatzResearch.WordTrace]
  refine ⟨119782535741118272815017083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79855023827412181876678055 119782535741118272815017083)
  ·
    refine ⟨179673803611677409222525625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119782535741118272815017083 179673803611677409222525625)
    ·
      refine ⟨134755352708758056916894219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179673803611677409222525625 134755352708758056916894219)
      ·
        refine ⟨202133029063137085375341329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134755352708758056916894219 202133029063137085375341329)
        ·
          refine ⟨151599771797352814031505997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202133029063137085375341329 151599771797352814031505997)
          ·
            refine ⟨56849914424007305261814749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151599771797352814031505997 56849914424007305261814749)
            ·
              refine ⟨21318717909002739473180531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56849914424007305261814749 21318717909002739473180531)
              ·
                refine ⟨31978076863504109209770797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21318717909002739473180531 31978076863504109209770797)
                ·
                  refine ⟨11991778823814040953664049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31978076863504109209770797 11991778823814040953664049)
                  ·
                    refine ⟨8993834117860530715248037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11991778823814040953664049 8993834117860530715248037)
                    ·
                      refine ⟨1686343897098849509109007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8993834117860530715248037 1686343897098849509109007)
                      ·
                        rfl

theorem cell23_3284143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_3284143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284143 prefixEnd_3284143 := by exact prefixLift 3284143
  have htrace : WordTrace (prefixWord ++ tailWord_3284143) baseStart_3284143 baseEnd_3284143 := by
    simpa [prefixWord, tailWord_3284143, baseEnd_3284143] using wordTrace_append hprefix tailTrace_3284143
  have hstable : (prefixWord ++ tailWord_3284143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284143).length < 2 ^ (prefixWord ++ tailWord_3284143).sum := by decide
  have hdescent : baseEnd_3284143 < baseStart_3284143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284158 : List Nat := [4, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_3284158 : Nat := 118140960795 + 3284158 * 2 ^ 59
def prefixEnd_3284158 : Nat := 4983230072969 + 3 ^ 40 * 3284158 * 2
def baseEnd_3284158 : Nat := 1686351599308666950421439

theorem tailTrace_3284158 : CollatzResearch.WordTrace tailWord_3284158 prefixEnd_3284158 1686351599308666950421439 := by
  unfold tailWord_3284158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14972885354507991297101641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79855388557375953584542085 14972885354507991297101641)
  ·
    refine ⟨11229664015880993472826231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14972885354507991297101641 11229664015880993472826231)
    ·
      refine ⟨16844496023821490209239347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11229664015880993472826231 16844496023821490209239347)
      ·
        refine ⟨25266744035732235313859021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16844496023821490209239347 25266744035732235313859021)
        ·
          refine ⟨9475029013399588242697133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25266744035732235313859021 9475029013399588242697133)
          ·
            refine ⟨3553135880024845591011425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9475029013399588242697133 3553135880024845591011425)
            ·
              refine ⟨2664851910018634193258569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553135880024845591011425 2664851910018634193258569)
              ·
                refine ⟨1998638932513975644943927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664851910018634193258569 1998638932513975644943927)
                ·
                  refine ⟨2997958398770963467415891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998638932513975644943927 2997958398770963467415891)
                  ·
                    refine ⟨4496937598156445201123837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2997958398770963467415891 4496937598156445201123837)
                    ·
                      refine ⟨1686351599308666950421439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4496937598156445201123837 1686351599308666950421439)
                      ·
                        rfl

theorem cell23_3284158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_3284158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284158 prefixEnd_3284158 := by exact prefixLift 3284158
  have htrace : WordTrace (prefixWord ++ tailWord_3284158) baseStart_3284158 baseEnd_3284158 := by
    simpa [prefixWord, tailWord_3284158, baseEnd_3284158] using wordTrace_append hprefix tailTrace_3284158
  have hstable : (prefixWord ++ tailWord_3284158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284158).length < 2 ^ (prefixWord ++ tailWord_3284158).sum := by decide
  have hdescent : baseEnd_3284158 < baseStart_3284158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284170 : List Nat := [3, 1, 2, 1, 3, 4, 1, 8]
def baseStart_3284170 : Nat := 118140960795 + 3284170 * 2 ^ 59
def prefixEnd_3284170 : Nat := 4983230072969 + 3 ^ 40 * 3284170 * 2
def baseEnd_3284170 : Nat := 62457694854685959387829

theorem tailTrace_3284170 : CollatzResearch.WordTrace tailWord_3284170 prefixEnd_3284170 62457694854685959387829 := by
  unfold tailWord_3284170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29945880128005114106562491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79855680341346970950833309 29945880128005114106562491)
  ·
    refine ⟨44918820192007671159843737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29945880128005114106562491 44918820192007671159843737)
    ·
      refine ⟨33689115144005753369882803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44918820192007671159843737 33689115144005753369882803)
      ·
        refine ⟨50533672716008630054824205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33689115144005753369882803 50533672716008630054824205)
        ·
          refine ⟨18950127268503236270559077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50533672716008630054824205 18950127268503236270559077)
          ·
            refine ⟨3553148862844356800729827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18950127268503236270559077 3553148862844356800729827)
            ·
              refine ⟨5329723294266535201094741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553148862844356800729827 5329723294266535201094741)
              ·
                refine ⟨62457694854685959387829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5329723294266535201094741 62457694854685959387829)
                ·
                  rfl

theorem cell23_3284170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_3284170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284170 prefixEnd_3284170 := by exact prefixLift 3284170
  have htrace : WordTrace (prefixWord ++ tailWord_3284170) baseStart_3284170 baseEnd_3284170 := by
    simpa [prefixWord, tailWord_3284170, baseEnd_3284170] using wordTrace_append hprefix tailTrace_3284170
  have hstable : (prefixWord ++ tailWord_3284170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284170).length < 2 ^ (prefixWord ++ tailWord_3284170).sum := by decide
  have hdescent : baseEnd_3284170 < baseStart_3284170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284277 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 7]
def baseStart_3284277 : Nat := 118140960795 + 3284277 * 2 ^ 59
def prefixEnd_3284277 : Nat := 4983230072969 + 3 ^ 40 * 3284277 * 2
def baseEnd_3284277 : Nat := 187379189278505776092599

theorem tailTrace_3284277 : CollatzResearch.WordTrace tailWord_3284277 prefixEnd_3284277 187379189278505776092599 := by
  unfold tailWord_3284277
  simp only [CollatzResearch.WordTrace]
  refine ⟨119787423122632813700395085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79858282081755209133596723 119787423122632813700395085)
  ·
    refine ⟨44920283670987305137648157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119787423122632813700395085 44920283670987305137648157)
    ·
      refine ⟨16845106376620239426618059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44920283670987305137648157 16845106376620239426618059)
      ·
        refine ⟨25267659564930359139927089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16845106376620239426618059 25267659564930359139927089)
        ·
          refine ⟨18950744673697769354945317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25267659564930359139927089 18950744673697769354945317)
          ·
            refine ⟨3553264626318331754052247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18950744673697769354945317 3553264626318331754052247)
            ·
              refine ⟨5329896939477497631078371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553264626318331754052247 5329896939477497631078371)
              ·
                refine ⟨7994845409216246446617557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329896939477497631078371 7994845409216246446617557)
                ·
                  refine ⟨187379189278505776092599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7994845409216246446617557 187379189278505776092599)
                  ·
                    rfl

theorem cell23_3284277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_3284277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284277 prefixEnd_3284277 := by exact prefixLift 3284277
  have htrace : WordTrace (prefixWord ++ tailWord_3284277) baseStart_3284277 baseEnd_3284277 := by
    simpa [prefixWord, tailWord_3284277, baseEnd_3284277] using wordTrace_append hprefix tailTrace_3284277
  have hstable : (prefixWord ++ tailWord_3284277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284277).length < 2 ^ (prefixWord ++ tailWord_3284277).sum := by decide
  have hdescent : baseEnd_3284277 < baseStart_3284277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284328 : List Nat := [2, 1, 4, 2, 4, 1, 2, 2, 5]
def baseStart_3284328 : Nat := 118140960795 + 3284328 * 2 ^ 59
def prefixEnd_3284328 : Nat := 4983230072969 + 3 ^ 40 * 3284328 * 2
def baseEnd_3284328 : Nat := 187382099002214587255073

theorem tailTrace_3284328 : CollatzResearch.WordTrace tailWord_3284328 prefixEnd_3284328 187382099002214587255073 := by
  unfold tailWord_3284328
  simp only [CollatzResearch.WordTrace]
  refine ⟨59894641622724024705250819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79859522163632032940334425 59894641622724024705250819)
  ·
    refine ⟨89841962434086037057876229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59894641622724024705250819 89841962434086037057876229)
    ·
      refine ⟨16845367956391131948351793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89841962434086037057876229 16845367956391131948351793)
      ·
        refine ⟨12634025967293348961263845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16845367956391131948351793 12634025967293348961263845)
        ·
          refine ⟨2368879868867502930236971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12634025967293348961263845 2368879868867502930236971)
          ·
            refine ⟨3553319803301254395355457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368879868867502930236971 3553319803301254395355457)
            ·
              refine ⟨2664989852475940796516593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553319803301254395355457 2664989852475940796516593)
              ·
                refine ⟨1998742389356955597387445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664989852475940796516593 1998742389356955597387445)
                ·
                  refine ⟨187382099002214587255073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998742389356955597387445 187382099002214587255073)
                  ·
                    rfl

theorem cell23_3284328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 5].length) (baseStart_3284328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284328 prefixEnd_3284328 := by exact prefixLift 3284328
  have htrace : WordTrace (prefixWord ++ tailWord_3284328) baseStart_3284328 baseEnd_3284328 := by
    simpa [prefixWord, tailWord_3284328, baseEnd_3284328] using wordTrace_append hprefix tailTrace_3284328
  have hstable : (prefixWord ++ tailWord_3284328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284328).length < 2 ^ (prefixWord ++ tailWord_3284328).sum := by decide
  have hdescent : baseEnd_3284328 < baseStart_3284328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284361 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 2, 1, 4]
def baseStart_3284361 : Nat := 118140960795 + 3284361 * 2 ^ 59
def prefixEnd_3284361 : Nat := 4983230072969 + 3 ^ 40 * 3284361 * 2
def baseEnd_3284361 : Nat := 1686455835881529656183005

theorem tailTrace_3284361 : CollatzResearch.WordTrace tailWord_3284361 prefixEnd_3284361 1686455835881529656183005 := by
  unfold tailWord_3284361
  simp only [CollatzResearch.WordTrace]
  refine ⟨119790486854328496046452937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79860324569552330697635291 119790486854328496046452937)
  ·
    refine ⟨89842865140746372034839703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119790486854328496046452937 89842865140746372034839703)
    ·
      refine ⟨134764297711119558052259555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89842865140746372034839703 134764297711119558052259555)
      ·
        refine ⟨202146446566679337078389333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134764297711119558052259555 202146446566679337078389333)
        ·
          refine ⟨2368903670703273481387375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 202146446566679337078389333 2368903670703273481387375)
          ·
            refine ⟨3553355506054910222081063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368903670703273481387375 3553355506054910222081063)
            ·
              refine ⟨5330033259082365333121595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553355506054910222081063 5330033259082365333121595)
              ·
                refine ⟨7995049888623547999682393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330033259082365333121595 7995049888623547999682393)
                ·
                  refine ⟨5996287416467660999761795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7995049888623547999682393 5996287416467660999761795)
                  ·
                    refine ⟨8994431124701491499642693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5996287416467660999761795 8994431124701491499642693)
                    ·
                      refine ⟨1686455835881529656183005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8994431124701491499642693 1686455835881529656183005)
                      ·
                        rfl

theorem cell23_3284361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 1, 4].length) (baseStart_3284361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284361 prefixEnd_3284361 := by exact prefixLift 3284361
  have htrace : WordTrace (prefixWord ++ tailWord_3284361) baseStart_3284361 baseEnd_3284361 := by
    simpa [prefixWord, tailWord_3284361, baseEnd_3284361] using wordTrace_append hprefix tailTrace_3284361
  have hstable : (prefixWord ++ tailWord_3284361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284361).length < 2 ^ (prefixWord ++ tailWord_3284361).sum := by decide
  have hdescent : baseEnd_3284361 < baseStart_3284361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284400 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_3284400 : Nat := 118140960795 + 3284400 * 2 ^ 59
def prefixEnd_3284400 : Nat := 4983230072969 + 3 ^ 40 * 3284400 * 2
def baseEnd_3284400 : Nat := 1686475861627055003595325

theorem tailTrace_3284400 : CollatzResearch.WordTrace tailWord_3284400 prefixEnd_3284400 1686475861627055003595325 := by
  unfold tailWord_3284400
  simp only [CollatzResearch.WordTrace]
  refine ⟨59895954650593602853561327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79861272867458137138081769 59895954650593602853561327)
  ·
    refine ⟨89843931975890404280341991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59895954650593602853561327 89843931975890404280341991)
    ·
      refine ⟨134765897963835606420512987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89843931975890404280341991 134765897963835606420512987)
      ·
        refine ⟨202148846945753409630769481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134765897963835606420512987 202148846945753409630769481)
        ·
          refine ⟨151611635209315057223077111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202148846945753409630769481 151611635209315057223077111)
          ·
            refine ⟨227417452813972585834615667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151611635209315057223077111 227417452813972585834615667)
            ·
              refine ⟨341126179220958878751923501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227417452813972585834615667 341126179220958878751923501)
              ·
                refine ⟨127922317207859579531971313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341126179220958878751923501 127922317207859579531971313)
                ·
                  refine ⟨95941737905894684648978485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127922317207859579531971313 95941737905894684648978485)
                  ·
                    refine ⟨8994537928677626685841733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95941737905894684648978485 8994537928677626685841733)
                    ·
                      refine ⟨1686475861627055003595325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8994537928677626685841733 1686475861627055003595325)
                      ·
                        rfl

theorem cell23_3284400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_3284400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284400 prefixEnd_3284400 := by exact prefixLift 3284400
  have htrace : WordTrace (prefixWord ++ tailWord_3284400) baseStart_3284400 baseEnd_3284400 := by
    simpa [prefixWord, tailWord_3284400, baseEnd_3284400] using wordTrace_append hprefix tailTrace_3284400
  have hstable : (prefixWord ++ tailWord_3284400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284400).length < 2 ^ (prefixWord ++ tailWord_3284400).sum := by decide
  have hdescent : baseEnd_3284400 < baseStart_3284400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284427 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 4, 4]
def baseStart_3284427 : Nat := 118140960795 + 3284427 * 2 ^ 59
def prefixEnd_3284427 : Nat := 4983230072969 + 3 ^ 40 * 3284427 * 2
def baseEnd_3284427 : Nat := 562163241868242132652567

theorem tailTrace_3284427 : CollatzResearch.WordTrace tailWord_3284427 prefixEnd_3284427 562163241868242132652567 := by
  unfold tailWord_3284427
  simp only [CollatzResearch.WordTrace]
  refine ⟨119792894072089389318355535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79861929381392926212237023 119792894072089389318355535)
  ·
    refine ⟨179689341108134083977533303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119792894072089389318355535 179689341108134083977533303)
    ·
      refine ⟨269534011662201125966299955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179689341108134083977533303 269534011662201125966299955)
      ·
        refine ⟨404301017493301688949449933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269534011662201125966299955 404301017493301688949449933)
        ·
          refine ⟨151612881559988133356043725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404301017493301688949449933 151612881559988133356043725)
          ·
            refine ⟨56854830584995550008516397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151612881559988133356043725 56854830584995550008516397)
            ·
              refine ⟨21320561469373331253193649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56854830584995550008516397 21320561469373331253193649)
              ·
                refine ⟨15990421102029998439895237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21320561469373331253193649 15990421102029998439895237)
                ·
                  refine ⟨2998203956630624707480357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15990421102029998439895237 2998203956630624707480357)
                  ·
                    refine ⟨562163241868242132652567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998203956630624707480357 562163241868242132652567)
                    ·
                      rfl

theorem cell23_3284427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 4].length) (baseStart_3284427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284427 prefixEnd_3284427 := by exact prefixLift 3284427
  have htrace : WordTrace (prefixWord ++ tailWord_3284427) baseStart_3284427 baseEnd_3284427 := by
    simpa [prefixWord, tailWord_3284427, baseEnd_3284427] using wordTrace_append hprefix tailTrace_3284427
  have hstable : (prefixWord ++ tailWord_3284427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284427).length < 2 ^ (prefixWord ++ tailWord_3284427).sum := by decide
  have hdescent : baseEnd_3284427 < baseStart_3284427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284428 : List Nat := [2, 2, 1, 4, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3284428 : Nat := 118140960795 + 3284428 * 2 ^ 59
def prefixEnd_3284428 : Nat := 4983230072969 + 3 ^ 40 * 3284428 * 2
def baseEnd_3284428 : Nat := 1686490239085380894045197

theorem tailTrace_3284428 : CollatzResearch.WordTrace tailWord_3284428 prefixEnd_3284428 1686490239085380894045197 := by
  unfold tailWord_3284428
  simp only [CollatzResearch.WordTrace]
  refine ⟨59896465272542883244570969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79861953696723844326094625 59896465272542883244570969)
  ·
    refine ⟨44922348954407162433428227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59896465272542883244570969 44922348954407162433428227)
    ·
      refine ⟨67383523431610743650142341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44922348954407162433428227 67383523431610743650142341)
      ·
        refine ⟨12634410643427014434401689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67383523431610743650142341 12634410643427014434401689)
        ·
          refine ⟨9475807982570260825801267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12634410643427014434401689 9475807982570260825801267)
          ·
            refine ⟨14213711973855391238701901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9475807982570260825801267 14213711973855391238701901)
            ·
              refine ⟨5330141990195771714513213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14213711973855391238701901 5330141990195771714513213)
              ·
                refine ⟨1998803246323414392942455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5330141990195771714513213 1998803246323414392942455)
                ·
                  refine ⟨2998204869485121589413683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998803246323414392942455 2998204869485121589413683)
                  ·
                    refine ⟨4497307304227682384120525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2998204869485121589413683 4497307304227682384120525)
                    ·
                      refine ⟨1686490239085380894045197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4497307304227682384120525 1686490239085380894045197)
                      ·
                        rfl

theorem cell23_3284428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3284428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284428 prefixEnd_3284428 := by exact prefixLift 3284428
  have htrace : WordTrace (prefixWord ++ tailWord_3284428) baseStart_3284428 baseEnd_3284428 := by
    simpa [prefixWord, tailWord_3284428, baseEnd_3284428] using wordTrace_append hprefix tailTrace_3284428
  have hstable : (prefixWord ++ tailWord_3284428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284428).length < 2 ^ (prefixWord ++ tailWord_3284428).sum := by decide
  have hdescent : baseEnd_3284428 < baseStart_3284428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284438 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_3284438 : Nat := 118140960795 + 3284438 * 2 ^ 59
def prefixEnd_3284438 : Nat := 4983230072969 + 3 ^ 40 * 3284438 * 2
def baseEnd_3284438 : Nat := 1686495373891925854920151

theorem tailTrace_3284438 : CollatzResearch.WordTrace tailWord_3284438 prefixEnd_3284438 1686495373891925854920151 := by
  unfold tailWord_3284438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7487080954690596137312873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79862196850033025464670645 7487080954690596137312873)
  ·
    refine ⟨5615310716017947102984655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7487080954690596137312873 5615310716017947102984655)
    ·
      refine ⟨8422966074026920654476983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5615310716017947102984655 8422966074026920654476983)
      ·
        refine ⟨12634449111040380981715475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8422966074026920654476983 12634449111040380981715475)
        ·
          refine ⟨18951673666560571472573213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634449111040380981715475 18951673666560571472573213)
          ·
            refine ⟨7106877624960214302214955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18951673666560571472573213 7106877624960214302214955)
            ·
              refine ⟨10660316437440321453322433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106877624960214302214955 10660316437440321453322433)
              ·
                refine ⟨7995237328080241089991825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10660316437440321453322433 7995237328080241089991825)
                ·
                  refine ⟨5996427996060180817493869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7995237328080241089991825 5996427996060180817493869)
                  ·
                    refine ⟨2248660498522567806560201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5996427996060180817493869 2248660498522567806560201)
                    ·
                      refine ⟨1686495373891925854920151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248660498522567806560201 1686495373891925854920151)
                      ·
                        rfl

theorem cell23_3284438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_3284438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284438 prefixEnd_3284438 := by exact prefixLift 3284438
  have htrace : WordTrace (prefixWord ++ tailWord_3284438) baseStart_3284438 baseEnd_3284438 := by
    simpa [prefixWord, tailWord_3284438, baseEnd_3284438] using wordTrace_append hprefix tailTrace_3284438
  have hstable : (prefixWord ++ tailWord_3284438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284438).length < 2 ^ (prefixWord ++ tailWord_3284438).sum := by decide
  have hdescent : baseEnd_3284438 < baseStart_3284438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284440 : List Nat := [2, 1, 2, 2, 2, 1, 13]
def baseStart_3284440 : Nat := 118140960795 + 3284440 * 2 ^ 59
def prefixEnd_3284440 : Nat := 4983230072969 + 3 ^ 40 * 3284440 * 2
def baseEnd_3284440 : Nat := 20820943220410306754261

theorem tailTrace_3284440 : CollatzResearch.WordTrace tailWord_3284440 prefixEnd_3284440 20820943220410306754261 := by
  unfold tailWord_3284440
  simp only [CollatzResearch.WordTrace]
  refine ⟨59896684110521146269289387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79862245480694861692385849 59896684110521146269289387)
  ·
    refine ⟨89845026165781719403934081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59896684110521146269289387 89845026165781719403934081)
    ·
      refine ⟨67383769624336289552950561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89845026165781719403934081 67383769624336289552950561)
      ·
        refine ⟨50537827218252217164712921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67383769624336289552950561 50537827218252217164712921)
        ·
          refine ⟨37903370413689162873534691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50537827218252217164712921 37903370413689162873534691)
          ·
            refine ⟨56855055620533744310302037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37903370413689162873534691 56855055620533744310302037)
            ·
              refine ⟨20820943220410306754261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 56855055620533744310302037 20820943220410306754261)
              ·
                rfl

theorem cell23_3284440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 13].length) (baseStart_3284440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284440 prefixEnd_3284440 := by exact prefixLift 3284440
  have htrace : WordTrace (prefixWord ++ tailWord_3284440) baseStart_3284440 baseEnd_3284440 := by
    simpa [prefixWord, tailWord_3284440, baseEnd_3284440] using wordTrace_append hprefix tailTrace_3284440
  have hstable : (prefixWord ++ tailWord_3284440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284440).length < 2 ^ (prefixWord ++ tailWord_3284440).sum := by decide
  have hdescent : baseEnd_3284440 < baseStart_3284440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284445 : List Nat := [1, 4, 3, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_3284445 : Nat := 118140960795 + 3284445 * 2 ^ 59
def prefixEnd_3284445 : Nat := 4983230072969 + 3 ^ 40 * 3284445 * 2
def baseEnd_3284445 : Nat := 1686498968256507327532619

theorem tailTrace_3284445 : CollatzResearch.WordTrace tailWord_3284445 prefixEnd_3284445 1686498968256507327532619 := by
  unfold tailWord_3284445
  simp only [CollatzResearch.WordTrace]
  refine ⟨119793550586024178392510789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79862367057349452261673859 119793550586024178392510789)
  ·
    refine ⟨22461290734879533448595773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119793550586024178392510789 22461290734879533448595773)
    ·
      refine ⟨8422984025579825043223415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22461290734879533448595773 8422984025579825043223415)
      ·
        refine ⟨12634476038369737564835123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8422984025579825043223415 12634476038369737564835123)
        ·
          refine ⟨18951714057554606347252685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634476038369737564835123 18951714057554606347252685)
          ·
            refine ⟨7106892771582977380219757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18951714057554606347252685 7106892771582977380219757)
            ·
              refine ⟨2665084789343616517582409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7106892771582977380219757 2665084789343616517582409)
              ·
                refine ⟨1998813592007712388186807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665084789343616517582409 1998813592007712388186807)
                ·
                  refine ⟨2998220388011568582280211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998813592007712388186807 2998220388011568582280211)
                  ·
                    refine ⟨4497330582017352873420317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2998220388011568582280211 4497330582017352873420317)
                    ·
                      refine ⟨1686498968256507327532619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4497330582017352873420317 1686498968256507327532619)
                      ·
                        rfl

theorem cell23_3284445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_3284445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284445 prefixEnd_3284445 := by exact prefixLift 3284445
  have htrace : WordTrace (prefixWord ++ tailWord_3284445) baseStart_3284445 baseEnd_3284445 := by
    simpa [prefixWord, tailWord_3284445, baseEnd_3284445] using wordTrace_append hprefix tailTrace_3284445
  have hstable : (prefixWord ++ tailWord_3284445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284445).length < 2 ^ (prefixWord ++ tailWord_3284445).sum := by decide
  have hdescent : baseEnd_3284445 < baseStart_3284445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284501 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_3284501 : Nat := 118140960795 + 3284501 * 2 ^ 59
def prefixEnd_3284501 : Nat := 4983230072969 + 3 ^ 40 * 3284501 * 2
def baseEnd_3284501 : Nat := 1686527723173159108432361

theorem tailTrace_3284501 : CollatzResearch.WordTrace tailWord_3284501 prefixEnd_3284501 1686527723173159108432361 := by
  unfold tailWord_3284501
  simp only [CollatzResearch.WordTrace]
  refine ⟨119795593073821299956549357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79863728715880866637699571 119795593073821299956549357)
  ·
    refine ⟨44923347402682987483706009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119795593073821299956549357 44923347402682987483706009)
    ·
      refine ⟨33692510552012240612779507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44923347402682987483706009 33692510552012240612779507)
      ·
        refine ⟨50538765828018360919169261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33692510552012240612779507 50538765828018360919169261)
        ·
          refine ⟨18952037185506885344688473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50538765828018360919169261 18952037185506885344688473)
          ·
            refine ⟨14214027889130164008516355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18952037185506885344688473 14214027889130164008516355)
            ·
              refine ⟨21321041833695246012774533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14214027889130164008516355 21321041833695246012774533)
              ·
                refine ⟨3997695343817858627395225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21321041833695246012774533 3997695343817858627395225)
                ·
                  refine ⟨2998271507863393970546419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3997695343817858627395225 2998271507863393970546419)
                  ·
                    refine ⟨4497407261795090955819629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2998271507863393970546419 4497407261795090955819629)
                    ·
                      refine ⟨1686527723173159108432361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4497407261795090955819629 1686527723173159108432361)
                      ·
                        rfl

theorem cell23_3284501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_3284501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284501 prefixEnd_3284501 := by exact prefixLift 3284501
  have htrace : WordTrace (prefixWord ++ tailWord_3284501) baseStart_3284501 baseEnd_3284501 := by
    simpa [prefixWord, tailWord_3284501, baseEnd_3284501] using wordTrace_append hprefix tailTrace_3284501
  have hstable : (prefixWord ++ tailWord_3284501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284501).length < 2 ^ (prefixWord ++ tailWord_3284501).sum := by decide
  have hdescent : baseEnd_3284501 < baseStart_3284501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284564 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 7]
def baseStart_3284564 : Nat := 118140960795 + 3284564 * 2 ^ 59
def prefixEnd_3284564 : Nat := 4983230072969 + 3 ^ 40 * 3284564 * 2
def baseEnd_3284564 : Nat := 187395563606043595771619

theorem tailTrace_3284564 : CollatzResearch.WordTrace tailWord_3284564 prefixEnd_3284564 187395563606043595771619 := by
  unfold tailWord_3284564
  simp only [CollatzResearch.WordTrace]
  refine ⟨59898945436296530858046373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79865260581728707810728497 59898945436296530858046373)
  ·
    refine ⟨11231052269305599535883695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59898945436296530858046373 11231052269305599535883695)
    ·
      refine ⟨16846578403958399303825543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11231052269305599535883695 16846578403958399303825543)
      ·
        refine ⟨25269867605937598955738315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16846578403958399303825543 25269867605937598955738315)
        ·
          refine ⟨37904801408906398433607473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25269867605937598955738315 37904801408906398433607473)
          ·
            refine ⟨28428601056679798825205605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37904801408906398433607473 28428601056679798825205605)
            ·
              refine ⟨5330362698127462279726051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28428601056679798825205605 5330362698127462279726051)
              ·
                refine ⟨7995544047191193419589077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330362698127462279726051 7995544047191193419589077)
                ·
                  refine ⟨187395563606043595771619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7995544047191193419589077 187395563606043595771619)
                  ·
                    rfl

theorem cell23_3284564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_3284564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284564 prefixEnd_3284564 := by exact prefixLift 3284564
  have htrace : WordTrace (prefixWord ++ tailWord_3284564) baseStart_3284564 baseEnd_3284564 := by
    simpa [prefixWord, tailWord_3284564, baseEnd_3284564] using wordTrace_append hprefix tailTrace_3284564
  have hstable : (prefixWord ++ tailWord_3284564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284564).length < 2 ^ (prefixWord ++ tailWord_3284564).sum := by decide
  have hdescent : baseEnd_3284564 < baseStart_3284564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284577 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3284577 : Nat := 118140960795 + 3284577 * 2 ^ 59
def prefixEnd_3284577 : Nat := 4983230072969 + 3 ^ 40 * 3284577 * 2
def baseEnd_3284577 : Nat := 562188915900966937027337

theorem tailTrace_3284577 : CollatzResearch.WordTrace tailWord_3284577 prefixEnd_3284577 562188915900966937027337 := by
  unfold tailWord_3284577
  simp only [CollatzResearch.WordTrace]
  refine ⟨119798365021545964936315985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79865576681030643290877323 119798365021545964936315985)
  ·
    refine ⟨89848773766159473702236989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119798365021545964936315985 89848773766159473702236989)
    ·
      refine ⟨33693290162309802638338871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89848773766159473702236989 33693290162309802638338871)
      ·
        refine ⟨50539935243464703957508307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33693290162309802638338871 50539935243464703957508307)
        ·
          refine ⟨75809902865197055936262461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50539935243464703957508307 75809902865197055936262461)
          ·
            refine ⟨28428713574448895976098423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75809902865197055936262461 28428713574448895976098423)
            ·
              refine ⟨42643070361673343964147635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28428713574448895976098423 42643070361673343964147635)
              ·
                refine ⟨63964605542510015946221453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42643070361673343964147635 63964605542510015946221453)
                ·
                  refine ⟨23986727078441255979833045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63964605542510015946221453 23986727078441255979833045)
                  ·
                    refine ⟨562188915900966937027337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23986727078441255979833045 562188915900966937027337)
                    ·
                      rfl

theorem cell23_3284577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3284577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284577 prefixEnd_3284577 := by exact prefixLift 3284577
  have htrace : WordTrace (prefixWord ++ tailWord_3284577) baseStart_3284577 baseEnd_3284577 := by
    simpa [prefixWord, tailWord_3284577, baseEnd_3284577] using wordTrace_append hprefix tailTrace_3284577
  have hstable : (prefixWord ++ tailWord_3284577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284577).length < 2 ^ (prefixWord ++ tailWord_3284577).sum := by decide
  have hdescent : baseEnd_3284577 < baseStart_3284577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284594 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_3284594 : Nat := 118140960795 + 3284594 * 2 ^ 59
def prefixEnd_3284594 : Nat := 4983230072969 + 3 ^ 40 * 3284594 * 2
def baseEnd_3284594 : Nat := 562191825624675748189811

theorem tailTrace_3284594 : CollatzResearch.WordTrace tailWord_3284594 prefixEnd_3284594 562191825624675748189811 := by
  unfold tailWord_3284594
  simp only [CollatzResearch.WordTrace]
  refine ⟨29949746265621094209921209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79865990041656251226456557 29949746265621094209921209)
  ·
    refine ⟨22462309699215820657440907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29949746265621094209921209 22462309699215820657440907)
    ·
      refine ⟨33693464548823730986161361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22462309699215820657440907 33693464548823730986161361)
      ·
        refine ⟨25270098411617798239621021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33693464548823730986161361 25270098411617798239621021)
        ·
          refine ⟨9476286904356674339857883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25270098411617798239621021 9476286904356674339857883)
          ·
            refine ⟨14214430356535011509786825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9476286904356674339857883 14214430356535011509786825)
            ·
              refine ⟨10660822767401258632340119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14214430356535011509786825 10660822767401258632340119)
              ·
                refine ⟨15991234151101887948510179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10660822767401258632340119 15991234151101887948510179)
                ·
                  refine ⟨23986851226652831922765269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15991234151101887948510179 23986851226652831922765269)
                  ·
                    refine ⟨562191825624675748189811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23986851226652831922765269 562191825624675748189811)
                    ·
                      rfl

theorem cell23_3284594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_3284594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284594 prefixEnd_3284594 := by exact prefixLift 3284594
  have htrace : WordTrace (prefixWord ++ tailWord_3284594) baseStart_3284594 baseEnd_3284594 := by
    simpa [prefixWord, tailWord_3284594, baseEnd_3284594] using wordTrace_append hprefix tailTrace_3284594
  have hstable : (prefixWord ++ tailWord_3284594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284594).length < 2 ^ (prefixWord ++ tailWord_3284594).sum := by decide
  have hdescent : baseEnd_3284594 < baseStart_3284594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284598 : List Nat := [5, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_3284598 : Nat := 118140960795 + 3284598 * 2 ^ 59
def prefixEnd_3284598 : Nat := 4983230072969 + 3 ^ 40 * 3284598 * 2
def baseEnd_3284598 : Nat := 187397503421849469879935

theorem tailTrace_3284598 : CollatzResearch.WordTrace tailWord_3284598 prefixEnd_3284598 187397503421849469879935 := by
  unfold tailWord_3284598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7487445684654367845176903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79866087302979923681886965 7487445684654367845176903)
  ·
    refine ⟨11231168526981551767765355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7487445684654367845176903 11231168526981551767765355)
    ·
      refine ⟨16846752790472327651648033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11231168526981551767765355 16846752790472327651648033)
      ·
        refine ⟨12635064592854245738736025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16846752790472327651648033 12635064592854245738736025)
        ·
          refine ⟨9476298444640684304052019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12635064592854245738736025 9476298444640684304052019)
          ·
            refine ⟨14214447666961026456078029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9476298444640684304052019 14214447666961026456078029)
            ·
              refine ⟨5330417875110384921029261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14214447666961026456078029 5330417875110384921029261)
              ·
                refine ⟨1998906703166394345385973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5330417875110384921029261 1998906703166394345385973)
                ·
                  refine ⟨187397503421849469879935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998906703166394345385973 187397503421849469879935)
                  ·
                    rfl

theorem cell23_3284598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_3284598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284598 prefixEnd_3284598 := by exact prefixLift 3284598
  have htrace : WordTrace (prefixWord ++ tailWord_3284598) baseStart_3284598 baseEnd_3284598 := by
    simpa [prefixWord, tailWord_3284598, baseEnd_3284598] using wordTrace_append hprefix tailTrace_3284598
  have hstable : (prefixWord ++ tailWord_3284598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284598).length < 2 ^ (prefixWord ++ tailWord_3284598).sum := by decide
  have hdescent : baseEnd_3284598 < baseStart_3284598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284698 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_3284698 : Nat := 118140960795 + 3284698 * 2 ^ 59
def prefixEnd_3284698 : Nat := 4983230072969 + 3 ^ 40 * 3284698 * 2
def baseEnd_3284698 : Nat := 1686628878862094837668955

theorem tailTrace_3284698 : CollatzResearch.WordTrace tailWord_3284698 prefixEnd_3284698 1686628878862094837668955 := by
  unfold tailWord_3284698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29950694563526900650367687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79868518836071735067647165 29950694563526900650367687)
  ·
    refine ⟨44926041845290350975551531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29950694563526900650367687 44926041845290350975551531)
    ·
      refine ⟨67389062767935526463327297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44926041845290350975551531 67389062767935526463327297)
      ·
        refine ⟨50541797075951644847495473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67389062767935526463327297 50541797075951644847495473)
        ·
          refine ⟨37906347806963733635621605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50541797075951644847495473 37906347806963733635621605)
          ·
            refine ⟨7107440213805700056679051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37906347806963733635621605 7107440213805700056679051)
            ·
              refine ⟨10661160320708550085018577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7107440213805700056679051 10661160320708550085018577)
              ·
                refine ⟨7995870240531412563763933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10661160320708550085018577 7995870240531412563763933)
                ·
                  refine ⟨2998451340199279711411475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7995870240531412563763933 2998451340199279711411475)
                  ·
                    refine ⟨4497677010298919567117213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2998451340199279711411475 4497677010298919567117213)
                    ·
                      refine ⟨1686628878862094837668955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4497677010298919567117213 1686628878862094837668955)
                      ·
                        rfl

theorem cell23_3284698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_3284698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284698 prefixEnd_3284698 := by exact prefixLift 3284698
  have htrace : WordTrace (prefixWord ++ tailWord_3284698) baseStart_3284698 baseEnd_3284698 := by
    simpa [prefixWord, tailWord_3284698, baseEnd_3284698] using wordTrace_append hprefix tailTrace_3284698
  have hstable : (prefixWord ++ tailWord_3284698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284698).length < 2 ^ (prefixWord ++ tailWord_3284698).sum := by decide
  have hdescent : baseEnd_3284698 < baseStart_3284698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284731 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 2, 4]
def baseStart_3284731 : Nat := 118140960795 + 3284731 * 2 ^ 59
def prefixEnd_3284731 : Nat := 4983230072969 + 3 ^ 40 * 3284731 * 2
def baseEnd_3284731 : Nat := 562215274574564402852101

theorem tailTrace_3284731 : CollatzResearch.WordTrace tailWord_3284731 prefixEnd_3284731 562215274574564402852101 := by
  unfold tailWord_3284731
  simp only [CollatzResearch.WordTrace]
  refine ⟨119803981862988049237422047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79869321241992032824948031 119803981862988049237422047)
  ·
    refine ⟨179705972794482073856133071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119803981862988049237422047 179705972794482073856133071)
    ·
      refine ⟨269558959191723110784199607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179705972794482073856133071 269558959191723110784199607)
      ·
        refine ⟨404338438787584666176299411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269558959191723110784199607 404338438787584666176299411)
        ·
          refine ⟨606507658181376999264449117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404338438787584666176299411 606507658181376999264449117)
          ·
            refine ⟨227440371818016374724168419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 606507658181376999264449117 227440371818016374724168419)
            ·
              refine ⟨341160557727024562086252629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227440371818016374724168419 341160557727024562086252629)
              ·
                refine ⟨3997975285863569086948273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 341160557727024562086252629 3997975285863569086948273)
                ·
                  refine ⟨2998481464397676815211205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3997975285863569086948273 2998481464397676815211205)
                  ·
                    refine ⟨562215274574564402852101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998481464397676815211205 562215274574564402852101)
                    ·
                      rfl

theorem cell23_3284731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 4].length) (baseStart_3284731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284731 prefixEnd_3284731 := by exact prefixLift 3284731
  have htrace : WordTrace (prefixWord ++ tailWord_3284731) baseStart_3284731 baseEnd_3284731 := by
    simpa [prefixWord, tailWord_3284731, baseEnd_3284731] using wordTrace_append hprefix tailTrace_3284731
  have hstable : (prefixWord ++ tailWord_3284731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284731).length < 2 ^ (prefixWord ++ tailWord_3284731).sum := by decide
  have hdescent : baseEnd_3284731 < baseStart_3284731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284744 : List Nat := [2, 1, 3, 2, 2, 1, 2, 10]
def baseStart_3284744 : Nat := 118140960795 + 3284744 * 2 ^ 59
def prefixEnd_3284744 : Nat := 4983230072969 + 3 ^ 40 * 3284744 * 2
def baseEnd_3284744 : Nat := 62468611073044505840509

theorem tailTrace_3284744 : CollatzResearch.WordTrace tailWord_3284744 prefixEnd_3284744 62468611073044505840509 := by
  unfold tailWord_3284744
  simp only [CollatzResearch.WordTrace]
  refine ⟨59902228005970476228822643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79869637341293968305096857 59902228005970476228822643)
  ·
    refine ⟨89853342008955714343233965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59902228005970476228822643 89853342008955714343233965)
    ·
      refine ⟨33695003253358392878712737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89853342008955714343233965 33695003253358392878712737)
      ·
        refine ⟨25271252440018794659034553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33695003253358392878712737 25271252440018794659034553)
        ·
          refine ⟨18953439330014095994275915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25271252440018794659034553 18953439330014095994275915)
          ·
            refine ⟨28430158995021143991413873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18953439330014095994275915 28430158995021143991413873)
            ·
              refine ⟨21322619246265857993560405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28430158995021143991413873 21322619246265857993560405)
              ·
                refine ⟨62468611073044505840509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21322619246265857993560405 62468611073044505840509)
                ·
                  rfl

theorem cell23_3284744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 10].length) (baseStart_3284744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284744 prefixEnd_3284744 := by exact prefixLift 3284744
  have htrace : WordTrace (prefixWord ++ tailWord_3284744) baseStart_3284744 baseEnd_3284744 := by
    simpa [prefixWord, tailWord_3284744, baseEnd_3284744] using wordTrace_append hprefix tailTrace_3284744
  have hstable : (prefixWord ++ tailWord_3284744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284744).length < 2 ^ (prefixWord ++ tailWord_3284744).sum := by decide
  have hdescent : baseEnd_3284744 < baseStart_3284744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284771 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 3]
def baseStart_3284771 : Nat := 118140960795 + 3284771 * 2 ^ 59
def prefixEnd_3284771 : Nat := 4983230072969 + 3 ^ 40 * 3284771 * 2
def baseEnd_3284771 : Nat := 1686666362949873052056119

theorem tailTrace_3284771 : CollatzResearch.WordTrace tailWord_3284771 prefixEnd_3284771 1686666362949873052056119 := by
  unfold tailWord_3284771
  simp only [CollatzResearch.WordTrace]
  refine ⟨119805440782843136068878167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79870293855228757379252111 119805440782843136068878167)
  ·
    refine ⟨179708161174264704103317251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119805440782843136068878167 179708161174264704103317251)
    ·
      refine ⟨269562241761397056154975877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179708161174264704103317251 269562241761397056154975877)
      ·
        refine ⟨50542920330261948029057977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269562241761397056154975877 50542920330261948029057977)
        ·
          refine ⟨37907190247696461021793483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50542920330261948029057977 37907190247696461021793483)
          ·
            refine ⟨56860785371544691532690225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37907190247696461021793483 56860785371544691532690225)
            ·
              refine ⟨42645589028658518649517669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56860785371544691532690225 42645589028658518649517669)
              ·
                refine ⟨7996047942873472246784563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42645589028658518649517669 7996047942873472246784563)
                ·
                  refine ⟨11994071914310208370176845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7996047942873472246784563 11994071914310208370176845)
                  ·
                    refine ⟨4497776967866328138816317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11994071914310208370176845 4497776967866328138816317)
                    ·
                      refine ⟨1686666362949873052056119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4497776967866328138816317 1686666362949873052056119)
                      ·
                        rfl

theorem cell23_3284771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_3284771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284771 prefixEnd_3284771 := by exact prefixLift 3284771
  have htrace : WordTrace (prefixWord ++ tailWord_3284771) baseStart_3284771 baseEnd_3284771 := by
    simpa [prefixWord, tailWord_3284771, baseEnd_3284771] using wordTrace_append hprefix tailTrace_3284771
  have hstable : (prefixWord ++ tailWord_3284771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284771).length < 2 ^ (prefixWord ++ tailWord_3284771).sum := by decide
  have hdescent : baseEnd_3284771 < baseStart_3284771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284789 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_3284789 : Nat := 118140960795 + 3284789 * 2 ^ 59
def prefixEnd_3284789 : Nat := 4983230072969 + 3 ^ 40 * 3284789 * 2
def baseEnd_3284789 : Nat := 1686675605601653981631037

theorem tailTrace_3284789 : CollatzResearch.WordTrace tailWord_3284789 prefixEnd_3284789 1686675605601653981631037 := by
  unfold tailWord_3284789
  simp only [CollatzResearch.WordTrace]
  refine ⟨119806097296777925143033421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79870731531185283428688947 119806097296777925143033421)
  ·
    refine ⟨44927286486291721928637533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119806097296777925143033421 44927286486291721928637533)
    ·
      refine ⟨16847732432359395723239075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44927286486291721928637533 16847732432359395723239075)
      ·
        refine ⟨25271598648539093584858613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16847732432359395723239075 25271598648539093584858613)
        ·
          refine ⟨2369212373300540023580495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25271598648539093584858613 2369212373300540023580495)
          ·
            refine ⟨3553818559950810035370743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369212373300540023580495 3553818559950810035370743)
            ·
              refine ⟨5330727839926215053056115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553818559950810035370743 5330727839926215053056115)
              ·
                refine ⟨7996091759889322579584173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330727839926215053056115 7996091759889322579584173)
                ·
                  refine ⟨2998534409958495967344065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7996091759889322579584173 2998534409958495967344065)
                  ·
                    refine ⟨2248900807468871975508049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2998534409958495967344065 2248900807468871975508049)
                    ·
                      refine ⟨1686675605601653981631037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248900807468871975508049 1686675605601653981631037)
                      ·
                        rfl

theorem cell23_3284789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_3284789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284789 prefixEnd_3284789 := by exact prefixLift 3284789
  have htrace : WordTrace (prefixWord ++ tailWord_3284789) baseStart_3284789 baseEnd_3284789 := by
    simpa [prefixWord, tailWord_3284789, baseEnd_3284789] using wordTrace_append hprefix tailTrace_3284789
  have hstable : (prefixWord ++ tailWord_3284789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284789).length < 2 ^ (prefixWord ++ tailWord_3284789).sum := by decide
  have hdescent : baseEnd_3284789 < baseStart_3284789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284831 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_3284831 : Nat := 118140960795 + 3284831 * 2 ^ 59
def prefixEnd_3284831 : Nat := 4983230072969 + 3 ^ 40 * 3284831 * 2
def baseEnd_3284831 : Nat := 1686697171789142817305843

theorem tailTrace_3284831 : CollatzResearch.WordTrace tailWord_3284831 prefixEnd_3284831 1686697171789142817305843 := by
  unfold tailWord_3284831
  simp only [CollatzResearch.WordTrace]
  refine ⟨119807629162625766316062347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79871752775083844210708231 119807629162625766316062347)
  ·
    refine ⟨179711443743938649474093521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119807629162625766316062347 179711443743938649474093521)
    ·
      refine ⟨134783582807953987105570141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179711443743938649474093521 134783582807953987105570141)
      ·
        refine ⟨50543843552982745164588803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134783582807953987105570141 50543843552982745164588803)
        ·
          refine ⟨75815765329474117746883205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50543843552982745164588803 75815765329474117746883205)
          ·
            refine ⟨14215455999276397077540601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75815765329474117746883205 14215455999276397077540601)
            ·
              refine ⟨10661591999457297808155451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14215455999276397077540601 10661591999457297808155451)
              ·
                refine ⟨15992387999185946712233177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10661591999457297808155451 15992387999185946712233177)
                ·
                  refine ⟨11994290999389460034174883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15992387999185946712233177 11994290999389460034174883)
                  ·
                    refine ⟨17991436499084190051262325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11994290999389460034174883 17991436499084190051262325)
                    ·
                      refine ⟨1686697171789142817305843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17991436499084190051262325 1686697171789142817305843)
                      ·
                        rfl

theorem cell23_3284831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_3284831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284831 prefixEnd_3284831 := by exact prefixLift 3284831
  have htrace : WordTrace (prefixWord ++ tailWord_3284831) baseStart_3284831 baseEnd_3284831 := by
    simpa [prefixWord, tailWord_3284831, baseEnd_3284831] using wordTrace_append hprefix tailTrace_3284831
  have hstable : (prefixWord ++ tailWord_3284831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284831).length < 2 ^ (prefixWord ++ tailWord_3284831).sum := by decide
  have hdescent : baseEnd_3284831 < baseStart_3284831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284832 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 1, 3, 2]
def baseStart_3284832 : Nat := 118140960795 + 3284832 * 2 ^ 59
def prefixEnd_3284832 : Nat := 4983230072969 + 3 ^ 40 * 3284832 * 2
def baseEnd_3284832 : Nat := 1686697685269797313393339

theorem tailTrace_3284832 : CollatzResearch.WordTrace tailWord_3284832 prefixEnd_3284832 1686697685269797313393339 := by
  unfold tailWord_3284832
  simp only [CollatzResearch.WordTrace]
  refine ⟨59903832817811071743424375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79871777090414762324565833 59903832817811071743424375)
  ·
    refine ⟨89855749226716607615136563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59903832817811071743424375 89855749226716607615136563)
    ·
      refine ⟨134783623840074911422704845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89855749226716607615136563 134783623840074911422704845)
      ·
        refine ⟨50543858940028091783514317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134783623840074911422704845 50543858940028091783514317)
        ·
          refine ⟨18953947102510534418817869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50543858940028091783514317 18953947102510534418817869)
          ·
            refine ⟨7107730163441450407056701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18953947102510534418817869 7107730163441450407056701)
            ·
              refine ⟨2665398811290543902646263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7107730163441450407056701 2665398811290543902646263)
              ·
                refine ⟨3998098216935815853969395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665398811290543902646263 3998098216935815853969395)
                ·
                  refine ⟨5997147325403723780954093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998098216935815853969395 5997147325403723780954093)
                  ·
                    refine ⟨2248930247026396417857785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5997147325403723780954093 2248930247026396417857785)
                    ·
                      refine ⟨1686697685269797313393339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248930247026396417857785 1686697685269797313393339)
                      ·
                        rfl

theorem cell23_3284832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_3284832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284832 prefixEnd_3284832 := by exact prefixLift 3284832
  have htrace : WordTrace (prefixWord ++ tailWord_3284832) baseStart_3284832 baseEnd_3284832 := by
    simpa [prefixWord, tailWord_3284832, baseEnd_3284832] using wordTrace_append hprefix tailTrace_3284832
  have hstable : (prefixWord ++ tailWord_3284832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284832).length < 2 ^ (prefixWord ++ tailWord_3284832).sum := by decide
  have hdescent : baseEnd_3284832 < baseStart_3284832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284845 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_3284845 : Nat := 118140960795 + 3284845 * 2 ^ 59
def prefixEnd_3284845 : Nat := 4983230072969 + 3 ^ 40 * 3284845 * 2
def baseEnd_3284845 : Nat := 1686704360518305762530779

theorem tailTrace_3284845 : CollatzResearch.WordTrace tailWord_3284845 prefixEnd_3284845 1686704360518305762530779 := by
  unfold tailWord_3284845
  simp only [CollatzResearch.WordTrace]
  refine ⟨119808139784575046707071989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79872093189716697804714659 119808139784575046707071989)
  ·
    refine ⟨11232013104803910628787999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119808139784575046707071989 11232013104803910628787999)
    ·
      refine ⟨16848019657205865943181999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11232013104803910628787999 16848019657205865943181999)
      ·
        refine ⟨25272029485808798914772999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16848019657205865943181999 25272029485808798914772999)
        ·
          refine ⟨37908044228713198372159499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25272029485808798914772999 37908044228713198372159499)
          ·
            refine ⟨56862066343069797558239249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37908044228713198372159499 56862066343069797558239249)
            ·
              refine ⟨42646549757302348168679437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56862066343069797558239249 42646549757302348168679437)
              ·
                refine ⟨15992456158988380563254789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42646549757302348168679437 15992456158988380563254789)
                ·
                  refine ⟨2998585529810321355610273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15992456158988380563254789 2998585529810321355610273)
                  ·
                    refine ⟨2248939147357741016707705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2998585529810321355610273 2248939147357741016707705)
                    ·
                      refine ⟨1686704360518305762530779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248939147357741016707705 1686704360518305762530779)
                      ·
                        rfl

theorem cell23_3284845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_3284845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284845 prefixEnd_3284845 := by exact prefixLift 3284845
  have htrace : WordTrace (prefixWord ++ tailWord_3284845) baseStart_3284845 baseEnd_3284845 := by
    simpa [prefixWord, tailWord_3284845, baseEnd_3284845] using wordTrace_append hprefix tailTrace_3284845
  have hstable : (prefixWord ++ tailWord_3284845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284845).length < 2 ^ (prefixWord ++ tailWord_3284845).sum := by decide
  have hdescent : baseEnd_3284845 < baseStart_3284845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284862 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3284862 : Nat := 118140960795 + 3284862 * 2 ^ 59
def prefixEnd_3284862 : Nat := 4983230072969 + 3 ^ 40 * 3284862 * 2
def baseEnd_3284862 : Nat := 1686713089689432196018201

theorem tailTrace_3284862 : CollatzResearch.WordTrace tailWord_3284862 prefixEnd_3284862 1686713089689432196018201 := by
  unfold tailWord_3284862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14976094978189182326305105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79872506550342305740293893 14976094978189182326305105)
  ·
    refine ⟨11232071233641886744728829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14976094978189182326305105 11232071233641886744728829)
    ·
      refine ⟨4212026712615707529273311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11232071233641886744728829 4212026712615707529273311)
      ·
        refine ⟨6318040068923561293909967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212026712615707529273311 6318040068923561293909967)
        ·
          refine ⟨9477060103385341940864951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318040068923561293909967 9477060103385341940864951)
          ·
            refine ⟨14215590155078012911297427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9477060103385341940864951 14215590155078012911297427)
            ·
              refine ⟨21323385232617019366946141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14215590155078012911297427 21323385232617019366946141)
              ·
                refine ⟨7996269462231382262604803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21323385232617019366946141 7996269462231382262604803)
                ·
                  refine ⟨11994404193347073393907205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7996269462231382262604803 11994404193347073393907205)
                  ·
                    refine ⟨2248950786252576261357601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11994404193347073393907205 2248950786252576261357601)
                    ·
                      refine ⟨1686713089689432196018201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2248950786252576261357601 1686713089689432196018201)
                      ·
                        rfl

theorem cell23_3284862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3284862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284862 prefixEnd_3284862 := by exact prefixLift 3284862
  have htrace : WordTrace (prefixWord ++ tailWord_3284862) baseStart_3284862 baseEnd_3284862 := by
    simpa [prefixWord, tailWord_3284862, baseEnd_3284862] using wordTrace_append hprefix tailTrace_3284862
  have hstable : (prefixWord ++ tailWord_3284862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284862).length < 2 ^ (prefixWord ++ tailWord_3284862).sum := by decide
  have hdescent : baseEnd_3284862 < baseStart_3284862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284928 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 3, 4]
def baseStart_3284928 : Nat := 118140960795 + 3284928 * 2 ^ 59
def prefixEnd_3284928 : Nat := 4983230072969 + 3 ^ 40 * 3284928 * 2
def baseEnd_3284928 : Nat := 562248993137542979264299

theorem tailTrace_3284928 : CollatzResearch.WordTrace tailWord_3284928 prefixEnd_3284928 562248993137542979264299 := by
  unfold tailWord_3284928
  simp only [CollatzResearch.WordTrace]
  refine ⟨59905583521637175941171719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79874111362182901254895625 59905583521637175941171719)
  ·
    refine ⟨89858375282455763911757579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59905583521637175941171719 89858375282455763911757579)
    ·
      refine ⟨134787562923683645867636369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89858375282455763911757579 134787562923683645867636369)
      ·
        refine ⟨101090672192762734400727277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134787562923683645867636369 101090672192762734400727277)
        ·
          refine ⟨37909002072286025400272729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101090672192762734400727277 37909002072286025400272729)
          ·
            refine ⟨28431751554214519050204547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37909002072286025400272729 28431751554214519050204547)
            ·
              refine ⟨42647627331321778575306821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28431751554214519050204547 42647627331321778575306821)
              ·
                refine ⟨7996430124622833482870029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42647627331321778575306821 7996430124622833482870029)
                ·
                  refine ⟨2998661296733562556076261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7996430124622833482870029 2998661296733562556076261)
                  ·
                    refine ⟨562248993137542979264299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998661296733562556076261 562248993137542979264299)
                    ·
                      rfl

theorem cell23_3284928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_3284928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284928 prefixEnd_3284928 := by exact prefixLift 3284928
  have htrace : WordTrace (prefixWord ++ tailWord_3284928) baseStart_3284928 baseEnd_3284928 := by
    simpa [prefixWord, tailWord_3284928, baseEnd_3284928] using wordTrace_append hprefix tailTrace_3284928
  have hstable : (prefixWord ++ tailWord_3284928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284928).length < 2 ^ (prefixWord ++ tailWord_3284928).sum := by decide
  have hdescent : baseEnd_3284928 < baseStart_3284928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284938 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_3284938 : Nat := 118140960795 + 3284938 * 2 ^ 59
def prefixEnd_3284938 : Nat := 4983230072969 + 3 ^ 40 * 3284938 * 2
def baseEnd_3284938 : Nat := 1686752114219173898667851

theorem tailTrace_3284938 : CollatzResearch.WordTrace tailWord_3284938 prefixEnd_3284938 1686752114219173898667851 := by
  unfold tailWord_3284938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29952882943309530897551867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79874354515492082393471645 29952882943309530897551867)
  ·
    refine ⟨44929324414964296346327801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29952882943309530897551867 44929324414964296346327801)
    ·
      refine ⟨33696993311223222259745851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44929324414964296346327801 33696993311223222259745851)
      ·
        refine ⟨50545489966834833389618777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33696993311223222259745851 50545489966834833389618777)
        ·
          refine ⟨37909117475126125042214083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50545489966834833389618777 37909117475126125042214083)
          ·
            refine ⟨56863676212689187563321125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37909117475126125042214083 56863676212689187563321125)
            ·
              refine ⟨10661939289879222668122711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56863676212689187563321125 10661939289879222668122711)
              ·
                refine ⟨15992908934818834002184067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10661939289879222668122711 15992908934818834002184067)
                ·
                  refine ⟨23989363402228251003276101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15992908934818834002184067 23989363402228251003276101)
                  ·
                    refine ⟨4498005637917797063114269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23989363402228251003276101 4498005637917797063114269)
                    ·
                      refine ⟨1686752114219173898667851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4498005637917797063114269 1686752114219173898667851)
                      ·
                        rfl

theorem cell23_3284938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_3284938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284938 prefixEnd_3284938 := by exact prefixLift 3284938
  have htrace : WordTrace (prefixWord ++ tailWord_3284938) baseStart_3284938 baseEnd_3284938 := by
    simpa [prefixWord, tailWord_3284938, baseEnd_3284938] using wordTrace_append hprefix tailTrace_3284938
  have hstable : (prefixWord ++ tailWord_3284938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284938).length < 2 ^ (prefixWord ++ tailWord_3284938).sum := by decide
  have hdescent : baseEnd_3284938 < baseStart_3284938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284945 : List Nat := [1, 2, 2, 1, 2, 1, 2, 7, 1, 4]
def baseStart_3284945 : Nat := 118140960795 + 3284945 * 2 ^ 59
def prefixEnd_3284945 : Nat := 4983230072969 + 3 ^ 40 * 3284945 * 2
def baseEnd_3284945 : Nat := 562251902861251790426773

theorem tailTrace_3284945 : CollatzResearch.WordTrace tailWord_3284945 prefixEnd_3284945 562251902861251790426773 := by
  unfold tailWord_3284945
  simp only [CollatzResearch.WordTrace]
  refine ⟨119811787084212763785712289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79874524722808509190474859 119811787084212763785712289)
  ·
    refine ⟨89858840313159572839284217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119811787084212763785712289 89858840313159572839284217)
    ·
      refine ⟨67394130234869679629463163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89858840313159572839284217 67394130234869679629463163)
      ·
        refine ⟨101091195352304519444194745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67394130234869679629463163 101091195352304519444194745)
        ·
          refine ⟨75818396514228389583146059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101091195352304519444194745 75818396514228389583146059)
          ·
            refine ⟨113727594771342584374719089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75818396514228389583146059 113727594771342584374719089)
            ·
              refine ⟨85295696078506938281039317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113727594771342584374719089 85295696078506938281039317)
              ·
                refine ⟨1999117876840006365961859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85295696078506938281039317 1999117876840006365961859)
                ·
                  refine ⟨2998676815260009548942789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999117876840006365961859 2998676815260009548942789)
                  ·
                    refine ⟨562251902861251790426773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998676815260009548942789 562251902861251790426773)
                    ·
                      rfl

theorem cell23_3284945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_3284945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284945 prefixEnd_3284945 := by exact prefixLift 3284945
  have htrace : WordTrace (prefixWord ++ tailWord_3284945) baseStart_3284945 baseEnd_3284945 := by
    simpa [prefixWord, tailWord_3284945, baseEnd_3284945] using wordTrace_append hprefix tailTrace_3284945
  have hstable : (prefixWord ++ tailWord_3284945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284945).length < 2 ^ (prefixWord ++ tailWord_3284945).sum := by decide
  have hdescent : baseEnd_3284945 < baseStart_3284945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284961 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_3284961 : Nat := 118140960795 + 3284961 * 2 ^ 59
def prefixEnd_3284961 : Nat := 4983230072969 + 3 ^ 40 * 3284961 * 2
def baseEnd_3284961 : Nat := 1686763924274227308680245

theorem tailTrace_3284961 : CollatzResearch.WordTrace tailWord_3284961 prefixEnd_3284961 1686763924274227308680245 := by
  unfold tailWord_3284961
  simp only [CollatzResearch.WordTrace]
  refine ⟨119812370652154798518294737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79874913768103199012196491 119812370652154798518294737)
  ·
    refine ⟨89859277989116098888721053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119812370652154798518294737 89859277989116098888721053)
    ·
      refine ⟨33697229245918537083270395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89859277989116098888721053 33697229245918537083270395)
      ·
        refine ⟨50545843868877805624905593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33697229245918537083270395 50545843868877805624905593)
        ·
          refine ⟨37909382901658354218679195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50545843868877805624905593 37909382901658354218679195)
          ·
            refine ⟨56864074352487531328018793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37909382901658354218679195 56864074352487531328018793)
            ·
              refine ⟨42648055764365648496014095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56864074352487531328018793 42648055764365648496014095)
              ·
                refine ⟨63972083646548472744021143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42648055764365648496014095 63972083646548472744021143)
                ·
                  refine ⟨95958125469822709116031715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63972083646548472744021143 95958125469822709116031715)
                  ·
                    refine ⟨143937188204734063674047573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95958125469822709116031715 143937188204734063674047573)
                    ·
                      refine ⟨1686763924274227308680245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 143937188204734063674047573 1686763924274227308680245)
                      ·
                        rfl

theorem cell23_3284961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_3284961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284961 prefixEnd_3284961 := by exact prefixLift 3284961
  have htrace : WordTrace (prefixWord ++ tailWord_3284961) baseStart_3284961 baseEnd_3284961 := by
    simpa [prefixWord, tailWord_3284961, baseEnd_3284961] using wordTrace_append hprefix tailTrace_3284961
  have hstable : (prefixWord ++ tailWord_3284961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284961).length < 2 ^ (prefixWord ++ tailWord_3284961).sum := by decide
  have hdescent : baseEnd_3284961 < baseStart_3284961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284988 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_3284988 : Nat := 118140960795 + 3284988 * 2 ^ 59
def prefixEnd_3284988 : Nat := 4983230072969 + 3 ^ 40 * 3284988 * 2
def baseEnd_3284988 : Nat := 562259262750632901014207

theorem tailTrace_3284988 : CollatzResearch.WordTrace tailWord_3284988 prefixEnd_3284988 562259262750632901014207 := by
  unfold tailWord_3284988
  simp only [CollatzResearch.WordTrace]
  refine ⟨59906677711528491064763809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79875570282037988086351745 59906677711528491064763809)
  ·
    refine ⟨44930008283646368298572857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59906677711528491064763809 44930008283646368298572857)
    ·
      refine ⟨33697506212734776223929643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44930008283646368298572857 33697506212734776223929643)
      ·
        refine ⟨50546259319102164335894465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33697506212734776223929643 50546259319102164335894465)
        ·
          refine ⟨37909694489326623251920849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50546259319102164335894465 37909694489326623251920849)
          ·
            refine ⟨28432270866994967438940637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37909694489326623251920849 28432270866994967438940637)
            ·
              refine ⟨10662101575123112789602739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28432270866994967438940637 10662101575123112789602739)
              ·
                refine ⟨15993152362684669184404109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10662101575123112789602739 15993152362684669184404109)
                ·
                  refine ⟨5997432136006750944151541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15993152362684669184404109 5997432136006750944151541)
                  ·
                    refine ⟨562259262750632901014207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5997432136006750944151541 562259262750632901014207)
                    ·
                      rfl

theorem cell23_3284988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_3284988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3284988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3284988 prefixEnd_3284988 := by exact prefixLift 3284988
  have htrace : WordTrace (prefixWord ++ tailWord_3284988) baseStart_3284988 baseEnd_3284988 := by
    simpa [prefixWord, tailWord_3284988, baseEnd_3284988] using wordTrace_append hprefix tailTrace_3284988
  have hstable : (prefixWord ++ tailWord_3284988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284988).length < 2 ^ (prefixWord ++ tailWord_3284988).sum := by decide
  have hdescent : baseEnd_3284988 < baseStart_3284988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285042 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_3285042 : Nat := 118140960795 + 3285042 * 2 ^ 59
def prefixEnd_3285042 : Nat := 4983230072969 + 3 ^ 40 * 3285042 * 2
def baseEnd_3285042 : Nat := 1686805516207241491767373

theorem tailTrace_3285042 : CollatzResearch.WordTrace tailWord_3285042 prefixEnd_3285042 1686805516207241491767373 := by
  unfold tailWord_3285042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29953831241215337337998345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79876883309907566234662253 29953831241215337337998345)
  ·
    refine ⟨22465373430911503003498759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29953831241215337337998345 22465373430911503003498759)
    ·
      refine ⟨33698060146367254505248139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22465373430911503003498759 33698060146367254505248139)
      ·
        refine ⟨50547090219550881757872209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33698060146367254505248139 50547090219550881757872209)
        ·
          refine ⟨37910317664663161318404157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50547090219550881757872209 37910317664663161318404157)
          ·
            refine ⟨14216369124248685494401559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37910317664663161318404157 14216369124248685494401559)
            ·
              refine ⟨21324553686373028241602339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14216369124248685494401559 21324553686373028241602339)
              ·
                refine ⟨31986830529559542362403509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21324553686373028241602339 31986830529559542362403509)
                ·
                  refine ⟨2998765362146207096475329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31986830529559542362403509 2998765362146207096475329)
                  ·
                    refine ⟨2249074021609655322356497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2998765362146207096475329 2249074021609655322356497)
                    ·
                      refine ⟨1686805516207241491767373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249074021609655322356497 1686805516207241491767373)
                      ·
                        rfl

theorem cell23_3285042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_3285042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285042 prefixEnd_3285042 := by exact prefixLift 3285042
  have htrace : WordTrace (prefixWord ++ tailWord_3285042) baseStart_3285042 baseEnd_3285042 := by
    simpa [prefixWord, tailWord_3285042, baseEnd_3285042] using wordTrace_append hprefix tailTrace_3285042
  have hstable : (prefixWord ++ tailWord_3285042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285042).length < 2 ^ (prefixWord ++ tailWord_3285042).sum := by decide
  have hdescent : baseEnd_3285042 < baseStart_3285042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285045 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_3285045 : Nat := 118140960795 + 3285045 * 2 ^ 59
def prefixEnd_3285045 : Nat := 4983230072969 + 3 ^ 40 * 3285045 * 2
def baseEnd_3285045 : Nat := 1686807056649204980029859

theorem tailTrace_3285045 : CollatzResearch.WordTrace tailWord_3285045 prefixEnd_3285045 1686807056649204980029859 := by
  unfold tailWord_3285045
  simp only [CollatzResearch.WordTrace]
  refine ⟨119815434383850480864352589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79876956255900320576235059 119815434383850480864352589)
  ·
    refine ⟨44930787893943930324132221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119815434383850480864352589 44930787893943930324132221)
    ·
      refine ⟨16849045460228973871549583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44930787893943930324132221 16849045460228973871549583)
      ·
        refine ⟨25273568190343460807324375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16849045460228973871549583 25273568190343460807324375)
        ·
          refine ⟨37910352285515191210986563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25273568190343460807324375 37910352285515191210986563)
          ·
            refine ⟨56865528428272786816479845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37910352285515191210986563 56865528428272786816479845)
            ·
              refine ⟨10662286580301147528089971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56865528428272786816479845 10662286580301147528089971)
              ·
                refine ⟨15993429870451721292134957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10662286580301147528089971 15993429870451721292134957)
                ·
                  refine ⟨5997536201419395484550609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15993429870451721292134957 5997536201419395484550609)
                  ·
                    refine ⟨4498152151064546613412957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5997536201419395484550609 4498152151064546613412957)
                    ·
                      refine ⟨1686807056649204980029859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4498152151064546613412957 1686807056649204980029859)
                      ·
                        rfl

theorem cell23_3285045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_3285045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285045 prefixEnd_3285045 := by exact prefixLift 3285045
  have htrace : WordTrace (prefixWord ++ tailWord_3285045) baseStart_3285045 baseEnd_3285045 := by
    simpa [prefixWord, tailWord_3285045, baseEnd_3285045] using wordTrace_append hprefix tailTrace_3285045
  have hstable : (prefixWord ++ tailWord_3285045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285045).length < 2 ^ (prefixWord ++ tailWord_3285045).sum := by decide
  have hdescent : baseEnd_3285045 < baseStart_3285045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285062 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3285062 : Nat := 118140960795 + 3285062 * 2 ^ 59
def prefixEnd_3285062 : Nat := 4983230072969 + 3 ^ 40 * 3285062 * 2
def baseEnd_3285062 : Nat := 1686815785820331413517281

theorem tailTrace_3285062 : CollatzResearch.WordTrace tailWord_3285062 prefixEnd_3285062 1686815785820331413517281 := by
  unfold tailWord_3285062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3744251700774652898991295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79877369616525928511814293 3744251700774652898991295)
  ·
    refine ⟨5616377551161979348486943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3744251700774652898991295 5616377551161979348486943)
    ·
      refine ⟨8424566326742969022730415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5616377551161979348486943 8424566326742969022730415)
      ·
        refine ⟨12636849490114453534095623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8424566326742969022730415 12636849490114453534095623)
        ·
          refine ⟨18955274235171680301143435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12636849490114453534095623 18955274235171680301143435)
          ·
            refine ⟨28432911352757520451715153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18955274235171680301143435 28432911352757520451715153)
            ·
              refine ⟨21324683514568140338786365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28432911352757520451715153 21324683514568140338786365)
              ·
                refine ⟨7996756317963052627044887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21324683514568140338786365 7996756317963052627044887)
                ·
                  refine ⟨11995134476944578940567331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7996756317963052627044887 11995134476944578940567331)
                  ·
                    refine ⟨17992701715416868410850997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11995134476944578940567331 17992701715416868410850997)
                    ·
                      refine ⟨1686815785820331413517281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17992701715416868410850997 1686815785820331413517281)
                      ·
                        rfl

theorem cell23_3285062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3285062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285062 prefixEnd_3285062 := by exact prefixLift 3285062
  have htrace : WordTrace (prefixWord ++ tailWord_3285062) baseStart_3285062 baseEnd_3285062 := by
    simpa [prefixWord, tailWord_3285062, baseEnd_3285062] using wordTrace_append hprefix tailTrace_3285062
  have hstable : (prefixWord ++ tailWord_3285062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285062).length < 2 ^ (prefixWord ++ tailWord_3285062).sum := by decide
  have hdescent : baseEnd_3285062 < baseStart_3285062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285086 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3285086 : Nat := 118140960795 + 3285086 * 2 ^ 59
def prefixEnd_3285086 : Nat := 4983230072969 + 3 ^ 40 * 3285086 * 2
def baseEnd_3285086 : Nat := 562276036452013106539057

theorem tailTrace_3285086 : CollatzResearch.WordTrace tailWord_3285086 prefixEnd_3285086 562276036452013106539057 := by
  unfold tailWord_3285086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14977116222087743108324389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79877953184467963244396741 14977116222087743108324389)
  ·
    refine ⟨2808209291641451832810823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14977116222087743108324389 2808209291641451832810823)
    ·
      refine ⟨4212313937462177749216235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2808209291641451832810823 4212313937462177749216235)
      ·
        refine ⟨6318470906193266623824353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212313937462177749216235 6318470906193266623824353)
        ·
          refine ⟨4738853179644949967868265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6318470906193266623824353 4738853179644949967868265)
          ·
            refine ⟨3554139884733712475901199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4738853179644949967868265 3554139884733712475901199)
            ·
              refine ⟨5331209827100568713851799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554139884733712475901199 5331209827100568713851799)
              ·
                refine ⟨7996814740650853070777699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5331209827100568713851799 7996814740650853070777699)
                ·
                  refine ⟨11995222110976279606166549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7996814740650853070777699 11995222110976279606166549)
                  ·
                    refine ⟨562276036452013106539057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11995222110976279606166549 562276036452013106539057)
                    ·
                      rfl

theorem cell23_3285086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3285086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285086 prefixEnd_3285086 := by exact prefixLift 3285086
  have htrace : WordTrace (prefixWord ++ tailWord_3285086) baseStart_3285086 baseEnd_3285086 := by
    simpa [prefixWord, tailWord_3285086, baseEnd_3285086] using wordTrace_append hprefix tailTrace_3285086
  have hstable : (prefixWord ++ tailWord_3285086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285086).length < 2 ^ (prefixWord ++ tailWord_3285086).sum := by decide
  have hdescent : baseEnd_3285086 < baseStart_3285086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285092 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_3285092 : Nat := 118140960795 + 3285092 * 2 ^ 59
def prefixEnd_3285092 : Nat := 4983230072969 + 3 ^ 40 * 3285092 * 2
def baseEnd_3285092 : Nat := 1686831190239966296142143

theorem tailTrace_3285092 : CollatzResearch.WordTrace tailWord_3285092 prefixEnd_3285092 1686831190239966296142143 := by
  unfold tailWord_3285092
  simp only [CollatzResearch.WordTrace]
  refine ⟨59908574307340103945656765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79878099076453471927542353 59908574307340103945656765)
  ·
    refine ⟨22465715365252538979621287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59908574307340103945656765 22465715365252538979621287)
    ·
      refine ⟨33698573047878808469431931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22465715365252538979621287 33698573047878808469431931)
      ·
        refine ⟨50547859571818212704147897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33698573047878808469431931 50547859571818212704147897)
        ·
          refine ⟨37910894678863659528110923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50547859571818212704147897 37910894678863659528110923)
          ·
            refine ⟨56866342018295489292166385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37910894678863659528110923 56866342018295489292166385)
            ·
              refine ⟨42649756513721616969124789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56866342018295489292166385 42649756513721616969124789)
              ·
                refine ⟨3998414673161401590855449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42649756513721616969124789 3998414673161401590855449)
                ·
                  refine ⟨2998811004871051193141587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998414673161401590855449 2998811004871051193141587)
                  ·
                    refine ⟨4498216507306576789712381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2998811004871051193141587 4498216507306576789712381)
                    ·
                      refine ⟨1686831190239966296142143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4498216507306576789712381 1686831190239966296142143)
                      ·
                        rfl

theorem cell23_3285092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_3285092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285092 prefixEnd_3285092 := by exact prefixLift 3285092
  have htrace : WordTrace (prefixWord ++ tailWord_3285092) baseStart_3285092 baseEnd_3285092 := by
    simpa [prefixWord, tailWord_3285092, baseEnd_3285092] using wordTrace_append hprefix tailTrace_3285092
  have hstable : (prefixWord ++ tailWord_3285092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285092).length < 2 ^ (prefixWord ++ tailWord_3285092).sum := by decide
  have hdescent : baseEnd_3285092 < baseStart_3285092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285143 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 2, 1, 3]
def baseStart_3285143 : Nat := 118140960795 + 3285143 * 2 ^ 59
def prefixEnd_3285143 : Nat := 4983230072969 + 3 ^ 40 * 3285143 * 2
def baseEnd_3285143 : Nat := 1686857377753345596604409

theorem tailTrace_3285143 : CollatzResearch.WordTrace tailWord_3285143 prefixEnd_3285143 1686857377753345596604409 := by
  unfold tailWord_3285143
  simp only [CollatzResearch.WordTrace]
  refine ⟨119819008737495443601420083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79879339158330295734280055 119819008737495443601420083)
  ·
    refine ⟨179728513106243165402130125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119819008737495443601420083 179728513106243165402130125)
    ·
      refine ⟨67398192414841187025798797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179728513106243165402130125 67398192414841187025798797)
      ·
        refine ⟨25274322155565445134674549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67398192414841187025798797 25274322155565445134674549)
        ·
          refine ⟨2369467702084260481375739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25274322155565445134674549 2369467702084260481375739)
          ·
            refine ⟨3554201553126390722063609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369467702084260481375739 3554201553126390722063609)
            ·
              refine ⟨2665651164844793041547707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554201553126390722063609 2665651164844793041547707)
              ·
                refine ⟨3998476747267189562321561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665651164844793041547707 3998476747267189562321561)
                ·
                  refine ⟨2998857560450392171741171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998476747267189562321561 2998857560450392171741171)
                  ·
                    refine ⟨4498286340675588257611757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2998857560450392171741171 4498286340675588257611757)
                    ·
                      refine ⟨1686857377753345596604409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4498286340675588257611757 1686857377753345596604409)
                      ·
                        rfl

theorem cell23_3285143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_3285143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285143 prefixEnd_3285143 := by exact prefixLift 3285143
  have htrace : WordTrace (prefixWord ++ tailWord_3285143) baseStart_3285143 baseEnd_3285143 := by
    simpa [prefixWord, tailWord_3285143, baseEnd_3285143] using wordTrace_append hprefix tailTrace_3285143
  have hstable : (prefixWord ++ tailWord_3285143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285143).length < 2 ^ (prefixWord ++ tailWord_3285143).sum := by decide
  have hdescent : baseEnd_3285143 < baseStart_3285143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285225 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 3]
def baseStart_3285225 : Nat := 118140960795 + 3285225 * 2 ^ 59
def prefixEnd_3285225 : Nat := 4983230072969 + 3 ^ 40 * 3285225 * 2
def baseEnd_3285225 : Nat := 1686899483167014275779031

theorem tailTrace_3285225 : CollatzResearch.WordTrace tailWord_3285225 prefixEnd_3285225 1686899483167014275779031 := by
  unfold tailWord_3285225
  simp only [CollatzResearch.WordTrace]
  refine ⟨119821999523198371605905129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79881333015465581070603419 119821999523198371605905129)
  ·
    refine ⟨89866499642398778704428847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119821999523198371605905129 89866499642398778704428847)
    ·
      refine ⟨134799749463598168056643271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89866499642398778704428847 134799749463598168056643271)
      ·
        refine ⟨202199624195397252084964907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134799749463598168056643271 202199624195397252084964907)
        ·
          refine ⟨303299436293095878127447361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202199624195397252084964907 303299436293095878127447361)
          ·
            refine ⟨227474577219821908595585521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303299436293095878127447361 227474577219821908595585521)
            ·
              refine ⟨170605932914866431446689141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227474577219821908595585521 170605932914866431446689141)
              ·
                refine ⟨15994306210768727948127107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170605932914866431446689141 15994306210768727948127107)
                ·
                  refine ⟨23991459316153091922190661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15994306210768727948127107 23991459316153091922190661)
                  ·
                    refine ⟨4498398621778704735410749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23991459316153091922190661 4498398621778704735410749)
                    ·
                      refine ⟨1686899483167014275779031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4498398621778704735410749 1686899483167014275779031)
                      ·
                        rfl

theorem cell23_3285225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_3285225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285225 prefixEnd_3285225 := by exact prefixLift 3285225
  have htrace : WordTrace (prefixWord ++ tailWord_3285225) baseStart_3285225 baseEnd_3285225 := by
    simpa [prefixWord, tailWord_3285225, baseEnd_3285225] using wordTrace_append hprefix tailTrace_3285225
  have hstable : (prefixWord ++ tailWord_3285225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285225).length < 2 ^ (prefixWord ++ tailWord_3285225).sum := by decide
  have hdescent : baseEnd_3285225 < baseStart_3285225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285249 : List Nat := [1, 2, 4, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3285249 : Nat := 118140960795 + 3285249 * 2 ^ 59
def prefixEnd_3285249 : Nat := 4983230072969 + 3 ^ 40 * 3285249 * 2
def baseEnd_3285249 : Nat := 562303935567574060626307

theorem tailTrace_3285249 : CollatzResearch.WordTrace tailWord_3285249 prefixEnd_3285249 562303935567574060626307 := by
  unfold tailWord_3285249
  simp only [CollatzResearch.WordTrace]
  refine ⟨119822874875111423704778801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79881916583407615803185867 119822874875111423704778801)
  ·
    refine ⟨89867156156333567778584101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119822874875111423704778801 89867156156333567778584101)
    ·
      refine ⟨16850091779312543958484519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89867156156333567778584101 16850091779312543958484519)
      ·
        refine ⟨25275137668968815937726779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16850091779312543958484519 25275137668968815937726779)
        ·
          refine ⟨37912706503453223906590169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25275137668968815937726779 37912706503453223906590169)
          ·
            refine ⟨28434529877589917929942627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37912706503453223906590169 28434529877589917929942627)
            ·
              refine ⟨42651794816384876894913941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28434529877589917929942627 42651794816384876894913941)
              ·
                refine ⟨1999302882018041104449091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42651794816384876894913941 1999302882018041104449091)
                ·
                  refine ⟨2998954323027061656673637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999302882018041104449091 2998954323027061656673637)
                  ·
                    refine ⟨562303935567574060626307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998954323027061656673637 562303935567574060626307)
                    ·
                      rfl

theorem cell23_3285249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3285249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285249 prefixEnd_3285249 := by exact prefixLift 3285249
  have htrace : WordTrace (prefixWord ++ tailWord_3285249) baseStart_3285249 baseEnd_3285249 := by
    simpa [prefixWord, tailWord_3285249, baseEnd_3285249] using wordTrace_append hprefix tailTrace_3285249
  have hstable : (prefixWord ++ tailWord_3285249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285249).length < 2 ^ (prefixWord ++ tailWord_3285249).sum := by decide
  have hdescent : baseEnd_3285249 < baseStart_3285249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285275 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 3, 5]
def baseStart_3285275 : Nat := 118140960795 + 3285275 * 2 ^ 59
def prefixEnd_3285275 : Nat := 4983230072969 + 3 ^ 40 * 3285275 * 2
def baseEnd_3285275 : Nat := 562308385733246360051267

theorem tailTrace_3285275 : CollatzResearch.WordTrace tailWord_3285275 prefixEnd_3285275 562308385733246360051267 := by
  unfold tailWord_3285275
  simp only [CollatzResearch.WordTrace]
  refine ⟨119823823173017230145225279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79882548782011486763483519 119823823173017230145225279)
  ·
    refine ⟨179735734759525845217837919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119823823173017230145225279 179735734759525845217837919)
    ·
      refine ⟨269603602139288767826756879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179735734759525845217837919 269603602139288767826756879)
      ·
        refine ⟨404405403208933151740135319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269603602139288767826756879 404405403208933151740135319)
        ·
          refine ⟨606608104813399727610202979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404405403208933151740135319 606608104813399727610202979)
          ·
            refine ⟨909912157220099591415304469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606608104813399727610202979 909912157220099591415304469)
            ·
              refine ⟨42652132369692168347592397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 909912157220099591415304469 42652132369692168347592397)
              ·
                refine ⟨15994549638634563130347149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42652132369692168347592397 15994549638634563130347149)
                ·
                  refine ⟨5997956114487961173880181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15994549638634563130347149 5997956114487961173880181)
                  ·
                    refine ⟨562308385733246360051267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5997956114487961173880181 562308385733246360051267)
                    ·
                      rfl

theorem cell23_3285275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 5].length) (baseStart_3285275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285275 prefixEnd_3285275 := by exact prefixLift 3285275
  have htrace : WordTrace (prefixWord ++ tailWord_3285275) baseStart_3285275 baseEnd_3285275 := by
    simpa [prefixWord, tailWord_3285275, baseEnd_3285275] using wordTrace_append hprefix tailTrace_3285275
  have hstable : (prefixWord ++ tailWord_3285275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285275).length < 2 ^ (prefixWord ++ tailWord_3285275).sum := by decide
  have hdescent : baseEnd_3285275 < baseStart_3285275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285292 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_3285292 : Nat := 118140960795 + 3285292 * 2 ^ 59
def prefixEnd_3285292 : Nat := 4983230072969 + 3 ^ 40 * 3285292 * 2
def baseEnd_3285292 : Nat := 562311295456955171213741

theorem tailTrace_3285292 : CollatzResearch.WordTrace tailWord_3285292 prefixEnd_3285292 562311295456955171213741 := by
  unfold tailWord_3285292
  simp only [CollatzResearch.WordTrace]
  refine ⟨59912221606977821024297065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79882962142637094699062753 59912221606977821024297065)
  ·
    refine ⟨44934166205233365768222799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59912221606977821024297065 44934166205233365768222799)
    ·
      refine ⟨67401249307850048652334199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44934166205233365768222799 67401249307850048652334199)
      ·
        refine ⟨101101873961775072978501299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67401249307850048652334199 101101873961775072978501299)
        ·
          refine ⟨151652810942662609467751949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101101873961775072978501299 151652810942662609467751949)
          ·
            refine ⟨56869804103498478550406981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151652810942662609467751949 56869804103498478550406981)
            ·
              refine ⟨10663088269405964728201309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56869804103498478550406981 10663088269405964728201309)
              ·
                refine ⟨3998658101027236773075491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10663088269405964728201309 3998658101027236773075491)
                ·
                  refine ⟨5997987151540855159613237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998658101027236773075491 5997987151540855159613237)
                  ·
                    refine ⟨562311295456955171213741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5997987151540855159613237 562311295456955171213741)
                    ·
                      rfl

theorem cell23_3285292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_3285292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285292 prefixEnd_3285292 := by exact prefixLift 3285292
  have htrace : WordTrace (prefixWord ++ tailWord_3285292) baseStart_3285292 baseEnd_3285292 := by
    simpa [prefixWord, tailWord_3285292, baseEnd_3285292] using wordTrace_append hprefix tailTrace_3285292
  have hstable : (prefixWord ++ tailWord_3285292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285292).length < 2 ^ (prefixWord ++ tailWord_3285292).sum := by decide
  have hdescent : baseEnd_3285292 < baseStart_3285292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285299 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 2, 3, 2]
def baseStart_3285299 : Nat := 118140960795 + 3285299 * 2 ^ 59
def prefixEnd_3285299 : Nat := 4983230072969 + 3 ^ 40 * 3285299 * 2
def baseEnd_3285299 : Nat := 1686937480735446986253691

theorem tailTrace_3285299 : CollatzResearch.WordTrace tailWord_3285299 prefixEnd_3285299 1686937480735446986253691 := by
  unfold tailWord_3285299
  simp only [CollatzResearch.WordTrace]
  refine ⟨119824698524930282244098951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79883132349953521496065967 119824698524930282244098951)
  ·
    refine ⟨179737047787395423366148427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119824698524930282244098951 179737047787395423366148427)
    ·
      refine ⟨269605571681093135049222641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179737047787395423366148427 269605571681093135049222641)
      ·
        refine ⟨202204178760819851286916981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269605571681093135049222641 202204178760819851286916981)
        ·
          refine ⟨18956641758826861058148467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202204178760819851286916981 18956641758826861058148467)
          ·
            refine ⟨28434962638240291587222701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18956641758826861058148467 28434962638240291587222701)
            ·
              refine ⟨10663110989340109345208513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28434962638240291587222701 10663110989340109345208513)
              ·
                refine ⟨7997333242005082008906385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10663110989340109345208513 7997333242005082008906385)
                ·
                  refine ⟨5997999931503811506679789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7997333242005082008906385 5997999931503811506679789)
                  ·
                    refine ⟨2249249974313929315004921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5997999931503811506679789 2249249974313929315004921)
                    ·
                      refine ⟨1686937480735446986253691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249249974313929315004921 1686937480735446986253691)
                      ·
                        rfl

theorem cell23_3285299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3, 2].length) (baseStart_3285299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285299 prefixEnd_3285299 := by exact prefixLift 3285299
  have htrace : WordTrace (prefixWord ++ tailWord_3285299) baseStart_3285299 baseEnd_3285299 := by
    simpa [prefixWord, tailWord_3285299, baseEnd_3285299] using wordTrace_append hprefix tailTrace_3285299
  have hstable : (prefixWord ++ tailWord_3285299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285299).length < 2 ^ (prefixWord ++ tailWord_3285299).sum := by decide
  have hdescent : baseEnd_3285299 < baseStart_3285299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285306 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_3285306 : Nat := 118140960795 + 3285306 * 2 ^ 59
def prefixEnd_3285306 : Nat := 4983230072969 + 3 ^ 40 * 3285306 * 2
def baseEnd_3285306 : Nat := 1686941075100028458866159

theorem tailTrace_3285306 : CollatzResearch.WordTrace tailWord_3285306 prefixEnd_3285306 1686941075100028458866159 := by
  unfold tailWord_3285306
  simp only [CollatzResearch.WordTrace]
  refine ⟨29956238458976230609900943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79883302557269948293069181 29956238458976230609900943)
  ·
    refine ⟨44934357688464345914851415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29956238458976230609900943 44934357688464345914851415)
    ·
      refine ⟨67401536532696518872277123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44934357688464345914851415 67401536532696518872277123)
      ·
        refine ⟨101102304799044778308415685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67401536532696518872277123 101102304799044778308415685)
        ·
          refine ⟨18956682149820895932827941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101102304799044778308415685 18956682149820895932827941)
          ·
            refine ⟨3554377903091417987405239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18956682149820895932827941 3554377903091417987405239)
            ·
              refine ⟨5331566854637126981107859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554377903091417987405239 5331566854637126981107859)
              ·
                refine ⟨7997350281955690471661789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5331566854637126981107859 7997350281955690471661789)
                ·
                  refine ⟨2999006355733383926873171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7997350281955690471661789 2999006355733383926873171)
                  ·
                    refine ⟨4498509533600075890309757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2999006355733383926873171 4498509533600075890309757)
                    ·
                      refine ⟨1686941075100028458866159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4498509533600075890309757 1686941075100028458866159)
                      ·
                        rfl

theorem cell23_3285306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_3285306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285306 prefixEnd_3285306 := by exact prefixLift 3285306
  have htrace : WordTrace (prefixWord ++ tailWord_3285306) baseStart_3285306 baseEnd_3285306 := by
    simpa [prefixWord, tailWord_3285306, baseEnd_3285306] using wordTrace_append hprefix tailTrace_3285306
  have hstable : (prefixWord ++ tailWord_3285306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285306).length < 2 ^ (prefixWord ++ tailWord_3285306).sum := by decide
  have hdescent : baseEnd_3285306 < baseStart_3285306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285312 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 2, 6, 2]
def baseStart_3285312 : Nat := 118140960795 + 3285312 * 2 ^ 59
def prefixEnd_3285312 : Nat := 4983230072969 + 3 ^ 40 * 3285312 * 2
def baseEnd_3285312 : Nat := 1686944155983955435391131

theorem tailTrace_3285312 : CollatzResearch.WordTrace tailWord_3285312 prefixEnd_3285312 1686944155983955435391131 := by
  unfold tailWord_3285312
  simp only [CollatzResearch.WordTrace]
  refine ⟨59912586336941592732161095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79883448449255456976214793 59912586336941592732161095)
  ·
    refine ⟨89868879505412389098241643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59912586336941592732161095 89868879505412389098241643)
    ·
      refine ⟨134803319258118583647362465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89868879505412389098241643 134803319258118583647362465)
      ·
        refine ⟨101102489443588937735521849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134803319258118583647362465 101102489443588937735521849)
        ·
          refine ⟨75826867082691703301641387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101102489443588937735521849 75826867082691703301641387)
          ·
            refine ⟨113740300624037554952462081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75826867082691703301641387 113740300624037554952462081)
            ·
              refine ⟨85305225468028166214346561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113740300624037554952462081 85305225468028166214346561)
              ·
                refine ⟨63978919101021124660759921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85305225468028166214346561 63978919101021124660759921)
                ·
                  refine ⟨47984189325765843495569941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63978919101021124660759921 47984189325765843495569941)
                  ·
                    refine ⟨2249258874645273913854841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47984189325765843495569941 2249258874645273913854841)
                    ·
                      refine ⟨1686944155983955435391131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249258874645273913854841 1686944155983955435391131)
                      ·
                        rfl

theorem cell23_3285312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_3285312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285312 prefixEnd_3285312 := by exact prefixLift 3285312
  have htrace : WordTrace (prefixWord ++ tailWord_3285312) baseStart_3285312 baseEnd_3285312 := by
    simpa [prefixWord, tailWord_3285312, baseEnd_3285312] using wordTrace_append hprefix tailTrace_3285312
  have hstable : (prefixWord ++ tailWord_3285312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285312).length < 2 ^ (prefixWord ++ tailWord_3285312).sum := by decide
  have hdescent : baseEnd_3285312 < baseStart_3285312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285313 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 6]
def baseStart_3285313 : Nat := 118140960795 + 3285313 * 2 ^ 59
def prefixEnd_3285313 : Nat := 4983230072969 + 3 ^ 40 * 3285313 * 2
def baseEnd_3285313 : Nat := 187438296607178881275403

theorem tailTrace_3285313 : CollatzResearch.WordTrace tailWord_3285313 prefixEnd_3285313 187438296607178881275403 := by
  unfold tailWord_3285313
  simp only [CollatzResearch.WordTrace]
  refine ⟨119825209146879562635108593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79883472764586375090072395 119825209146879562635108593)
  ·
    refine ⟨89868906860159671976331445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119825209146879562635108593 89868906860159671976331445)
    ·
      refine ⟨8425210018139969247781073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89868906860159671976331445 8425210018139969247781073)
      ·
        refine ⟨6318907513604976935835805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8425210018139969247781073 6318907513604976935835805)
        ·
          refine ⟨2369590317601866350938427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6318907513604976935835805 2369590317601866350938427)
          ·
            refine ⟨3554385476402799526407641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369590317601866350938427 3554385476402799526407641)
            ·
              refine ⟨2665789107302099644805731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554385476402799526407641 2665789107302099644805731)
              ·
                refine ⟨3998683660953149467208597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665789107302099644805731 3998683660953149467208597)
                ·
                  refine ⟨187438296607178881275403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3998683660953149467208597 187438296607178881275403)
                  ·
                    rfl

theorem cell23_3285313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 6].length) (baseStart_3285313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285313 prefixEnd_3285313 := by exact prefixLift 3285313
  have htrace : WordTrace (prefixWord ++ tailWord_3285313) baseStart_3285313 baseEnd_3285313 := by
    simpa [prefixWord, tailWord_3285313, baseEnd_3285313] using wordTrace_append hprefix tailTrace_3285313
  have hstable : (prefixWord ++ tailWord_3285313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285313).length < 2 ^ (prefixWord ++ tailWord_3285313).sum := by decide
  have hdescent : baseEnd_3285313 < baseStart_3285313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285329 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_3285329 : Nat := 118140960795 + 3285329 * 2 ^ 59
def prefixEnd_3285329 : Nat := 4983230072969 + 3 ^ 40 * 3285329 * 2
def baseEnd_3285329 : Nat := 1686952885155081868878553

theorem tailTrace_3285329 : CollatzResearch.WordTrace tailWord_3285329 prefixEnd_3285329 1686952885155081868878553 := by
  unfold tailWord_3285329
  simp only [CollatzResearch.WordTrace]
  refine ⟨119825792714821597367691041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79883861809881064911794027 119825792714821597367691041)
  ·
    refine ⟨89869344536116198025768281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119825792714821597367691041 89869344536116198025768281)
    ·
      refine ⟨67402008402087148519326211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89869344536116198025768281 67402008402087148519326211)
      ·
        refine ⟨101103012603130722778989317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67402008402087148519326211 101103012603130722778989317)
        ·
          refine ⟨18956814863087010521060497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101103012603130722778989317 18956814863087010521060497)
          ·
            refine ⟨14217611147315257890795373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18956814863087010521060497 14217611147315257890795373)
            ·
              refine ⟨5331604180243221709048265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14217611147315257890795373 5331604180243221709048265)
              ·
                refine ⟨3998703135182416281786199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5331604180243221709048265 3998703135182416281786199)
                ·
                  refine ⟨5998054702773624422679299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998703135182416281786199 5998054702773624422679299)
                  ·
                    refine ⟨8997082054160436634018949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5998054702773624422679299 8997082054160436634018949)
                    ·
                      refine ⟨1686952885155081868878553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8997082054160436634018949 1686952885155081868878553)
                      ·
                        rfl

theorem cell23_3285329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_3285329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285329 prefixEnd_3285329 := by exact prefixLift 3285329
  have htrace : WordTrace (prefixWord ++ tailWord_3285329) baseStart_3285329 baseEnd_3285329 := by
    simpa [prefixWord, tailWord_3285329, baseEnd_3285329] using wordTrace_append hprefix tailTrace_3285329
  have hstable : (prefixWord ++ tailWord_3285329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285329).length < 2 ^ (prefixWord ++ tailWord_3285329).sum := by decide
  have hdescent : baseEnd_3285329 < baseStart_3285329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285335 : List Nat := [1, 1, 3, 2, 3, 1, 1, 11]
def baseStart_3285335 : Nat := 118140960795 + 3285335 * 2 ^ 59
def prefixEnd_3285335 : Nat := 4983230072969 + 3 ^ 40 * 3285335 * 2
def baseEnd_3285335 : Nat := 62479850594037364644575

theorem tailTrace_3285335 : CollatzResearch.WordTrace tailWord_3285335 prefixEnd_3285335 62479850594037364644575 := by
  unfold tailWord_3285335
  simp only [CollatzResearch.WordTrace]
  refine ⟨119826011552799860392409459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79884007701866573594939639 119826011552799860392409459)
  ·
    refine ⟨179739017329199790588614189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119826011552799860392409459 179739017329199790588614189)
    ·
      refine ⟨67402131498449921470730321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179739017329199790588614189 67402131498449921470730321)
      ·
        refine ⟨50551598623837441103047741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67402131498449921470730321 50551598623837441103047741)
        ·
          refine ⟨18956849483939040413642903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50551598623837441103047741 18956849483939040413642903)
          ·
            refine ⟨28435274225908560620464355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18956849483939040413642903 28435274225908560620464355)
            ·
              refine ⟨42652911338862840930696533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28435274225908560620464355 42652911338862840930696533)
              ·
                refine ⟨62479850594037364644575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 42652911338862840930696533 62479850594037364644575)
                ·
                  rfl

theorem cell23_3285335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 11].length) (baseStart_3285335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285335 prefixEnd_3285335 := by exact prefixLift 3285335
  have htrace : WordTrace (prefixWord ++ tailWord_3285335) baseStart_3285335 baseEnd_3285335 := by
    simpa [prefixWord, tailWord_3285335, baseEnd_3285335] using wordTrace_append hprefix tailTrace_3285335
  have hstable : (prefixWord ++ tailWord_3285335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285335).length < 2 ^ (prefixWord ++ tailWord_3285335).sum := by decide
  have hdescent : baseEnd_3285335 < baseStart_3285335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285349 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_3285349 : Nat := 118140960795 + 3285349 * 2 ^ 59
def prefixEnd_3285349 : Nat := 4983230072969 + 3 ^ 40 * 3285349 * 2
def baseEnd_3285349 : Nat := 1686963154768171790628461

theorem tailTrace_3285349 : CollatzResearch.WordTrace tailWord_3285349 prefixEnd_3285349 1686963154768171790628461 := by
  unfold tailWord_3285349
  simp only [CollatzResearch.WordTrace]
  refine ⟨119826522174749140783419101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79884348116499427188946067 119826522174749140783419101)
  ·
    refine ⟨44934945815530927793782163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119826522174749140783419101 44934945815530927793782163)
    ·
      refine ⟨67402418723296391690673245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44934945815530927793782163 67402418723296391690673245)
      ·
        refine ⟨25275907021236146884002467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67402418723296391690673245 25275907021236146884002467)
        ·
          refine ⟨37913860531854220326003701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25275907021236146884002467 37913860531854220326003701)
          ·
            refine ⟨3554424424861333155562847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37913860531854220326003701 3554424424861333155562847)
            ·
              refine ⟨5331636637291999733344271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554424424861333155562847 5331636637291999733344271)
              ·
                refine ⟨7997454955937999600016407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5331636637291999733344271 7997454955937999600016407)
                ·
                  refine ⟨11996182433906999400024611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7997454955937999600016407 11996182433906999400024611)
                  ·
                    refine ⟨17994273650860499100036917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11996182433906999400024611 17994273650860499100036917)
                    ·
                      refine ⟨1686963154768171790628461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17994273650860499100036917 1686963154768171790628461)
                      ·
                        rfl

theorem cell23_3285349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_3285349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285349 prefixEnd_3285349 := by exact prefixLift 3285349
  have htrace : WordTrace (prefixWord ++ tailWord_3285349) baseStart_3285349 baseEnd_3285349 := by
    simpa [prefixWord, tailWord_3285349, baseEnd_3285349] using wordTrace_append hprefix tailTrace_3285349
  have hstable : (prefixWord ++ tailWord_3285349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285349).length < 2 ^ (prefixWord ++ tailWord_3285349).sum := by decide
  have hdescent : baseEnd_3285349 < baseStart_3285349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285356 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_3285356 : Nat := 118140960795 + 3285356 * 2 ^ 59
def prefixEnd_3285356 : Nat := 4983230072969 + 3 ^ 40 * 3285356 * 2
def baseEnd_3285356 : Nat := 562322249710917754413643

theorem tailTrace_3285356 : CollatzResearch.WordTrace tailWord_3285356 prefixEnd_3285356 562322249710917754413643 := by
  unfold tailWord_3285356
  simp only [CollatzResearch.WordTrace]
  refine ⟨59913388742861890489461961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79884518323815853985949281 59913388742861890489461961)
  ·
    refine ⟨44935041557146417867096471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59913388742861890489461961 44935041557146417867096471)
    ·
      refine ⟨67402562335719626800644707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44935041557146417867096471 67402562335719626800644707)
      ·
        refine ⟨101103843503579440200967061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67402562335719626800644707 101103843503579440200967061)
        ·
          refine ⟨4739242664230286259420331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101103843503579440200967061 4739242664230286259420331)
          ·
            refine ⟨7108863996345429389130497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739242664230286259420331 7108863996345429389130497)
            ·
              refine ⟨5331647997259072041847873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7108863996345429389130497 5331647997259072041847873)
              ·
                refine ⟨3998735997944304031385905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5331647997259072041847873 3998735997944304031385905)
                ·
                  refine ⟨2999051998458228023539429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998735997944304031385905 2999051998458228023539429)
                  ·
                    refine ⟨562322249710917754413643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2999051998458228023539429 562322249710917754413643)
                    ·
                      rfl

theorem cell23_3285356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_3285356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285356 prefixEnd_3285356 := by exact prefixLift 3285356
  have htrace : WordTrace (prefixWord ++ tailWord_3285356) baseStart_3285356 baseEnd_3285356 := by
    simpa [prefixWord, tailWord_3285356, baseEnd_3285356] using wordTrace_append hprefix tailTrace_3285356
  have hstable : (prefixWord ++ tailWord_3285356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285356).length < 2 ^ (prefixWord ++ tailWord_3285356).sum := by decide
  have hdescent : baseEnd_3285356 < baseStart_3285356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285386 : List Nat := [3, 1, 2, 5, 1, 1, 3, 7]
def baseStart_3285386 : Nat := 118140960795 + 3285386 * 2 ^ 59
def prefixEnd_3285386 : Nat := 4983230072969 + 3 ^ 40 * 3285386 * 2
def baseEnd_3285386 : Nat := 62480820501940301698733

theorem tailTrace_3285386 : CollatzResearch.WordTrace tailWord_3285386 prefixEnd_3285386 62480820501940301698733 := by
  unfold tailWord_3285386
  simp only [CollatzResearch.WordTrace]
  refine ⟨29956967918903774025629003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79885247783743397401677341 29956967918903774025629003)
  ·
    refine ⟨44935451878355661038443505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29956967918903774025629003 44935451878355661038443505)
    ·
      refine ⟨33701588908766745778832629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44935451878355661038443505 33701588908766745778832629)
      ·
        refine ⟨3159523960196882416765559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33701588908766745778832629 3159523960196882416765559)
        ·
          refine ⟨4739285940295323625148339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159523960196882416765559 4739285940295323625148339)
          ·
            refine ⟨7108928910442985437722509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739285940295323625148339 7108928910442985437722509)
            ·
              refine ⟨2665848341416119539145941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7108928910442985437722509 2665848341416119539145941)
              ·
                refine ⟨62480820501940301698733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2665848341416119539145941 62480820501940301698733)
                ·
                  rfl

theorem cell23_3285386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_3285386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285386 prefixEnd_3285386 := by exact prefixLift 3285386
  have htrace : WordTrace (prefixWord ++ tailWord_3285386) baseStart_3285386 baseEnd_3285386 := by
    simpa [prefixWord, tailWord_3285386, baseEnd_3285386] using wordTrace_append hprefix tailTrace_3285386
  have hstable : (prefixWord ++ tailWord_3285386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285386).length < 2 ^ (prefixWord ++ tailWord_3285386).sum := by decide
  have hdescent : baseEnd_3285386 < baseStart_3285386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285412 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_3285412 : Nat := 118140960795 + 3285412 * 2 ^ 59
def prefixEnd_3285412 : Nat := 4983230072969 + 3 ^ 40 * 3285412 * 2
def baseEnd_3285412 : Nat := 562331834683135014713557

theorem tailTrace_3285412 : CollatzResearch.WordTrace tailWord_3285412 prefixEnd_3285412 562331834683135014713557 := by
  unfold tailWord_3285412
  simp only [CollatzResearch.WordTrace]
  refine ⟨59914409986760451271481245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79885879982347268361974993 59914409986760451271481245)
  ·
    refine ⟨22467903745035169226805467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59914409986760451271481245 22467903745035169226805467)
    ·
      refine ⟨33701855617552753840208201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22467903745035169226805467 33701855617552753840208201)
      ·
        refine ⟨25276391713164565380156151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33701855617552753840208201 25276391713164565380156151)
        ·
          refine ⟨37914587569746848070234227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25276391713164565380156151 37914587569746848070234227)
          ·
            refine ⟨56871881354620272105351341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37914587569746848070234227 56871881354620272105351341)
            ·
              refine ⟨21326955507982602039506753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56871881354620272105351341 21326955507982602039506753)
              ·
                refine ⟨15995216630986951529630065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21326955507982602039506753 15995216630986951529630065)
                ·
                  refine ⟨11996412473240213647222549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15995216630986951529630065 11996412473240213647222549)
                  ·
                    refine ⟨562331834683135014713557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11996412473240213647222549 562331834683135014713557)
                    ·
                      rfl

theorem cell23_3285412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_3285412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285412 prefixEnd_3285412 := by exact prefixLift 3285412
  have htrace : WordTrace (prefixWord ++ tailWord_3285412) baseStart_3285412 baseEnd_3285412 := by
    simpa [prefixWord, tailWord_3285412, baseEnd_3285412] using wordTrace_append hprefix tailTrace_3285412
  have hstable : (prefixWord ++ tailWord_3285412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285412).length < 2 ^ (prefixWord ++ tailWord_3285412).sum := by decide
  have hdescent : baseEnd_3285412 < baseStart_3285412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285509 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_3285509 : Nat := 118140960795 + 3285509 * 2 ^ 59
def prefixEnd_3285509 : Nat := 4983230072969 + 3 ^ 40 * 3285509 * 2
def baseEnd_3285509 : Nat := 1687045311672891164627725

theorem tailTrace_3285509 : CollatzResearch.WordTrace tailWord_3285509 prefixEnd_3285509 1687045311672891164627725 := by
  unfold tailWord_3285509
  simp only [CollatzResearch.WordTrace]
  refine ⟨119832357854169488109243581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79888238569446325406162387 119832357854169488109243581)
  ·
    refine ⟨44937134195313558040966343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119832357854169488109243581 44937134195313558040966343)
    ·
      refine ⟨67405701292970337061449515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44937134195313558040966343 67405701292970337061449515)
      ·
        refine ⟨101108551939455505592174273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67405701292970337061449515 101108551939455505592174273)
        ·
          refine ⟨75831413954591629194130705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101108551939455505592174273 75831413954591629194130705)
          ·
            refine ⟨56873560465943721895598029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75831413954591629194130705 56873560465943721895598029)
            ·
              refine ⟨21327585174728895710849261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56873560465943721895598029 21327585174728895710849261)
              ·
                refine ⟨7997844440523335891568473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21327585174728895710849261 7997844440523335891568473)
                ·
                  refine ⟨5998383330392501918676355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7997844440523335891568473 5998383330392501918676355)
                  ·
                    refine ⟨8997574995588752878014533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5998383330392501918676355 8997574995588752878014533)
                    ·
                      refine ⟨1687045311672891164627725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8997574995588752878014533 1687045311672891164627725)
                      ·
                        rfl

theorem cell23_3285509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_3285509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285509 prefixEnd_3285509 := by exact prefixLift 3285509
  have htrace : WordTrace (prefixWord ++ tailWord_3285509) baseStart_3285509 baseEnd_3285509 := by
    simpa [prefixWord, tailWord_3285509, baseEnd_3285509] using wordTrace_append hprefix tailTrace_3285509
  have hstable : (prefixWord ++ tailWord_3285509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285509).length < 2 ^ (prefixWord ++ tailWord_3285509).sum := by decide
  have hdescent : baseEnd_3285509 < baseStart_3285509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285527 : List Nat := [1, 1, 3, 6, 2, 1, 2, 2, 5]
def baseStart_3285527 : Nat := 118140960795 + 3285527 * 2 ^ 59
def prefixEnd_3285527 : Nat := 4983230072969 + 3 ^ 40 * 3285527 * 2
def baseEnd_3285527 : Nat := 187450506036074677133627

theorem tailTrace_3285527 : CollatzResearch.WordTrace tailWord_3285527 prefixEnd_3285527 187450506036074677133627 := by
  unfold tailWord_3285527
  simp only [CollatzResearch.WordTrace]
  refine ⟨119833014368104277183398835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79888676245402851455599223 119833014368104277183398835)
  ·
    refine ⟨179749521552156415775098253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119833014368104277183398835 179749521552156415775098253)
    ·
      refine ⟨67406070582058655915661845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179749521552156415775098253 67406070582058655915661845)
      ·
        refine ⟨3159659558533999496046649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67406070582058655915661845 3159659558533999496046649)
        ·
          refine ⟨2369744668900499622034987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3159659558533999496046649 2369744668900499622034987)
          ·
            refine ⟨3554617003350749433052481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369744668900499622034987 3554617003350749433052481)
            ·
              refine ⟨2665962752513062074789361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554617003350749433052481 2665962752513062074789361)
              ·
                refine ⟨1999472064384796556092021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665962752513062074789361 1999472064384796556092021)
                ·
                  refine ⟨187450506036074677133627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1999472064384796556092021 187450506036074677133627)
                  ·
                    rfl

theorem cell23_3285527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 5].length) (baseStart_3285527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285527 prefixEnd_3285527 := by exact prefixLift 3285527
  have htrace : WordTrace (prefixWord ++ tailWord_3285527) baseStart_3285527 baseEnd_3285527 := by
    simpa [prefixWord, tailWord_3285527, baseEnd_3285527] using wordTrace_append hprefix tailTrace_3285527
  have hstable : (prefixWord ++ tailWord_3285527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285527).length < 2 ^ (prefixWord ++ tailWord_3285527).sum := by decide
  have hdescent : baseEnd_3285527 < baseStart_3285527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285599 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_3285599 : Nat := 118140960795 + 3285599 * 2 ^ 59
def prefixEnd_3285599 : Nat := 4983230072969 + 3 ^ 40 * 3285599 * 2
def baseEnd_3285599 : Nat := 1687091524931795812502311

theorem tailTrace_3285599 : CollatzResearch.WordTrace tailWord_3285599 prefixEnd_3285599 1687091524931795812502311 := by
  unfold tailWord_3285599
  simp only [CollatzResearch.WordTrace]
  refine ⟨119835640423843433480019851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79890426949228955653346567 119835640423843433480019851)
  ·
    refine ⟨179753460635765150220029777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119835640423843433480019851 179753460635765150220029777)
    ·
      refine ⟨134815095476823862665022333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179753460635765150220029777 134815095476823862665022333)
      ·
        refine ⟨50555660803808948499383375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134815095476823862665022333 50555660803808948499383375)
        ·
          refine ⟨75833491205713422749075063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50555660803808948499383375 75833491205713422749075063)
          ·
            refine ⟨113750236808570134123612595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75833491205713422749075063 113750236808570134123612595)
            ·
              refine ⟨170625355212855201185418893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113750236808570134123612595 170625355212855201185418893)
              ·
                refine ⟨63984508204820700444532085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170625355212855201185418893 63984508204820700444532085)
                ·
                  refine ⟨5998547644201940666674883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63984508204820700444532085 5998547644201940666674883)
                  ·
                    refine ⟨8997821466302911000012325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5998547644201940666674883 8997821466302911000012325)
                    ·
                      refine ⟨1687091524931795812502311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8997821466302911000012325 1687091524931795812502311)
                      ·
                        rfl

theorem cell23_3285599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_3285599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285599 prefixEnd_3285599 := by exact prefixLift 3285599
  have htrace : WordTrace (prefixWord ++ tailWord_3285599) baseStart_3285599 baseEnd_3285599 := by
    simpa [prefixWord, tailWord_3285599, baseEnd_3285599] using wordTrace_append hprefix tailTrace_3285599
  have hstable : (prefixWord ++ tailWord_3285599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285599).length < 2 ^ (prefixWord ++ tailWord_3285599).sum := by decide
  have hdescent : baseEnd_3285599 < baseStart_3285599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285613 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_3285613 : Nat := 118140960795 + 3285613 * 2 ^ 59
def prefixEnd_3285613 : Nat := 4983230072969 + 3 ^ 40 * 3285613 * 2
def baseEnd_3285613 : Nat := 562366237886986252575749

theorem tailTrace_3285613 : CollatzResearch.WordTrace tailWord_3285613 prefixEnd_3285613 562366237886986252575749 := by
  unfold tailWord_3285613
  simp only [CollatzResearch.WordTrace]
  refine ⟨119836151045792713871029493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79890767363861809247352995 119836151045792713871029493)
  ·
    refine ⟨11234639160543066925409015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119836151045792713871029493 11234639160543066925409015)
    ·
      refine ⟨16851958740814600388113523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11234639160543066925409015 16851958740814600388113523)
      ·
        refine ⟨25277938111221900582170285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16851958740814600388113523 25277938111221900582170285)
        ·
          refine ⟨9479226791708212718313857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25277938111221900582170285 9479226791708212718313857)
          ·
            refine ⟨7109420093781159538735393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9479226791708212718313857 7109420093781159538735393)
            ·
              refine ⟨5332065070335869654051545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7109420093781159538735393 5332065070335869654051545)
              ·
                refine ⟨3999048802751902240538659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5332065070335869654051545 3999048802751902240538659)
                ·
                  refine ⟨5998573204127853360807989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999048802751902240538659 5998573204127853360807989)
                  ·
                    refine ⟨562366237886986252575749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5998573204127853360807989 562366237886986252575749)
                    ·
                      rfl

theorem cell23_3285613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_3285613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285613 prefixEnd_3285613 := by exact prefixLift 3285613
  have htrace : WordTrace (prefixWord ++ tailWord_3285613) baseStart_3285613 baseEnd_3285613 := by
    simpa [prefixWord, tailWord_3285613, baseEnd_3285613] using wordTrace_append hprefix tailTrace_3285613
  have hstable : (prefixWord ++ tailWord_3285613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285613).length < 2 ^ (prefixWord ++ tailWord_3285613).sum := by decide
  have hdescent : baseEnd_3285613 < baseStart_3285613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285636 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3285636 : Nat := 118140960795 + 3285636 * 2 ^ 59
def prefixEnd_3285636 : Nat := 4983230072969 + 3 ^ 40 * 3285636 * 2
def baseEnd_3285636 : Nat := 1687110523716012167739641

theorem tailTrace_3285636 : CollatzResearch.WordTrace tailWord_3285636 prefixEnd_3285636 1687110523716012167739641 := by
  unfold tailWord_3285636
  simp only [CollatzResearch.WordTrace]
  refine ⟨59918494962354694399558381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79891326616472925866077841 59918494962354694399558381)
  ·
    refine ⟨22469435610883010399834393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59918494962354694399558381 22469435610883010399834393)
    ·
      refine ⟨16852076708162257799875795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22469435610883010399834393 16852076708162257799875795)
      ·
        refine ⟨25278115062243386699813693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16852076708162257799875795 25278115062243386699813693)
        ·
          refine ⟨9479293148341270012430135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25278115062243386699813693 9479293148341270012430135)
          ·
            refine ⟨14218939722511905018645203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9479293148341270012430135 14218939722511905018645203)
            ·
              refine ⟨21328409583767857527967805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14218939722511905018645203 21328409583767857527967805)
              ·
                refine ⟨7998153593912946572987927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21328409583767857527967805 7998153593912946572987927)
                ·
                  refine ⟨11997230390869419859481891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7998153593912946572987927 11997230390869419859481891)
                  ·
                    refine ⟨17995845586304129789222837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11997230390869419859481891 17995845586304129789222837)
                    ·
                      refine ⟨1687110523716012167739641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17995845586304129789222837 1687110523716012167739641)
                      ·
                        rfl

theorem cell23_3285636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3285636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285636 prefixEnd_3285636 := by exact prefixLift 3285636
  have htrace : WordTrace (prefixWord ++ tailWord_3285636) baseStart_3285636 baseEnd_3285636 := by
    simpa [prefixWord, tailWord_3285636, baseEnd_3285636] using wordTrace_append hprefix tailTrace_3285636
  have hstable : (prefixWord ++ tailWord_3285636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285636).length < 2 ^ (prefixWord ++ tailWord_3285636).sum := by decide
  have hdescent : baseEnd_3285636 < baseStart_3285636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285660 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_3285660 : Nat := 118140960795 + 3285660 * 2 ^ 59
def prefixEnd_3285660 : Nat := 4983230072969 + 3 ^ 40 * 3285660 * 2
def baseEnd_3285660 : Nat := 562374282417240024613177

theorem tailTrace_3285660 : CollatzResearch.WordTrace tailWord_3285660 prefixEnd_3285660 562374282417240024613177 := by
  unfold tailWord_3285660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59918932638311220448995217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79891910184414960598660289 59918932638311220448995217)
  ·
    refine ⟨44939199478733415336746413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59918932638311220448995217 44939199478733415336746413)
    ·
      refine ⟨16852199804525030751279905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44939199478733415336746413 16852199804525030751279905)
      ·
        refine ⟨12639149853393773063459929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16852199804525030751279905 12639149853393773063459929)
        ·
          refine ⟨9479362390045329797594947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12639149853393773063459929 9479362390045329797594947)
          ·
            refine ⟨14219043585067994696392421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9479362390045329797594947 14219043585067994696392421)
            ·
              refine ⟨2666070672200249005573579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14219043585067994696392421 2666070672200249005573579)
              ·
                refine ⟨3999106008300373508360369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666070672200249005573579 3999106008300373508360369)
                ·
                  refine ⟨2999329506225280131270277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999106008300373508360369 2999329506225280131270277)
                  ·
                    refine ⟨562374282417240024613177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2999329506225280131270277 562374282417240024613177)
                    ·
                      rfl

theorem cell23_3285660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_3285660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285660 prefixEnd_3285660 := by exact prefixLift 3285660
  have htrace : WordTrace (prefixWord ++ tailWord_3285660) baseStart_3285660 baseEnd_3285660 := by
    simpa [prefixWord, tailWord_3285660, baseEnd_3285660] using wordTrace_append hprefix tailTrace_3285660
  have hstable : (prefixWord ++ tailWord_3285660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285660).length < 2 ^ (prefixWord ++ tailWord_3285660).sum := by decide
  have hdescent : baseEnd_3285660 < baseStart_3285660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285700 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3285700 : Nat := 118140960795 + 3285700 * 2 ^ 59
def prefixEnd_3285700 : Nat := 4983230072969 + 3 ^ 40 * 3285700 * 2
def baseEnd_3285700 : Nat := 1687143386477899917339347

theorem tailTrace_3285700 : CollatzResearch.WordTrace tailWord_3285700 prefixEnd_3285700 1687143386477899917339347 := by
  unfold tailWord_3285700
  simp only [CollatzResearch.WordTrace]
  refine ⟨59919662098238763864723277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79892882797651685152964369 59919662098238763864723277)
  ·
    refine ⟨22469873286839536449271229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59919662098238763864723277 22469873286839536449271229)
    ·
      refine ⟨8426202482564826168476711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22469873286839536449271229 8426202482564826168476711)
      ·
        refine ⟨12639303723847239252715067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426202482564826168476711 12639303723847239252715067)
        ·
          refine ⟨18958955585770858879072601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12639303723847239252715067 18958955585770858879072601)
          ·
            refine ⟨14219216689328144159304451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18958955585770858879072601 14219216689328144159304451)
            ·
              refine ⟨21328825033992216238956677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14219216689328144159304451 21328825033992216238956677)
              ·
                refine ⟨3999154693873540544804377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21328825033992216238956677 3999154693873540544804377)
                ·
                  refine ⟨2999366020405155408603283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999154693873540544804377 2999366020405155408603283)
                  ·
                    refine ⟨4499049030607733112904925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2999366020405155408603283 4499049030607733112904925)
                    ·
                      refine ⟨1687143386477899917339347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499049030607733112904925 1687143386477899917339347)
                      ·
                        rfl

theorem cell23_3285700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3285700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285700 prefixEnd_3285700 := by exact prefixLift 3285700
  have htrace : WordTrace (prefixWord ++ tailWord_3285700) baseStart_3285700 baseEnd_3285700 := by
    simpa [prefixWord, tailWord_3285700, baseEnd_3285700] using wordTrace_append hprefix tailTrace_3285700
  have hstable : (prefixWord ++ tailWord_3285700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285700).length < 2 ^ (prefixWord ++ tailWord_3285700).sum := by decide
  have hdescent : baseEnd_3285700 < baseStart_3285700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285706 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3285706 : Nat := 118140960795 + 3285706 * 2 ^ 59
def prefixEnd_3285706 : Nat := 4983230072969 + 3 ^ 40 * 3285706 * 2
def baseEnd_3285706 : Nat := 1687146467361826893864319

theorem tailTrace_3285706 : CollatzResearch.WordTrace tailWord_3285706 prefixEnd_3285706 1687146467361826893864319 := by
  unfold tailWord_3285706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959885758613947688541243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79893028689637193836109981 29959885758613947688541243)
  ·
    refine ⟨44939828637920921532811865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29959885758613947688541243 44939828637920921532811865)
    ·
      refine ⟨33704871478440691149608899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44939828637920921532811865 33704871478440691149608899)
      ·
        refine ⟨50557307217661036724413349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33704871478440691149608899 50557307217661036724413349)
        ·
          refine ⟨9479495103311444385827503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50557307217661036724413349 9479495103311444385827503)
          ·
            refine ⟨14219242654967166578741255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9479495103311444385827503 14219242654967166578741255)
            ·
              refine ⟨21328863982450749868111883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14219242654967166578741255 21328863982450749868111883)
              ·
                refine ⟨31993295973676124802167825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21328863982450749868111883 31993295973676124802167825)
                ·
                  refine ⟨23994971980257093601625869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31993295973676124802167825 23994971980257093601625869)
                  ·
                    refine ⟨8998114492596410100609701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23994971980257093601625869 8998114492596410100609701)
                    ·
                      refine ⟨1687146467361826893864319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8998114492596410100609701 1687146467361826893864319)
                      ·
                        rfl

theorem cell23_3285706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3285706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285706 prefixEnd_3285706 := by exact prefixLift 3285706
  have htrace : WordTrace (prefixWord ++ tailWord_3285706) baseStart_3285706 baseEnd_3285706 := by
    simpa [prefixWord, tailWord_3285706, baseEnd_3285706] using wordTrace_append hprefix tailTrace_3285706
  have hstable : (prefixWord ++ tailWord_3285706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285706).length < 2 ^ (prefixWord ++ tailWord_3285706).sum := by decide
  have hdescent : baseEnd_3285706 < baseStart_3285706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285739 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7]
def baseStart_3285739 : Nat := 118140960795 + 3285739 * 2 ^ 59
def prefixEnd_3285739 : Nat := 4983230072969 + 3 ^ 40 * 3285739 * 2
def baseEnd_3285739 : Nat := 1687163412223425264751667

theorem tailTrace_3285739 : CollatzResearch.WordTrace tailWord_3285739 prefixEnd_3285739 1687163412223425264751667 := by
  unfold tailWord_3285739
  simp only [CollatzResearch.WordTrace]
  refine ⟨119840746643336237390116271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79893831095557491593410847 119840746643336237390116271)
  ·
    refine ⟨179761119965004356085174407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119840746643336237390116271 179761119965004356085174407)
    ·
      refine ⟨269641679947506534127761611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179761119965004356085174407 269641679947506534127761611)
      ·
        refine ⟨404462519921259801191642417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269641679947506534127761611 404462519921259801191642417)
        ·
          refine ⟨303346889940944850893731813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404462519921259801191642417 303346889940944850893731813)
          ·
            refine ⟨56877541863927159542574715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303346889940944850893731813 56877541863927159542574715)
            ·
              refine ⟨85316312795890739313862073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56877541863927159542574715 85316312795890739313862073)
              ·
                refine ⟨63987234596918054485396555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85316312795890739313862073 63987234596918054485396555)
                ·
                  refine ⟨95980851895377081728094833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63987234596918054485396555 95980851895377081728094833)
                  ·
                    refine ⟨71985638921532811296071125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95980851895377081728094833 71985638921532811296071125)
                    ·
                      refine ⟨1687163412223425264751667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71985638921532811296071125 1687163412223425264751667)
                      ·
                        rfl

theorem cell23_3285739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_3285739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285739 prefixEnd_3285739 := by exact prefixLift 3285739
  have htrace : WordTrace (prefixWord ++ tailWord_3285739) baseStart_3285739 baseEnd_3285739 := by
    simpa [prefixWord, tailWord_3285739, baseEnd_3285739] using wordTrace_append hprefix tailTrace_3285739
  have hstable : (prefixWord ++ tailWord_3285739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285739).length < 2 ^ (prefixWord ++ tailWord_3285739).sum := by decide
  have hdescent : baseEnd_3285739 < baseStart_3285739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285813 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3285813 : Nat := 118140960795 + 3285813 * 2 ^ 59
def prefixEnd_3285813 : Nat := 4983230072969 + 3 ^ 40 * 3285813 * 2
def baseEnd_3285813 : Nat := 1687201409791857975226327

theorem tailTrace_3285813 : CollatzResearch.WordTrace tailWord_3285813 prefixEnd_3285813 1687201409791857975226327 := by
  unfold tailWord_3285813
  simp only [CollatzResearch.WordTrace]
  refine ⟨119843445645068148028310093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79895630430045432018873395 119843445645068148028310093)
  ·
    refine ⟨44941292116900555510616285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119843445645068148028310093 44941292116900555510616285)
    ·
      refine ⟨16852984543837708316481107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44941292116900555510616285 16852984543837708316481107)
      ·
        refine ⟨25279476815756562474721661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16852984543837708316481107 25279476815756562474721661)
        ·
          refine ⟨9479803805908710928020623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25279476815756562474721661 9479803805908710928020623)
          ·
            refine ⟨14219705708863066392030935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9479803805908710928020623 14219705708863066392030935)
            ·
              refine ⟨21329558563294599588046403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14219705708863066392030935 21329558563294599588046403)
              ·
                refine ⟨31994337844941899382069605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21329558563294599588046403 31994337844941899382069605)
                ·
                  refine ⟨5998938345926606134138051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31994337844941899382069605 5998938345926606134138051)
                  ·
                    refine ⟨8998407518889909201207077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5998938345926606134138051 8998407518889909201207077)
                    ·
                      refine ⟨1687201409791857975226327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8998407518889909201207077 1687201409791857975226327)
                      ·
                        rfl

theorem cell23_3285813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3285813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285813 prefixEnd_3285813 := by exact prefixLift 3285813
  have htrace : WordTrace (prefixWord ++ tailWord_3285813) baseStart_3285813 baseEnd_3285813 := by
    simpa [prefixWord, tailWord_3285813, baseEnd_3285813] using wordTrace_append hprefix tailTrace_3285813
  have hstable : (prefixWord ++ tailWord_3285813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285813).length < 2 ^ (prefixWord ++ tailWord_3285813).sum := by decide
  have hdescent : baseEnd_3285813 < baseStart_3285813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285814 : List Nat := [5, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_3285814 : Nat := 118140960795 + 3285814 * 2 ^ 59
def prefixEnd_3285814 : Nat := 4983230072969 + 3 ^ 40 * 3285814 * 2
def baseEnd_3285814 : Nat := 187466880363612496812647

theorem tailTrace_3285814 : CollatzResearch.WordTrace tailWord_3285814 prefixEnd_3285814 187466880363612496812647 := by
  unfold tailWord_3285814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490217632379032824943531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79895654745376350132730997 7490217632379032824943531)
  ·
    refine ⟨11235326448568549237415297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7490217632379032824943531 11235326448568549237415297)
    ·
      refine ⟨8426494836426411928061473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11235326448568549237415297 8426494836426411928061473)
      ·
        refine ⟨6319871127319808946046105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8426494836426411928061473 6319871127319808946046105)
        ·
          refine ⟨4739903345489856709534579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319871127319808946046105 4739903345489856709534579)
          ·
            refine ⟨7109855018234785064301869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739903345489856709534579 7109855018234785064301869)
            ·
              refine ⟨2666195631838044399113201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7109855018234785064301869 2666195631838044399113201)
              ·
                refine ⟨1999646723878533299334901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666195631838044399113201 1999646723878533299334901)
                ·
                  refine ⟨187466880363612496812647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1999646723878533299334901 187466880363612496812647)
                  ·
                    rfl

theorem cell23_3285814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_3285814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285814 prefixEnd_3285814 := by exact prefixLift 3285814
  have htrace : WordTrace (prefixWord ++ tailWord_3285814) baseStart_3285814 baseEnd_3285814 := by
    simpa [prefixWord, tailWord_3285814, baseEnd_3285814] using wordTrace_append hprefix tailTrace_3285814
  have hstable : (prefixWord ++ tailWord_3285814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285814).length < 2 ^ (prefixWord ++ tailWord_3285814).sum := by decide
  have hdescent : baseEnd_3285814 < baseStart_3285814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285850 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_3285850 : Nat := 118140960795 + 3285850 * 2 ^ 59
def prefixEnd_3285850 : Nat := 4983230072969 + 3 ^ 40 * 3285850 * 2
def baseEnd_3285850 : Nat := 1687220408576074330463657

theorem tailTrace_3285850 : CollatzResearch.WordTrace tailWord_3285850 prefixEnd_3285850 1687220408576074330463657 := by
  unfold tailWord_3285850
  simp only [CollatzResearch.WordTrace]
  refine ⟨29961198786483525836851751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79896530097289402231604669 29961198786483525836851751)
  ·
    refine ⟨44941798179725288755277627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29961198786483525836851751 44941798179725288755277627)
    ·
      refine ⟨67412697269587933132916441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44941798179725288755277627 67412697269587933132916441)
      ·
        refine ⟨50559522952190949849687331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67412697269587933132916441 50559522952190949849687331)
        ·
          refine ⟨75839284428286424774530997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50559522952190949849687331 75839284428286424774530997)
          ·
            refine ⟨7109932915151852322612281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75839284428286424774530997 7109932915151852322612281)
            ·
              refine ⟨5332449686363889241959211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7109932915151852322612281 5332449686363889241959211)
              ·
                refine ⟨7998674529545833862938817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5332449686363889241959211 7998674529545833862938817)
                ·
                  refine ⟨5999005897159375397204113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7998674529545833862938817 5999005897159375397204113)
                  ·
                    refine ⟨4499254422869531547903085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5999005897159375397204113 4499254422869531547903085)
                    ·
                      refine ⟨1687220408576074330463657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499254422869531547903085 1687220408576074330463657)
                      ·
                        rfl

theorem cell23_3285850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_3285850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285850 prefixEnd_3285850 := by exact prefixLift 3285850
  have htrace : WordTrace (prefixWord ++ tailWord_3285850) baseStart_3285850 baseEnd_3285850 := by
    simpa [prefixWord, tailWord_3285850, baseEnd_3285850] using wordTrace_append hprefix tailTrace_3285850
  have hstable : (prefixWord ++ tailWord_3285850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285850).length < 2 ^ (prefixWord ++ tailWord_3285850).sum := by decide
  have hdescent : baseEnd_3285850 < baseStart_3285850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285913 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 4, 4]
def baseStart_3285913 : Nat := 118140960795 + 3285913 * 2 ^ 59
def prefixEnd_3285913 : Nat := 4983230072969 + 3 ^ 40 * 3285913 * 2
def baseEnd_3285913 : Nat := 562417585952435861325289

theorem tailTrace_3285913 : CollatzResearch.WordTrace tailWord_3285913 prefixEnd_3285913 562417585952435861325289 := by
  unfold tailWord_3285913
  simp only [CollatzResearch.WordTrace]
  refine ⟨119847092944705865106950393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79898061963137243404633595 119847092944705865106950393)
  ·
    refine ⟨89885319708529398830212795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119847092944705865106950393 89885319708529398830212795)
    ·
      refine ⟨134827979562794098245319193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89885319708529398830212795 134827979562794098245319193)
      ·
        refine ⟨101120984672095573683989395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134827979562794098245319193 101120984672095573683989395)
        ·
          refine ⟨151681477008143360525984093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101120984672095573683989395 151681477008143360525984093)
          ·
            refine ⟨56880553878053760197244035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151681477008143360525984093 56880553878053760197244035)
            ·
              refine ⟨85320830817080640295866053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56880553878053760197244035 85320830817080640295866053)
              ·
                refine ⟨15997655778202620055474885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85320830817080640295866053 15997655778202620055474885)
                ·
                  refine ⟨2999560458412991260401541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15997655778202620055474885 2999560458412991260401541)
                  ·
                    refine ⟨562417585952435861325289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2999560458412991260401541 562417585952435861325289)
                    ·
                      rfl

theorem cell23_3285913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_3285913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285913 prefixEnd_3285913 := by exact prefixLift 3285913
  have htrace : WordTrace (prefixWord ++ tailWord_3285913) baseStart_3285913 baseEnd_3285913 := by
    simpa [prefixWord, tailWord_3285913, baseEnd_3285913] using wordTrace_append hprefix tailTrace_3285913
  have hstable : (prefixWord ++ tailWord_3285913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285913).length < 2 ^ (prefixWord ++ tailWord_3285913).sum := by decide
  have hdescent : baseEnd_3285913 < baseStart_3285913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285974 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3285974 : Nat := 118140960795 + 3285974 * 2 ^ 59
def prefixEnd_3285974 : Nat := 4983230072969 + 3 ^ 40 * 3285974 * 2
def baseEnd_3285974 : Nat := 1687284080177231845313087

theorem tailTrace_3285974 : CollatzResearch.WordTrace tailWord_3285974 prefixEnd_3285974 1687284080177231845313087 := by
  unfold tailWord_3285974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490582362342804532807561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79899545198323248349947317 7490582362342804532807561)
  ·
    refine ⟨5617936771757103399605671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7490582362342804532807561 5617936771757103399605671)
    ·
      refine ⟨8426905157635655099408507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617936771757103399605671 8426905157635655099408507)
      ·
        refine ⟨12640357736453482649112761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426905157635655099408507 12640357736453482649112761)
        ·
          refine ⟨9480268302340111986834571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12640357736453482649112761 9480268302340111986834571)
          ·
            refine ⟨14220402453510167980251857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480268302340111986834571 14220402453510167980251857)
            ·
              refine ⟨10665301840132625985188893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14220402453510167980251857 10665301840132625985188893)
              ·
                refine ⟨3999488190049734744445835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10665301840132625985188893 3999488190049734744445835)
                ·
                  refine ⟨5999232285074602116668753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999488190049734744445835 5999232285074602116668753)
                  ·
                    refine ⟨4499424213805951587501565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5999232285074602116668753 4499424213805951587501565)
                    ·
                      refine ⟨1687284080177231845313087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499424213805951587501565 1687284080177231845313087)
                      ·
                        rfl

theorem cell23_3285974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3285974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285974 prefixEnd_3285974 := by exact prefixLift 3285974
  have htrace : WordTrace (prefixWord ++ tailWord_3285974) baseStart_3285974 baseEnd_3285974 := by
    simpa [prefixWord, tailWord_3285974, baseEnd_3285974] using wordTrace_append hprefix tailTrace_3285974
  have hstable : (prefixWord ++ tailWord_3285974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285974).length < 2 ^ (prefixWord ++ tailWord_3285974).sum := by decide
  have hdescent : baseEnd_3285974 < baseStart_3285974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285987 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3285987 : Nat := 118140960795 + 3285987 * 2 ^ 59
def prefixEnd_3285987 : Nat := 4983230072969 + 3 ^ 40 * 3285987 * 2
def baseEnd_3285987 : Nat := 1687290755425740294450527

theorem tailTrace_3285987 : CollatzResearch.WordTrace tailWord_3285987 prefixEnd_3285987 1687290755425740294450527 := by
  unfold tailWord_3285987
  simp only [CollatzResearch.WordTrace]
  refine ⟨119849791946437775745144215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79899861297625183830096143 119849791946437775745144215)
  ·
    refine ⟨179774687919656663617716323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119849791946437775745144215 179774687919656663617716323)
    ·
      refine ⟨269662031879484995426574485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179774687919656663617716323 269662031879484995426574485)
      ·
        refine ⟨12640407744350859160620679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 269662031879484995426574485 12640407744350859160620679)
        ·
          refine ⟨18960611616526288740931019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12640407744350859160620679 18960611616526288740931019)
          ·
            refine ⟨28440917424789433111396529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18960611616526288740931019 28440917424789433111396529)
            ·
              refine ⟨21330688068592074833547397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28440917424789433111396529 21330688068592074833547397)
              ·
                refine ⟨3999504012861014031290137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21330688068592074833547397 3999504012861014031290137)
                ·
                  refine ⟨2999628009645760523467603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999504012861014031290137 2999628009645760523467603)
                  ·
                    refine ⟨4499442014468640785201405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2999628009645760523467603 4499442014468640785201405)
                    ·
                      refine ⟨1687290755425740294450527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499442014468640785201405 1687290755425740294450527)
                      ·
                        rfl

theorem cell23_3285987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3285987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3285987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3285987 prefixEnd_3285987 := by exact prefixLift 3285987
  have htrace : WordTrace (prefixWord ++ tailWord_3285987) baseStart_3285987 baseEnd_3285987 := by
    simpa [prefixWord, tailWord_3285987, baseEnd_3285987] using wordTrace_append hprefix tailTrace_3285987
  have hstable : (prefixWord ++ tailWord_3285987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285987).length < 2 ^ (prefixWord ++ tailWord_3285987).sum := by decide
  have hdescent : baseEnd_3285987 < baseStart_3285987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286010 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2]
def baseStart_3286010 : Nat := 118140960795 + 3286010 * 2 ^ 59
def prefixEnd_3286010 : Nat := 4983230072969 + 3 ^ 40 * 3286010 * 2
def baseEnd_3286010 : Nat := 1687302565480793704462921

theorem tailTrace_3286010 : CollatzResearch.WordTrace tailWord_3286010 prefixEnd_3286010 1687302565480793704462921 := by
  unfold tailWord_3286010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29962657706338612668307871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79900420550236300448820989 29962657706338612668307871)
  ·
    refine ⟨44943986559507919002461807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29962657706338612668307871 44943986559507919002461807)
    ·
      refine ⟨67415979839261878503692711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44943986559507919002461807 67415979839261878503692711)
      ·
        refine ⟨101123969758892817755539067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67415979839261878503692711 101123969758892817755539067)
        ·
          refine ⟨151685954638339226633308601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101123969758892817755539067 151685954638339226633308601)
          ·
            refine ⟨113764465978754419974981451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151685954638339226633308601 113764465978754419974981451)
            ·
              refine ⟨170646698968131629962472177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113764465978754419974981451 170646698968131629962472177)
              ·
                refine ⟨127985024226098722471854133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170646698968131629962472177 127985024226098722471854133)
                ·
                  refine ⟨11998596021196755231736325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127985024226098722471854133 11998596021196755231736325)
                  ·
                    refine ⟨2249736753974391605950561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11998596021196755231736325 2249736753974391605950561)
                    ·
                      refine ⟨1687302565480793704462921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249736753974391605950561 1687302565480793704462921)
                      ·
                        rfl

theorem cell23_3286010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_3286010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286010 prefixEnd_3286010 := by exact prefixLift 3286010
  have htrace : WordTrace (prefixWord ++ tailWord_3286010) baseStart_3286010 baseEnd_3286010 := by
    simpa [prefixWord, tailWord_3286010, baseEnd_3286010] using wordTrace_append hprefix tailTrace_3286010
  have hstable : (prefixWord ++ tailWord_3286010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286010).length < 2 ^ (prefixWord ++ tailWord_3286010).sum := by decide
  have hdescent : baseEnd_3286010 < baseStart_3286010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286027 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 1, 4, 2]
def baseStart_3286027 : Nat := 118140960795 + 3286027 * 2 ^ 59
def prefixEnd_3286027 : Nat := 4983230072969 + 3 ^ 40 * 3286027 * 2
def baseEnd_3286027 : Nat := 1687311294651920137950343

theorem tailTrace_3286027 : CollatzResearch.WordTrace tailWord_3286027 prefixEnd_3286027 1687311294651920137950343 := by
  unfold tailWord_3286027
  simp only [CollatzResearch.WordTrace]
  refine ⟨119851250866292862576600335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79900833910861908384400223 119851250866292862576600335)
  ·
    refine ⟨179776876299439293864900503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119851250866292862576600335 179776876299439293864900503)
    ·
      refine ⟨269665314449158940797350755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179776876299439293864900503 269665314449158940797350755)
      ·
        refine ⟨404497971673738411196026133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269665314449158940797350755 404497971673738411196026133)
        ·
          refine ⟨18960842422206488024813725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 404497971673738411196026133 18960842422206488024813725)
          ·
            refine ⟨7110315908327433009305147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18960842422206488024813725 7110315908327433009305147)
            ·
              refine ⟨10665473862491149513957721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110315908327433009305147 10665473862491149513957721)
              ·
                refine ⟨7999105396868362135468291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10665473862491149513957721 7999105396868362135468291)
                ·
                  refine ⟨11998658095302543203202437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7999105396868362135468291 11998658095302543203202437)
                  ·
                    refine ⟨2249748392869226850600457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11998658095302543203202437 2249748392869226850600457)
                    ·
                      refine ⟨1687311294651920137950343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249748392869226850600457 1687311294651920137950343)
                      ·
                        rfl

theorem cell23_3286027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4, 2].length) (baseStart_3286027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286027 prefixEnd_3286027 := by exact prefixLift 3286027
  have htrace : WordTrace (prefixWord ++ tailWord_3286027) baseStart_3286027 baseEnd_3286027 := by
    simpa [prefixWord, tailWord_3286027, baseEnd_3286027] using wordTrace_append hprefix tailTrace_3286027
  have hstable : (prefixWord ++ tailWord_3286027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286027).length < 2 ^ (prefixWord ++ tailWord_3286027).sum := by decide
  have hdescent : baseEnd_3286027 < baseStart_3286027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286030 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3286030 : Nat := 118140960795 + 3286030 * 2 ^ 59
def prefixEnd_3286030 : Nat := 4983230072969 + 3 ^ 40 * 3286030 * 2
def baseEnd_3286030 : Nat := 1687312835093883626212829

theorem tailTrace_3286030 : CollatzResearch.WordTrace tailWord_3286030 prefixEnd_3286030 1687312835093883626212829 := by
  unfold tailWord_3286030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14981420035660249261119943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79900906856854662725973029 14981420035660249261119943)
  ·
    refine ⟨22472130053490373891679915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14981420035660249261119943 22472130053490373891679915)
    ·
      refine ⟨33708195080235560837519873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22472130053490373891679915 33708195080235560837519873)
      ·
        refine ⟨25281146310176670628139905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33708195080235560837519873 25281146310176670628139905)
        ·
          refine ⟨18960859732632502971104929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25281146310176670628139905 18960859732632502971104929)
          ·
            refine ⟨14220644799474377228328697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18960859732632502971104929 14220644799474377228328697)
            ·
              refine ⟨10665483599605782921246523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14220644799474377228328697 10665483599605782921246523)
              ·
                refine ⟨15998225399408674381869785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10665483599605782921246523 15998225399408674381869785)
                ·
                  refine ⟨11998669049556505786402339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15998225399408674381869785 11998669049556505786402339)
                  ·
                    refine ⟨17998003574334758679603509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11998669049556505786402339 17998003574334758679603509)
                    ·
                      refine ⟨1687312835093883626212829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17998003574334758679603509 1687312835093883626212829)
                      ·
                        rfl

theorem cell23_3286030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3286030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286030 prefixEnd_3286030 := by exact prefixLift 3286030
  have htrace : WordTrace (prefixWord ++ tailWord_3286030) baseStart_3286030 baseEnd_3286030 := by
    simpa [prefixWord, tailWord_3286030, baseEnd_3286030] using wordTrace_append hprefix tailTrace_3286030
  have hstable : (prefixWord ++ tailWord_3286030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286030).length < 2 ^ (prefixWord ++ tailWord_3286030).sum := by decide
  have hdescent : baseEnd_3286030 < baseStart_3286030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286060 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_3286060 : Nat := 118140960795 + 3286060 * 2 ^ 59
def prefixEnd_3286060 : Nat := 4983230072969 + 3 ^ 40 * 3286060 * 2
def baseEnd_3286060 : Nat := 1687328239513518508837691

theorem tailTrace_3286060 : CollatzResearch.WordTrace tailWord_3286060 prefixEnd_3286060 1687328239513518508837691 := by
  unfold tailWord_3286060
  simp only [CollatzResearch.WordTrace]
  refine ⟨59926227237586654606275817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79901636316782206141701089 59926227237586654606275817)
  ·
    refine ⟨44944670428189990954706863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59926227237586654606275817 44944670428189990954706863)
    ·
      refine ⟨67417005642284986432060295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44944670428189990954706863 67417005642284986432060295)
      ·
        refine ⟨101125508463427479648090443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67417005642284986432060295 101125508463427479648090443)
        ·
          refine ⟨151688262695141219472135665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101125508463427479648090443 151688262695141219472135665)
          ·
            refine ⟨113766197021355914604101749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151688262695141219472135665 113766197021355914604101749)
            ·
              refine ⟨10665580970752116994134539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113766197021355914604101749 10665580970752116994134539)
              ·
                refine ⟨15998371456128175491201809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10665580970752116994134539 15998371456128175491201809)
                ·
                  refine ⟨11998778592096131618401357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15998371456128175491201809 11998778592096131618401357)
                  ·
                    refine ⟨4499541972036049356900509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11998778592096131618401357 4499541972036049356900509)
                    ·
                      refine ⟨1687328239513518508837691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499541972036049356900509 1687328239513518508837691)
                      ·
                        rfl

theorem cell23_3286060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_3286060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286060 prefixEnd_3286060 := by exact prefixLift 3286060
  have htrace : WordTrace (prefixWord ++ tailWord_3286060) baseStart_3286060 baseEnd_3286060 := by
    simpa [prefixWord, tailWord_3286060, baseEnd_3286060] using wordTrace_append hprefix tailTrace_3286060
  have hstable : (prefixWord ++ tailWord_3286060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286060).length < 2 ^ (prefixWord ++ tailWord_3286060).sum := by decide
  have hdescent : baseEnd_3286060 < baseStart_3286060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286117 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 2, 4, 2]
def baseStart_3286117 : Nat := 118140960795 + 3286117 * 2 ^ 59
def prefixEnd_3286117 : Nat := 4983230072969 + 3 ^ 40 * 3286117 * 2
def baseEnd_3286117 : Nat := 1687357507910824785824929

theorem tailTrace_3286117 : CollatzResearch.WordTrace tailWord_3286117 prefixEnd_3286117 1687357507910824785824929 := by
  unfold tailWord_3286117
  simp only [CollatzResearch.WordTrace]
  refine ⟨119854533435966807947376605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79903022290644538631584403 119854533435966807947376605)
  ·
    refine ⟨44945450038487552980266227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119854533435966807947376605 44945450038487552980266227)
    ·
      refine ⟨67418175057731329470399341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44945450038487552980266227 67418175057731329470399341)
      ·
        refine ⟨25281815646649248551399753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67418175057731329470399341 25281815646649248551399753)
        ·
          refine ⟨18961361734986936413549815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25281815646649248551399753 18961361734986936413549815)
          ·
            refine ⟨28442042602480404620324723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18961361734986936413549815 28442042602480404620324723)
            ·
              refine ⟨42663063903720606930487085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28442042602480404620324723 42663063903720606930487085)
              ·
                refine ⟨15998648963895227598932657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42663063903720606930487085 15998648963895227598932657)
                ·
                  refine ⟨11998986722921420699199493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15998648963895227598932657 11998986722921420699199493)
                  ·
                    refine ⟨2249810010547766381099905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11998986722921420699199493 2249810010547766381099905)
                    ·
                      refine ⟨1687357507910824785824929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249810010547766381099905 1687357507910824785824929)
                      ·
                        rfl

theorem cell23_3286117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_3286117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286117 prefixEnd_3286117 := by exact prefixLift 3286117
  have htrace : WordTrace (prefixWord ++ tailWord_3286117) baseStart_3286117 baseEnd_3286117 := by
    simpa [prefixWord, tailWord_3286117, baseEnd_3286117] using wordTrace_append hprefix tailTrace_3286117
  have hstable : (prefixWord ++ tailWord_3286117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286117).length < 2 ^ (prefixWord ++ tailWord_3286117).sum := by decide
  have hdescent : baseEnd_3286117 < baseStart_3286117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286130 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3286130 : Nat := 118140960795 + 3286130 * 2 ^ 59
def prefixEnd_3286130 : Nat := 4983230072969 + 3 ^ 40 * 3286130 * 2
def baseEnd_3286130 : Nat := 1687364183159333234962369

theorem tailTrace_3286130 : CollatzResearch.WordTrace tailWord_3286130 prefixEnd_3286130 1687364183159333234962369 := by
  unfold tailWord_3286130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29963751896229927791899961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79903338389946474111733229 29963751896229927791899961)
  ·
    refine ⟨22472813922172445843924971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29963751896229927791899961 22472813922172445843924971)
    ·
      refine ⟨33709220883258668765887457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22472813922172445843924971 33709220883258668765887457)
      ·
        refine ⟨25281915662444001574415593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33709220883258668765887457 25281915662444001574415593)
        ·
          refine ⟨18961436746833001180811695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25281915662444001574415593 18961436746833001180811695)
          ·
            refine ⟨28442155120249501771217543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18961436746833001180811695 28442155120249501771217543)
            ·
              refine ⟨42663232680374252656826315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28442155120249501771217543 42663232680374252656826315)
              ·
                refine ⟨63994849020561378985239473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42663232680374252656826315 63994849020561378985239473)
                ·
                  refine ⟨47996136765421034238929605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63994849020561378985239473 47996136765421034238929605)
                  ·
                    refine ⟨8999275643516443919799301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47996136765421034238929605 8999275643516443919799301)
                    ·
                      refine ⟨1687364183159333234962369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8999275643516443919799301 1687364183159333234962369)
                      ·
                        rfl

theorem cell23_3286130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3286130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286130 prefixEnd_3286130 := by exact prefixLift 3286130
  have htrace : WordTrace (prefixWord ++ tailWord_3286130) baseStart_3286130 baseEnd_3286130 := by
    simpa [prefixWord, tailWord_3286130, baseEnd_3286130] using wordTrace_append hprefix tailTrace_3286130
  have hstable : (prefixWord ++ tailWord_3286130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286130).length < 2 ^ (prefixWord ++ tailWord_3286130).sum := by decide
  have hdescent : baseEnd_3286130 < baseStart_3286130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286144 : List Nat := [2, 1, 1, 2, 1, 3, 5, 3, 1, 4]
def baseStart_3286144 : Nat := 118140960795 + 3286144 * 2 ^ 59
def prefixEnd_3286144 : Nat := 4983230072969 + 3 ^ 40 * 3286144 * 2
def baseEnd_3286144 : Nat := 562457123962832060062435

theorem tailTrace_3286144 : CollatzResearch.WordTrace tailWord_3286144 prefixEnd_3286144 562457123962832060062435 := by
  unfold tailWord_3286144
  simp only [CollatzResearch.WordTrace]
  refine ⟨59927759103434495779304743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79903678804579327705739657 59927759103434495779304743)
  ·
    refine ⟨89891638655151743668957115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59927759103434495779304743 89891638655151743668957115)
    ·
      refine ⟨134837457982727615503435673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89891638655151743668957115 134837457982727615503435673)
      ·
        refine ⟨101128093487045711627576755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134837457982727615503435673 101128093487045711627576755)
        ·
          refine ⟨151692140230568567441365133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101128093487045711627576755 151692140230568567441365133)
          ·
            refine ⟨56884552586463212790511925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151692140230568567441365133 56884552586463212790511925)
            ·
              refine ⟨5332926804980926199110493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56884552586463212790511925 5332926804980926199110493)
              ·
                refine ⟨1999847551867847324666435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5332926804980926199110493 1999847551867847324666435)
                ·
                  refine ⟨2999771327801770986999653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999847551867847324666435 2999771327801770986999653)
                  ·
                    refine ⟨562457123962832060062435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2999771327801770986999653 562457123962832060062435)
                    ·
                      rfl

theorem cell23_3286144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 4].length) (baseStart_3286144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286144 prefixEnd_3286144 := by exact prefixLift 3286144
  have htrace : WordTrace (prefixWord ++ tailWord_3286144) baseStart_3286144 baseEnd_3286144 := by
    simpa [prefixWord, tailWord_3286144, baseEnd_3286144] using wordTrace_append hprefix tailTrace_3286144
  have hstable : (prefixWord ++ tailWord_3286144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286144).length < 2 ^ (prefixWord ++ tailWord_3286144).sum := by decide
  have hdescent : baseEnd_3286144 < baseStart_3286144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286174 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3286174 : Nat := 118140960795 + 3286174 * 2 ^ 59
def prefixEnd_3286174 : Nat := 4983230072969 + 3 ^ 40 * 3286174 * 2
def baseEnd_3286174 : Nat := 187487419589792340312463

theorem tailTrace_3286174 : CollatzResearch.WordTrace tailWord_3286174 prefixEnd_3286174 187487419589792340312463 := by
  unfold tailWord_3286174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14982076549595038335275197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79904408264506871121467717 14982076549595038335275197)
  ·
    refine ⟨5618278706098139375728199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14982076549595038335275197 5618278706098139375728199)
    ·
      refine ⟨8427418059147209063592299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618278706098139375728199 8427418059147209063592299)
      ·
        refine ⟨12641127088720813595388449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8427418059147209063592299 12641127088720813595388449)
        ·
          refine ⟨9480845316540610196541337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12641127088720813595388449 9480845316540610196541337)
          ·
            refine ⟨7110633987405457647406003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9480845316540610196541337 7110633987405457647406003)
            ·
              refine ⟨10665950981108186471109005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110633987405457647406003 10665950981108186471109005)
              ·
                refine ⟨3999731617915569926665877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10665950981108186471109005 3999731617915569926665877)
                ·
                  refine ⟨187487419589792340312463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3999731617915569926665877 187487419589792340312463)
                  ·
                    rfl

theorem cell23_3286174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3286174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286174 prefixEnd_3286174 := by exact prefixLift 3286174
  have htrace : WordTrace (prefixWord ++ tailWord_3286174) baseStart_3286174 baseEnd_3286174 := by
    simpa [prefixWord, tailWord_3286174, baseEnd_3286174] using wordTrace_append hprefix tailTrace_3286174
  have hstable : (prefixWord ++ tailWord_3286174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286174).length < 2 ^ (prefixWord ++ tailWord_3286174).sum := by decide
  have hdescent : baseEnd_3286174 < baseStart_3286174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286194 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_3286194 : Nat := 118140960795 + 3286194 * 2 ^ 59
def prefixEnd_3286194 : Nat := 4983230072969 + 3 ^ 40 * 3286194 * 2
def baseEnd_3286194 : Nat := 1687397045921220984562075

theorem tailTrace_3286194 : CollatzResearch.WordTrace tailWord_3286194 prefixEnd_3286194 1687397045921220984562075 := by
  unfold tailWord_3286194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29964335464171962524482409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79904894571125233398619757 29964335464171962524482409)
  ·
    refine ⟨22473251598128971893361807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29964335464171962524482409 22473251598128971893361807)
    ·
      refine ⟨33709877397193457840042711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22473251598128971893361807 33709877397193457840042711)
      ·
        refine ⟨50564816095790186760064067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33709877397193457840042711 50564816095790186760064067)
        ·
          refine ⟨75847224143685280140096101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50564816095790186760064067 75847224143685280140096101)
          ·
            refine ⟨14221354526940990026268019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75847224143685280140096101 14221354526940990026268019)
            ·
              refine ⟨21332031790411485039402029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14221354526940990026268019 21332031790411485039402029)
              ·
                refine ⟨7999511921404306889775761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21332031790411485039402029 7999511921404306889775761)
                ·
                  refine ⟨5999633941053230167331821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7999511921404306889775761 5999633941053230167331821)
                  ·
                    refine ⟨2249862727894961312749433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5999633941053230167331821 2249862727894961312749433)
                    ·
                      refine ⟨1687397045921220984562075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249862727894961312749433 1687397045921220984562075)
                      ·
                        rfl

theorem cell23_3286194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_3286194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286194 prefixEnd_3286194 := by exact prefixLift 3286194
  have htrace : WordTrace (prefixWord ++ tailWord_3286194) baseStart_3286194 baseEnd_3286194 := by
    simpa [prefixWord, tailWord_3286194, baseEnd_3286194] using wordTrace_append hprefix tailTrace_3286194
  have hstable : (prefixWord ++ tailWord_3286194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286194).length < 2 ^ (prefixWord ++ tailWord_3286194).sum := by decide
  have hdescent : baseEnd_3286194 < baseStart_3286194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286207 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 4]
def baseStart_3286207 : Nat := 118140960795 + 3286207 * 2 ^ 59
def prefixEnd_3286207 : Nat := 4983230072969 + 3 ^ 40 * 3286207 * 2
def baseEnd_3286207 : Nat := 1687403721169729433699515

theorem tailTrace_3286207 : CollatzResearch.WordTrace tailWord_3286207 prefixEnd_3286207 1687403721169729433699515 := by
  unfold tailWord_3286207
  simp only [CollatzResearch.WordTrace]
  refine ⟨119857816005640753318152875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79905210670427168878768583 119857816005640753318152875)
  ·
    refine ⟨179786724008461129977229313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119857816005640753318152875 179786724008461129977229313)
    ·
      refine ⟨134840043006345847482921985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179786724008461129977229313 134840043006345847482921985)
      ·
        refine ⟨101130032254759385612191489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134840043006345847482921985 101130032254759385612191489)
        ·
          refine ⟨75847524191069539209143617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101130032254759385612191489 75847524191069539209143617)
          ·
            refine ⟨56885643143302154406857713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75847524191069539209143617 56885643143302154406857713)
            ·
              refine ⟨42664232357476615805143285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56885643143302154406857713 42664232357476615805143285)
              ·
                refine ⟨3999771783513432731732183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42664232357476615805143285 3999771783513432731732183)
                ·
                  refine ⟨5999657675270149097598275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999771783513432731732183 5999657675270149097598275)
                  ·
                    refine ⟨8999486512905223646397413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5999657675270149097598275 8999486512905223646397413)
                    ·
                      refine ⟨1687403721169729433699515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8999486512905223646397413 1687403721169729433699515)
                      ·
                        rfl

theorem cell23_3286207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_3286207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286207 prefixEnd_3286207 := by exact prefixLift 3286207
  have htrace : WordTrace (prefixWord ++ tailWord_3286207) baseStart_3286207 baseEnd_3286207 := by
    simpa [prefixWord, tailWord_3286207, baseEnd_3286207] using wordTrace_append hprefix tailTrace_3286207
  have hstable : (prefixWord ++ tailWord_3286207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286207).length < 2 ^ (prefixWord ++ tailWord_3286207).sum := by decide
  have hdescent : baseEnd_3286207 < baseStart_3286207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286218 : List Nat := [3, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_3286218 : Nat := 118140960795 + 3286218 * 2 ^ 59
def prefixEnd_3286218 : Nat := 4983230072969 + 3 ^ 40 * 3286218 * 2
def baseEnd_3286218 : Nat := 1687409369456928890661965

theorem tailTrace_3286218 : CollatzResearch.WordTrace tailWord_3286218 prefixEnd_3286218 1687409369456928890661965 := by
  unfold tailWord_3286218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29964554302150225549200827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79905478139067268131202205 29964554302150225549200827)
  ·
    refine ⟨44946831453225338323801241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29964554302150225549200827 44946831453225338323801241)
    ·
      refine ⟨33710123589919003742850931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44946831453225338323801241 33710123589919003742850931)
      ·
        refine ⟨50565185384878505614276397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33710123589919003742850931 50565185384878505614276397)
        ·
          refine ⟨18961944519329439605353649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50565185384878505614276397 18961944519329439605353649)
          ·
            refine ⟨14221458389497079704015237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18961944519329439605353649 14221458389497079704015237)
            ·
              refine ⟨2666523448030702444502857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14221458389497079704015237 2666523448030702444502857)
              ·
                refine ⟨1999892586023026833377143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666523448030702444502857 1999892586023026833377143)
                ·
                  refine ⟨2999838879034540250065715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999892586023026833377143 2999838879034540250065715)
                  ·
                    refine ⟨4499758318551810375098573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2999838879034540250065715 4499758318551810375098573)
                    ·
                      refine ⟨1687409369456928890661965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499758318551810375098573 1687409369456928890661965)
                      ·
                        rfl

theorem cell23_3286218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_3286218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286218 prefixEnd_3286218 := by exact prefixLift 3286218
  have htrace : WordTrace (prefixWord ++ tailWord_3286218) baseStart_3286218 baseEnd_3286218 := by
    simpa [prefixWord, tailWord_3286218, baseEnd_3286218] using wordTrace_append hprefix tailTrace_3286218
  have hstable : (prefixWord ++ tailWord_3286218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286218).length < 2 ^ (prefixWord ++ tailWord_3286218).sum := by decide
  have hdescent : baseEnd_3286218 < baseStart_3286218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286241 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_3286241 : Nat := 118140960795 + 3286241 * 2 ^ 59
def prefixEnd_3286241 : Nat := 4983230072969 + 3 ^ 40 * 3286241 * 2
def baseEnd_3286241 : Nat := 1687421179511982300674359

theorem tailTrace_3286241 : CollatzResearch.WordTrace tailWord_3286241 prefixEnd_3286241 1687421179511982300674359 := by
  unfold tailWord_3286241
  simp only [CollatzResearch.WordTrace]
  refine ⟨119859056087517577124890577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79906037391678384749927051 119859056087517577124890577)
  ·
    refine ⟨89894292065638182843667933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119859056087517577124890577 89894292065638182843667933)
    ·
      refine ⟨33710359524614318566375475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89894292065638182843667933 33710359524614318566375475)
      ·
        refine ⟨50565539286921477849563213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33710359524614318566375475 50565539286921477849563213)
        ·
          refine ⟨18962077232595554193586205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50565539286921477849563213 18962077232595554193586205)
          ·
            refine ⟨7110778962223332822594827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18962077232595554193586205 7110778962223332822594827)
            ·
              refine ⟨10666168443334999233892241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110778962223332822594827 10666168443334999233892241)
              ·
                refine ⟨7999626332501249425419181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10666168443334999233892241 7999626332501249425419181)
                ·
                  refine ⟨2999859874687968534532193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7999626332501249425419181 2999859874687968534532193)
                  ·
                    refine ⟨2249894906015976400899145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2999859874687968534532193 2249894906015976400899145)
                    ·
                      refine ⟨1687421179511982300674359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249894906015976400899145 1687421179511982300674359)
                      ·
                        rfl

theorem cell23_3286241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_3286241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286241 prefixEnd_3286241 := by exact prefixLift 3286241
  have htrace : WordTrace (prefixWord ++ tailWord_3286241) baseStart_3286241 baseEnd_3286241 := by
    simpa [prefixWord, tailWord_3286241, baseEnd_3286241] using wordTrace_append hprefix tailTrace_3286241
  have hstable : (prefixWord ++ tailWord_3286241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286241).length < 2 ^ (prefixWord ++ tailWord_3286241).sum := by decide
  have hdescent : baseEnd_3286241 < baseStart_3286241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286258 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3286258 : Nat := 118140960795 + 3286258 * 2 ^ 59
def prefixEnd_3286258 : Nat := 4983230072969 + 3 ^ 40 * 3286258 * 2
def baseEnd_3286258 : Nat := 1687429908683108734161781

theorem tailTrace_3286258 : CollatzResearch.WordTrace tailWord_3286258 prefixEnd_3286258 1687429908683108734161781 := by
  unfold tailWord_3286258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29964919032113997257064857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79906450752303992685506285 29964919032113997257064857)
  ·
    refine ⟨22473689274085497942798643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29964919032113997257064857 22473689274085497942798643)
    ·
      refine ⟨33710533911128246914197965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22473689274085497942798643 33710533911128246914197965)
      ·
        refine ⟨12641450216673092592824237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33710533911128246914197965 12641450216673092592824237)
        ·
          refine ⟨4740543831252409722309089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12641450216673092592824237 4740543831252409722309089)
          ·
            refine ⟨3555407873439307291731817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4740543831252409722309089 3555407873439307291731817)
            ·
              refine ⟨2666555905079480468798863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555407873439307291731817 2666555905079480468798863)
              ·
                refine ⟨3999833857619220703198295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666555905079480468798863 3999833857619220703198295)
                ·
                  refine ⟨5999750786428831054797443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999833857619220703198295 5999750786428831054797443)
                  ·
                    refine ⟨8999626179643246582196165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5999750786428831054797443 8999626179643246582196165)
                    ·
                      refine ⟨1687429908683108734161781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8999626179643246582196165 1687429908683108734161781)
                      ·
                        rfl

theorem cell23_3286258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3286258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286258 prefixEnd_3286258 := by exact prefixLift 3286258
  have htrace : WordTrace (prefixWord ++ tailWord_3286258) baseStart_3286258 baseEnd_3286258 := by
    simpa [prefixWord, tailWord_3286258, baseEnd_3286258] using wordTrace_append hprefix tailTrace_3286258
  have hstable : (prefixWord ++ tailWord_3286258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286258).length < 2 ^ (prefixWord ++ tailWord_3286258).sum := by decide
  have hdescent : baseEnd_3286258 < baseStart_3286258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286268 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_3286268 : Nat := 118140960795 + 3286268 * 2 ^ 59
def prefixEnd_3286268 : Nat := 4983230072969 + 3 ^ 40 * 3286268 * 2
def baseEnd_3286268 : Nat := 562478347829884565012245

theorem tailTrace_3286268 : CollatzResearch.WordTrace tailWord_3286268 prefixEnd_3286268 562478347829884565012245 := by
  unfold tailWord_3286268
  simp only [CollatzResearch.WordTrace]
  refine ⟨59930020429209880368061729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79906693905613173824082305 59930020429209880368061729)
  ·
    refine ⟨44947515321907410276046297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59930020429209880368061729 44947515321907410276046297)
    ·
      refine ⟨33710636491430557707034723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44947515321907410276046297 33710636491430557707034723)
      ·
        refine ⟨50565954737145836560552085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33710636491430557707034723 50565954737145836560552085)
        ·
          refine ⟨2370279128303711088775879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50565954737145836560552085 2370279128303711088775879)
          ·
            refine ⟨3555418692455566633163819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370279128303711088775879 3555418692455566633163819)
            ·
              refine ⟨5333128038683349949745729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555418692455566633163819 5333128038683349949745729)
              ·
                refine ⟨3999846029012512462309297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333128038683349949745729 3999846029012512462309297)
                ·
                  refine ⟨2999884521759384346731973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999846029012512462309297 2999884521759384346731973)
                  ·
                    refine ⟨562478347829884565012245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2999884521759384346731973 562478347829884565012245)
                    ·
                      rfl

theorem cell23_3286268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_3286268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286268 prefixEnd_3286268 := by exact prefixLift 3286268
  have htrace : WordTrace (prefixWord ++ tailWord_3286268) baseStart_3286268 baseEnd_3286268 := by
    simpa [prefixWord, tailWord_3286268, baseEnd_3286268] using wordTrace_append hprefix tailTrace_3286268
  have hstable : (prefixWord ++ tailWord_3286268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286268).length < 2 ^ (prefixWord ++ tailWord_3286268).sum := by decide
  have hdescent : baseEnd_3286268 < baseStart_3286268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286334 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3286334 : Nat := 118140960795 + 3286334 * 2 ^ 59
def prefixEnd_3286334 : Nat := 4983230072969 + 3 ^ 40 * 3286334 * 2
def baseEnd_3286334 : Nat := 1687468933212850436811431

theorem tailTrace_3286334 : CollatzResearch.WordTrace tailWord_3286334 prefixEnd_3286334 1687468933212850436811431 := by
  unfold tailWord_3286334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14982806009522581751003257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79908298717453769338684037 14982806009522581751003257)
  ·
    refine ⟨11237104507141936313252443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14982806009522581751003257 11237104507141936313252443)
    ·
      refine ⟨16855656760712904469878665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11237104507141936313252443 16855656760712904469878665)
      ·
        refine ⟨12641742570534678352408999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16855656760712904469878665 12641742570534678352408999)
        ·
          refine ⟨18962613855802017528613499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12641742570534678352408999 18962613855802017528613499)
          ·
            refine ⟨28443920783703026292920249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18962613855802017528613499 28443920783703026292920249)
            ·
              refine ⟨21332940587777269719690187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28443920783703026292920249 21332940587777269719690187)
              ·
                refine ⟨31999410881665904579535281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21332940587777269719690187 31999410881665904579535281)
                ·
                  refine ⟨23999558161249428434651461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31999410881665904579535281 23999558161249428434651461)
                  ·
                    refine ⟨4499917155234267831497149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23999558161249428434651461 4499917155234267831497149)
                    ·
                      refine ⟨1687468933212850436811431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499917155234267831497149 1687468933212850436811431)
                      ·
                        rfl

theorem cell23_3286334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3286334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286334 prefixEnd_3286334 := by exact prefixLift 3286334
  have htrace : WordTrace (prefixWord ++ tailWord_3286334) baseStart_3286334 baseEnd_3286334 := by
    simpa [prefixWord, tailWord_3286334, baseEnd_3286334] using wordTrace_append hprefix tailTrace_3286334
  have hstable : (prefixWord ++ tailWord_3286334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286334).length < 2 ^ (prefixWord ++ tailWord_3286334).sum := by decide
  have hdescent : baseEnd_3286334 < baseStart_3286334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286342 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3286342 : Nat := 118140960795 + 3286342 * 2 ^ 59
def prefixEnd_3286342 : Nat := 4983230072969 + 3 ^ 40 * 3286342 * 2
def baseEnd_3286342 : Nat := 1687473041058086405511395

theorem tailTrace_3286342 : CollatzResearch.WordTrace tailWord_3286342 prefixEnd_3286342 1687473041058086405511395 := by
  unfold tailWord_3286342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745710620629739730447415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79908493240101114249544853 3745710620629739730447415)
  ·
    refine ⟨5618565930944609595671123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745710620629739730447415 5618565930944609595671123)
    ·
      refine ⟨8427848896416914393506685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618565930944609595671123 8427848896416914393506685)
      ·
        refine ⟨3160443336156342897565007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8427848896416914393506685 3160443336156342897565007)
        ·
          refine ⟨4740665004234514346347511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160443336156342897565007 4740665004234514346347511)
          ·
            refine ⟨7110997506351771519521267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740665004234514346347511 7110997506351771519521267)
            ·
              refine ⟨10666496259527657279281901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110997506351771519521267 10666496259527657279281901)
              ·
                refine ⟨3999936097322871479730713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10666496259527657279281901 3999936097322871479730713)
                ·
                  refine ⟨2999952072992153609798035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999936097322871479730713 2999952072992153609798035)
                  ·
                    refine ⟨4499928109488230414697053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2999952072992153609798035 4499928109488230414697053)
                    ·
                      refine ⟨1687473041058086405511395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499928109488230414697053 1687473041058086405511395)
                      ·
                        rfl

theorem cell23_3286342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3286342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286342 prefixEnd_3286342 := by exact prefixLift 3286342
  have htrace : WordTrace (prefixWord ++ tailWord_3286342) baseStart_3286342 baseEnd_3286342 := by
    simpa [prefixWord, tailWord_3286342, baseEnd_3286342] using wordTrace_append hprefix tailTrace_3286342
  have hstable : (prefixWord ++ tailWord_3286342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286342).length < 2 ^ (prefixWord ++ tailWord_3286342).sum := by decide
  have hdescent : baseEnd_3286342 < baseStart_3286342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286347 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 3]
def baseStart_3286347 : Nat := 118140960795 + 3286347 * 2 ^ 59
def prefixEnd_3286347 : Nat := 4983230072969 + 3 ^ 40 * 3286347 * 2
def baseEnd_3286347 : Nat := 1687475608461358885948871

theorem tailTrace_3286347 : CollatzResearch.WordTrace tailWord_3286347 prefixEnd_3286347 1687475608461358885948871 := by
  unfold tailWord_3286347
  simp only [CollatzResearch.WordTrace]
  refine ⟨119862922225133557228249295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79908614816755704818832863 119862922225133557228249295)
  ·
    refine ⟨179794383337700335842373943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119862922225133557228249295 179794383337700335842373943)
    ·
      refine ⟨269691575006550503763560915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179794383337700335842373943 269691575006550503763560915)
      ·
        refine ⟨404537362509825755645341373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269691575006550503763560915 404537362509825755645341373)
        ·
          refine ⟨151701510941184658367003015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404537362509825755645341373 151701510941184658367003015)
          ·
            refine ⟨227552266411776987550504523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151701510941184658367003015 227552266411776987550504523)
            ·
              refine ⟨341328399617665481325756785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227552266411776987550504523 341328399617665481325756785)
              ·
                refine ⟨255996299713249110994317589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341328399617665481325756785 255996299713249110994317589)
                ·
                  refine ⟨11999826549058552077858637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 255996299713249110994317589 11999826549058552077858637)
                  ·
                    refine ⟨4499934955896957029196989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11999826549058552077858637 4499934955896957029196989)
                    ·
                      refine ⟨1687475608461358885948871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4499934955896957029196989 1687475608461358885948871)
                      ·
                        rfl

theorem cell23_3286347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 3].length) (baseStart_3286347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286347 prefixEnd_3286347 := by exact prefixLift 3286347
  have htrace : WordTrace (prefixWord ++ tailWord_3286347) baseStart_3286347 baseEnd_3286347 := by
    simpa [prefixWord, tailWord_3286347, baseEnd_3286347] using wordTrace_append hprefix tailTrace_3286347
  have hstable : (prefixWord ++ tailWord_3286347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286347).length < 2 ^ (prefixWord ++ tailWord_3286347).sum := by decide
  have hdescent : baseEnd_3286347 < baseStart_3286347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286348 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 2, 2, 2]
def baseStart_3286348 : Nat := 118140960795 + 3286348 * 2 ^ 59
def prefixEnd_3286348 : Nat := 4983230072969 + 3 ^ 40 * 3286348 * 2
def baseEnd_3286348 : Nat := 1687476121942013382036367

theorem tailTrace_3286348 : CollatzResearch.WordTrace tailWord_3286348 prefixEnd_3286348 1687476121942013382036367 := by
  unfold tailWord_3286348
  simp only [CollatzResearch.WordTrace]
  refine ⟨59931479349064967199517849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79908639132086622932690465 59931479349064967199517849)
  ·
    refine ⟨44948609511798725399638387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59931479349064967199517849 44948609511798725399638387)
    ·
      refine ⟨67422914267698088099457581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44948609511798725399638387 67422914267698088099457581)
      ·
        refine ⟨25283592850386783037296593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67422914267698088099457581 25283592850386783037296593)
        ·
          refine ⟨18962694637790087277972445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25283592850386783037296593 18962694637790087277972445)
          ·
            refine ⟨7111010489171282729239667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18962694637790087277972445 7111010489171282729239667)
            ·
              refine ⟨10666515733756924093859501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111010489171282729239667 10666515733756924093859501)
              ·
                refine ⟨3999943400158846535197313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10666515733756924093859501 3999943400158846535197313)
                ·
                  refine ⟨2999957550119134901397985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999943400158846535197313 2999957550119134901397985)
                  ·
                    refine ⟨2249968162589351176048489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2999957550119134901397985 2249968162589351176048489)
                    ·
                      refine ⟨1687476121942013382036367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2249968162589351176048489 1687476121942013382036367)
                      ·
                        rfl

theorem cell23_3286348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_3286348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3286348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3286348 prefixEnd_3286348 := by exact prefixLift 3286348
  have htrace : WordTrace (prefixWord ++ tailWord_3286348) baseStart_3286348 baseEnd_3286348 := by
    simpa [prefixWord, tailWord_3286348, baseEnd_3286348] using wordTrace_append hprefix tailTrace_3286348
  have hstable : (prefixWord ++ tailWord_3286348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286348).length < 2 ^ (prefixWord ++ tailWord_3286348).sum := by decide
  have hdescent : baseEnd_3286348 < baseStart_3286348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
