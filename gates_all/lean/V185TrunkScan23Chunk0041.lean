import V185TrunkScan23Chunk0040

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_243274 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_243274 : Nat := 118140960795 + 243274 * 2 ^ 59
def prefixEnd_243274 : Nat := 4983230072969 + 3 ^ 40 * 243274 * 2
def baseEnd_243274 : Nat := 124916492741986423056209

theorem tailTrace_243274 : CollatzResearch.WordTrace tailWord_243274 prefixEnd_243274 124916492741986423056209 := by
  unfold tailWord_243274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218232930166830184128219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5915287813778213824341917 2218232930166830184128219)
  ·
    refine ⟨3327349395250245276192329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2218232930166830184128219 3327349395250245276192329)
    ·
      refine ⟨2495512046437683957144247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3327349395250245276192329 2495512046437683957144247)
      ·
        refine ⟨3743268069656525935716371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495512046437683957144247 3743268069656525935716371)
        ·
          refine ⟨5614902104484788903574557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743268069656525935716371 5614902104484788903574557)
          ·
            refine ⟨2105588289181795838840459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5614902104484788903574557 2105588289181795838840459)
            ·
              refine ⟨3158382433772693758260689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105588289181795838840459 3158382433772693758260689)
              ·
                refine ⟨2368786825329520318695517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158382433772693758260689 2368786825329520318695517)
                ·
                  refine ⟨888295059498570119510819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2368786825329520318695517 888295059498570119510819)
                  ·
                    refine ⟨1332442589247855179266229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888295059498570119510819 1332442589247855179266229)
                    ·
                      refine ⟨124916492741986423056209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1332442589247855179266229 124916492741986423056209)
                      ·
                        rfl

theorem cell23_243274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_243274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243274 prefixEnd_243274 := by exact prefixLift 243274
  have htrace : WordTrace (prefixWord ++ tailWord_243274) baseStart_243274 baseEnd_243274 := by
    simpa [prefixWord, tailWord_243274, baseEnd_243274] using wordTrace_append hprefix tailTrace_243274
  have hstable : (prefixWord ++ tailWord_243274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243274).length < 2 ^ (prefixWord ++ tailWord_243274).sum := by decide
  have hdescent : baseEnd_243274 < baseStart_243274 := by decide
  rcases family_descends (prefixWord ++ tailWord_243274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243282 : List Nat := [3, 2, 2, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_243282 : Nat := 118140960795 + 243282 * 2 ^ 59
def prefixEnd_243282 : Nat := 4983230072969 + 3 ^ 40 * 243282 * 2
def baseEnd_243282 : Nat := 124920600587222391756173

theorem tailTrace_243282 : CollatzResearch.WordTrace tailWord_243282 prefixEnd_243282 124920600587222391756173 := by
  unfold tailWord_243282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218305876159584525701025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5915482336425558735202733 2218305876159584525701025)
  ·
    refine ⟨1663729407119688394275769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2218305876159584525701025 1663729407119688394275769)
    ·
      refine ⟨1247797055339766295706827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1663729407119688394275769 1247797055339766295706827)
      ·
        refine ⟨1871695583009649443560241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247797055339766295706827 1871695583009649443560241)
        ·
          refine ⟨1403771687257237082670181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1871695583009649443560241 1403771687257237082670181)
          ·
            refine ⟨263207191360731953000659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1403771687257237082670181 263207191360731953000659)
            ·
              refine ⟨394810787041097929500989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263207191360731953000659 394810787041097929500989)
              ·
                refine ⟨148054045140411723562871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394810787041097929500989 148054045140411723562871)
                ·
                  refine ⟨222081067710617585344307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148054045140411723562871 222081067710617585344307)
                  ·
                    refine ⟨333121601565926378016461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222081067710617585344307 333121601565926378016461)
                    ·
                      refine ⟨124920600587222391756173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333121601565926378016461 124920600587222391756173)
                      ·
                        rfl

theorem cell23_243282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_243282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243282 prefixEnd_243282 := by exact prefixLift 243282
  have htrace : WordTrace (prefixWord ++ tailWord_243282) baseStart_243282 baseEnd_243282 := by
    simpa [prefixWord, tailWord_243282, baseEnd_243282] using wordTrace_append hprefix tailTrace_243282
  have hstable : (prefixWord ++ tailWord_243282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243282).length < 2 ^ (prefixWord ++ tailWord_243282).sum := by decide
  have hdescent : baseEnd_243282 < baseStart_243282 := by decide
  rcases family_descends (prefixWord ++ tailWord_243282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243305 : List Nat := [1, 2, 1, 1, 1, 4, 2, 6, 1, 2, 2]
def baseStart_243305 : Nat := 118140960795 + 243305 * 2 ^ 59
def prefixEnd_243305 : Nat := 4983230072969 + 3 ^ 40 * 243305 * 2
def baseEnd_243305 : Nat := 124932410642275801768567

theorem tailTrace_243305 : CollatzResearch.WordTrace tailWord_243305 prefixEnd_243305 124932410642275801768567 := by
  unfold tailWord_243305
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874062383555013030891369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5916041589036675353927579 8874062383555013030891369)
  ·
    refine ⟨6655546787666259773168527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8874062383555013030891369 6655546787666259773168527)
    ·
      refine ⟨9983320181499389659752791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6655546787666259773168527 9983320181499389659752791)
      ·
        refine ⟨14974980272249084489629187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983320181499389659752791 14974980272249084489629187)
        ·
          refine ⟨22462470408373626734443781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14974980272249084489629187 22462470408373626734443781)
          ·
            refine ⟨4211713201570055012708209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22462470408373626734443781 4211713201570055012708209)
            ·
              refine ⟨3158784901177541259531157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211713201570055012708209 3158784901177541259531157)
              ·
                refine ⟨148068042242697246540523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3158784901177541259531157 148068042242697246540523)
                ·
                  refine ⟨222102063364045869810785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148068042242697246540523 222102063364045869810785)
                  ·
                    refine ⟨166576547523034402358089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222102063364045869810785 166576547523034402358089)
                    ·
                      refine ⟨124932410642275801768567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166576547523034402358089 124932410642275801768567)
                      ·
                        rfl

theorem cell23_243305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 2, 2].length) (baseStart_243305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243305 prefixEnd_243305 := by exact prefixLift 243305
  have htrace : WordTrace (prefixWord ++ tailWord_243305) baseStart_243305 baseEnd_243305 := by
    simpa [prefixWord, tailWord_243305, baseEnd_243305] using wordTrace_append hprefix tailTrace_243305
  have hstable : (prefixWord ++ tailWord_243305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243305).length < 2 ^ (prefixWord ++ tailWord_243305).sum := by decide
  have hdescent : baseEnd_243305 < baseStart_243305 := by decide
  rcases family_descends (prefixWord ++ tailWord_243305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243321 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 3]
def baseStart_243321 : Nat := 118140960795 + 243321 * 2 ^ 59
def prefixEnd_243321 : Nat := 4983230072969 + 3 ^ 40 * 243321 * 2
def baseEnd_243321 : Nat := 124940626332747739168493

theorem tailTrace_243321 : CollatzResearch.WordTrace tailWord_243321 prefixEnd_243321 124940626332747739168493 := by
  unfold tailWord_243321
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874645951497047763473817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5916430634331365175649211 8874645951497047763473817)
  ·
    refine ⟨6655984463622785822605363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8874645951497047763473817 6655984463622785822605363)
    ·
      refine ⟨9983976695434178733908045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6655984463622785822605363 9983976695434178733908045)
      ·
        refine ⟨3743991260787817025215517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9983976695434178733908045 3743991260787817025215517)
        ·
          refine ⟨1403996722795431384455819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3743991260787817025215517 1403996722795431384455819)
          ·
            refine ⟨2105995084193147076683729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403996722795431384455819 2105995084193147076683729)
            ·
              refine ⟨1579496313144860307512797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105995084193147076683729 1579496313144860307512797)
              ·
                refine ⟨592311117429322615317299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1579496313144860307512797 592311117429322615317299)
                ·
                  refine ⟨888466676143983922975949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592311117429322615317299 888466676143983922975949)
                  ·
                    refine ⟨333175003553993971115981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888466676143983922975949 333175003553993971115981)
                    ·
                      refine ⟨124940626332747739168493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333175003553993971115981 124940626332747739168493)
                      ·
                        rfl

theorem cell23_243321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_243321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243321 prefixEnd_243321 := by exact prefixLift 243321
  have htrace : WordTrace (prefixWord ++ tailWord_243321) baseStart_243321 baseEnd_243321 := by
    simpa [prefixWord, tailWord_243321, baseEnd_243321] using wordTrace_append hprefix tailTrace_243321
  have hstable : (prefixWord ++ tailWord_243321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243321).length < 2 ^ (prefixWord ++ tailWord_243321).sum := by decide
  have hdescent : baseEnd_243321 < baseStart_243321 := by decide
  rcases family_descends (prefixWord ++ tailWord_243321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243325 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_243325 : Nat := 118140960795 + 243325 * 2 ^ 59
def prefixEnd_243325 : Nat := 4983230072969 + 3 ^ 40 * 243325 * 2
def baseEnd_243325 : Nat := 124942680255365723518475

theorem tailTrace_243325 : CollatzResearch.WordTrace tailWord_243325 prefixEnd_243325 124942680255365723518475 := by
  unfold tailWord_243325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874791843482556446619429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5916527895655037631079619 8874791843482556446619429)
  ·
    refine ⟨1664023470652979333741143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8874791843482556446619429 1664023470652979333741143)
    ·
      refine ⟨2496035205979469000611715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664023470652979333741143 2496035205979469000611715)
      ·
        refine ⟨3744052808969203500917573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496035205979469000611715 3744052808969203500917573)
        ·
          refine ⟨702009901681725656422045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3744052808969203500917573 702009901681725656422045)
          ·
            refine ⟨263253713130647121158267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 702009901681725656422045 263253713130647121158267)
            ·
              refine ⟨394880569695970681737401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263253713130647121158267 394880569695970681737401)
              ·
                refine ⟨296160427271978011303051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394880569695970681737401 296160427271978011303051)
                ·
                  refine ⟨444240640907967016954577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296160427271978011303051 444240640907967016954577)
                  ·
                    refine ⟨333180480680975262715933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 444240640907967016954577 333180480680975262715933)
                    ·
                      refine ⟨124942680255365723518475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333180480680975262715933 124942680255365723518475)
                      ·
                        rfl

theorem cell23_243325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_243325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243325 prefixEnd_243325 := by exact prefixLift 243325
  have htrace : WordTrace (prefixWord ++ tailWord_243325) baseStart_243325 baseEnd_243325 := by
    simpa [prefixWord, tailWord_243325, baseEnd_243325] using wordTrace_append hprefix tailTrace_243325
  have hstable : (prefixWord ++ tailWord_243325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243325).length < 2 ^ (prefixWord ++ tailWord_243325).sum := by decide
  have hdescent : baseEnd_243325 < baseStart_243325 := by decide
  rcases family_descends (prefixWord ++ tailWord_243325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243338 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_243338 : Nat := 118140960795 + 243338 * 2 ^ 59
def prefixEnd_243338 : Nat := 4983230072969 + 3 ^ 40 * 243338 * 2
def baseEnd_243338 : Nat := 124949355503874172655915

theorem tailTrace_243338 : CollatzResearch.WordTrace tailWord_243338 prefixEnd_243338 124949355503874172655915 := by
  unfold tailWord_243338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218816498108864916710667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5916843994956973111228445 2218816498108864916710667)
  ·
    refine ⟨3328224747163297375066001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2218816498108864916710667 3328224747163297375066001)
    ·
      refine ⟨2496168560372473031299501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3328224747163297375066001 2496168560372473031299501)
      ·
        refine ⟨936063210139677386737313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2496168560372473031299501 936063210139677386737313)
        ·
          refine ⟨702047407604758040052985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936063210139677386737313 702047407604758040052985)
          ·
            refine ⟨526535555703568530039739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702047407604758040052985 526535555703568530039739)
            ·
              refine ⟨789803333555352795059609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526535555703568530039739 789803333555352795059609)
              ·
                refine ⟨592352500166514596294707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789803333555352795059609 592352500166514596294707)
                ·
                  refine ⟨888528750249771894442061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592352500166514596294707 888528750249771894442061)
                  ·
                    refine ⟨333198281343664460415773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888528750249771894442061 333198281343664460415773)
                    ·
                      refine ⟨124949355503874172655915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333198281343664460415773 124949355503874172655915)
                      ·
                        rfl

theorem cell23_243338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_243338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243338 prefixEnd_243338 := by exact prefixLift 243338
  have htrace : WordTrace (prefixWord ++ tailWord_243338) baseStart_243338 baseEnd_243338 := by
    simpa [prefixWord, tailWord_243338, baseEnd_243338] using wordTrace_append hprefix tailTrace_243338
  have hstable : (prefixWord ++ tailWord_243338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243338).length < 2 ^ (prefixWord ++ tailWord_243338).sum := by decide
  have hdescent : baseEnd_243338 < baseStart_243338 := by decide
  rcases family_descends (prefixWord ++ tailWord_243338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243344 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_243344 : Nat := 118140960795 + 243344 * 2 ^ 59
def prefixEnd_243344 : Nat := 4983230072969 + 3 ^ 40 * 243344 * 2
def baseEnd_243344 : Nat := 124952436387801149180887

theorem tailTrace_243344 : CollatzResearch.WordTrace tailWord_243344 prefixEnd_243344 124952436387801149180887 := by
  unfold tailWord_243344
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437742415206861345780543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5916989886942481794374057 4437742415206861345780543)
  ·
    refine ⟨6656613622810292018670815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437742415206861345780543 6656613622810292018670815)
    ·
      refine ⟨9984920434215438028006223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656613622810292018670815 9984920434215438028006223)
      ·
        refine ⟨14977380651323157042009335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984920434215438028006223 14977380651323157042009335)
        ·
          refine ⟨22466070976984735563014003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14977380651323157042009335 22466070976984735563014003)
          ·
            refine ⟨33699106465477103344521005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22466070976984735563014003 33699106465477103344521005)
            ·
              refine ⟨12637164924553913754195377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33699106465477103344521005 12637164924553913754195377)
              ·
                refine ⟨9477873693415435315646533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12637164924553913754195377 9477873693415435315646533)
                ·
                  refine ⟨1777101317515394121683725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9477873693415435315646533 1777101317515394121683725)
                  ·
                    refine ⟨666412994068272795631397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777101317515394121683725 666412994068272795631397)
                    ·
                      refine ⟨124952436387801149180887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 666412994068272795631397 124952436387801149180887)
                      ·
                        rfl

theorem cell23_243344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_243344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243344 prefixEnd_243344 := by exact prefixLift 243344
  have htrace : WordTrace (prefixWord ++ tailWord_243344) baseStart_243344 baseEnd_243344 := by
    simpa [prefixWord, tailWord_243344, baseEnd_243344] using wordTrace_append hprefix tailTrace_243344
  have hstable : (prefixWord ++ tailWord_243344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243344).length < 2 ^ (prefixWord ++ tailWord_243344).sum := by decide
  have hdescent : baseEnd_243344 < baseStart_243344 := by decide
  rcases family_descends (prefixWord ++ tailWord_243344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243356 : List Nat := [2, 2, 3, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_243356 : Nat := 118140960795 + 243356 * 2 ^ 59
def prefixEnd_243356 : Nat := 4983230072969 + 3 ^ 40 * 243356 * 2
def baseEnd_243356 : Nat := 124958598155655102230833

theorem tailTrace_243356 : CollatzResearch.WordTrace tailWord_243356 prefixEnd_243356 124958598155655102230833 := by
  unfold tailWord_243356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437961253185124370498961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5917281670913499160665281 4437961253185124370498961)
  ·
    refine ⟨3328470939888843277874221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4437961253185124370498961 3328470939888843277874221)
    ·
      refine ⟨1248176602458316229202833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3328470939888843277874221 1248176602458316229202833)
      ·
        refine ⟨936132451843737171902125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1248176602458316229202833 936132451843737171902125)
        ·
          refine ⟨351049669441401439463297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 936132451843737171902125 351049669441401439463297)
          ·
            refine ⟨263287252081051079597473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351049669441401439463297 263287252081051079597473)
            ·
              refine ⟨197465439060788309698105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263287252081051079597473 197465439060788309698105)
              ·
                refine ⟨148099079295591232273579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197465439060788309698105 148099079295591232273579)
                ·
                  refine ⟨222148618943386848410369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148099079295591232273579 222148618943386848410369)
                  ·
                    refine ⟨166611464207540136307777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222148618943386848410369 166611464207540136307777)
                    ·
                      refine ⟨124958598155655102230833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166611464207540136307777 124958598155655102230833)
                      ·
                        rfl

theorem cell23_243356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_243356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243356 prefixEnd_243356 := by exact prefixLift 243356
  have htrace : WordTrace (prefixWord ++ tailWord_243356) baseStart_243356 baseEnd_243356 := by
    simpa [prefixWord, tailWord_243356, baseEnd_243356] using wordTrace_append hprefix tailTrace_243356
  have hstable : (prefixWord ++ tailWord_243356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243356).length < 2 ^ (prefixWord ++ tailWord_243356).sum := by decide
  have hdescent : baseEnd_243356 < baseStart_243356 := by decide
  rcases family_descends (prefixWord ++ tailWord_243356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243361 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_243361 : Nat := 118140960795 + 243361 * 2 ^ 59
def prefixEnd_243361 : Nat := 4983230072969 + 3 ^ 40 * 243361 * 2
def baseEnd_243361 : Nat := 124961165558927582668309

theorem tailTrace_243361 : CollatzResearch.WordTrace tailWord_243361 prefixEnd_243361 124961165558927582668309 := by
  unfold tailWord_243361
  simp only [CollatzResearch.WordTrace]
  refine ⟨8876104871352134594929937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5917403247568089729953291 8876104871352134594929937)
  ·
    refine ⟨6657078653514100946197453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8876104871352134594929937 6657078653514100946197453)
    ·
      refine ⟨2496404495067787854824045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6657078653514100946197453 2496404495067787854824045)
      ·
        refine ⟨936151685650420445559017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2496404495067787854824045 936151685650420445559017)
        ·
          refine ⟨702113764237815334169263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936151685650420445559017 702113764237815334169263)
          ·
            refine ⟨1053170646356723001253895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702113764237815334169263 1053170646356723001253895)
            ·
              refine ⟨1579755969535084501880843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053170646356723001253895 1579755969535084501880843)
              ·
                refine ⟨2369633954302626752821265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579755969535084501880843 2369633954302626752821265)
                ·
                  refine ⟨1777225465726970064615949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369633954302626752821265 1777225465726970064615949)
                  ·
                    refine ⟨666459549647613774230981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777225465726970064615949 666459549647613774230981)
                    ·
                      refine ⟨124961165558927582668309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 666459549647613774230981 124961165558927582668309)
                      ·
                        rfl

theorem cell23_243361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_243361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243361 prefixEnd_243361 := by exact prefixLift 243361
  have htrace : WordTrace (prefixWord ++ tailWord_243361) baseStart_243361 baseEnd_243361 := by
    simpa [prefixWord, tailWord_243361, baseEnd_243361] using wordTrace_append hprefix tailTrace_243361
  have hstable : (prefixWord ++ tailWord_243361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243361).length < 2 ^ (prefixWord ++ tailWord_243361).sum := by decide
  have hdescent : baseEnd_243361 < baseStart_243361 := by decide
  rcases family_descends (prefixWord ++ tailWord_243361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243378 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_243378 : Nat := 118140960795 + 243378 * 2 ^ 59
def prefixEnd_243378 : Nat := 4983230072969 + 3 ^ 40 * 243378 * 2
def baseEnd_243378 : Nat := 124969894730054016155731

theorem tailTrace_243378 : CollatzResearch.WordTrace tailWord_243378 prefixEnd_243378 124969894730054016155731 := by
  unfold tailWord_243378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219181228072636624574697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5917816608193697665532525 2219181228072636624574697)
  ·
    refine ⟨1664385921054477468431023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2219181228072636624574697 1664385921054477468431023)
    ·
      refine ⟨2496578881581716202646535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664385921054477468431023 2496578881581716202646535)
      ·
        refine ⟨3744868322372574303969803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496578881581716202646535 3744868322372574303969803)
        ·
          refine ⟨5617302483558861455954705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744868322372574303969803 5617302483558861455954705)
          ·
            refine ⟨4212976862669146091966029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5617302483558861455954705 4212976862669146091966029)
            ·
              refine ⟨1579866323500929784487261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4212976862669146091966029 1579866323500929784487261)
              ·
                refine ⟨592449871312848669182723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1579866323500929784487261 592449871312848669182723)
                ·
                  refine ⟨888674806969273003774085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592449871312848669182723 888674806969273003774085)
                  ·
                    refine ⟨166626526306738688207641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888674806969273003774085 166626526306738688207641)
                    ·
                      refine ⟨124969894730054016155731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166626526306738688207641 124969894730054016155731)
                      ·
                        rfl

theorem cell23_243378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_243378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243378 prefixEnd_243378 := by exact prefixLift 243378
  have htrace : WordTrace (prefixWord ++ tailWord_243378) baseStart_243378 baseEnd_243378 := by
    simpa [prefixWord, tailWord_243378, baseEnd_243378] using wordTrace_append hprefix tailTrace_243378
  have hstable : (prefixWord ++ tailWord_243378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243378).length < 2 ^ (prefixWord ++ tailWord_243378).sum := by decide
  have hdescent : baseEnd_243378 < baseStart_243378 := by decide
  rcases family_descends (prefixWord ++ tailWord_243378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243382 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_243382 : Nat := 118140960795 + 243382 * 2 ^ 59
def prefixEnd_243382 : Nat := 4983230072969 + 3 ^ 40 * 243382 * 2
def baseEnd_243382 : Nat := 124971948652672000505713

theorem tailTrace_243382 : CollatzResearch.WordTrace tailWord_243382 prefixEnd_243382 124971948652672000505713 := by
  unfold tailWord_243382
  simp only [CollatzResearch.WordTrace]
  refine ⟨554804425267253448840275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5917913869517370120962933 554804425267253448840275)
  ·
    refine ⟨832206637900880173260413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 554804425267253448840275 832206637900880173260413)
    ·
      refine ⟨312077489212830064972655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 832206637900880173260413 312077489212830064972655)
      ·
        refine ⟨468116233819245097458983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312077489212830064972655 468116233819245097458983)
        ·
          refine ⟨702174350728867646188475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468116233819245097458983 702174350728867646188475)
          ·
            refine ⟨1053261526093301469282713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702174350728867646188475 1053261526093301469282713)
            ·
              refine ⟨789946144569976101962035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053261526093301469282713 789946144569976101962035)
              ·
                refine ⟨1184919216854964152943053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789946144569976101962035 1184919216854964152943053)
                ·
                  refine ⟨444344706320611557353645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184919216854964152943053 444344706320611557353645)
                  ·
                    refine ⟨166629264870229334007617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444344706320611557353645 166629264870229334007617)
                    ·
                      refine ⟨124971948652672000505713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166629264870229334007617 124971948652672000505713)
                      ·
                        rfl

theorem cell23_243382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_243382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243382 prefixEnd_243382 := by exact prefixLift 243382
  have htrace : WordTrace (prefixWord ++ tailWord_243382) baseStart_243382 baseEnd_243382 := by
    simpa [prefixWord, tailWord_243382, baseEnd_243382] using wordTrace_append hprefix tailTrace_243382
  have hstable : (prefixWord ++ tailWord_243382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243382).length < 2 ^ (prefixWord ++ tailWord_243382).sum := by decide
  have hdescent : baseEnd_243382 < baseStart_243382 := by decide
  rcases family_descends (prefixWord ++ tailWord_243382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243412 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_243412 : Nat := 118140960795 + 243412 * 2 ^ 59
def prefixEnd_243412 : Nat := 4983230072969 + 3 ^ 40 * 243412 * 2
def baseEnd_243412 : Nat := 124987353072306883130575

theorem tailTrace_243412 : CollatzResearch.WordTrace tailWord_243412 prefixEnd_243412 124987353072306883130575 := by
  unfold tailWord_243412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4438982497083685152518245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5918643329444913536690993 4438982497083685152518245)
  ·
    refine ⟨832309218203190966097171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4438982497083685152518245 832309218203190966097171)
    ·
      refine ⟨1248463827304786449145757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832309218203190966097171 1248463827304786449145757)
      ·
        refine ⟨468173935239294918429659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1248463827304786449145757 468173935239294918429659)
        ·
          refine ⟨702260902858942377644489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468173935239294918429659 702260902858942377644489)
          ·
            refine ⟨526695677144206783233367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702260902858942377644489 526695677144206783233367)
            ·
              refine ⟨790043515716310174850051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526695677144206783233367 790043515716310174850051)
              ·
                refine ⟨1185065273574465262275077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790043515716310174850051 1185065273574465262275077)
                ·
                  refine ⟨222199738795212236676577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185065273574465262275077 222199738795212236676577)
                  ·
                    refine ⟨166649804096409177507433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222199738795212236676577 166649804096409177507433)
                    ·
                      refine ⟨124987353072306883130575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166649804096409177507433 124987353072306883130575)
                      ·
                        rfl

theorem cell23_243412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_243412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243412 prefixEnd_243412 := by exact prefixLift 243412
  have htrace : WordTrace (prefixWord ++ tailWord_243412) baseStart_243412 baseEnd_243412 := by
    simpa [prefixWord, tailWord_243412, baseEnd_243412] using wordTrace_append hprefix tailTrace_243412
  have hstable : (prefixWord ++ tailWord_243412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243412).length < 2 ^ (prefixWord ++ tailWord_243412).sum := by decide
  have hdescent : baseEnd_243412 < baseStart_243412 := by decide
  rcases family_descends (prefixWord ++ tailWord_243412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243418 : List Nat := [3, 1, 1, 2, 2, 3, 2, 4, 5]
def baseStart_243418 : Nat := 118140960795 + 243418 * 2 ^ 59
def prefixEnd_243418 : Nat := 4983230072969 + 3 ^ 40 * 243418 * 2
def baseEnd_243418 : Nat := 13887825995137095517283

theorem tailTrace_243418 : CollatzResearch.WordTrace tailWord_243418 prefixEnd_243418 13887825995137095517283 := by
  unfold tailWord_243418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219545958036408332438727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5918789221430422219836605 2219545958036408332438727)
  ·
    refine ⟨3329318937054612498658091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2219545958036408332438727 3329318937054612498658091)
    ·
      refine ⟨4993978405581918747987137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3329318937054612498658091 4993978405581918747987137)
      ·
        refine ⟨3745483804186439060990353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4993978405581918747987137 3745483804186439060990353)
        ·
          refine ⟨2809112853139829295742765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3745483804186439060990353 2809112853139829295742765)
          ·
            refine ⟨1053417319927435985903537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2809112853139829295742765 1053417319927435985903537)
            ·
              refine ⟨790062989945576989427653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053417319927435985903537 790062989945576989427653)
              ·
                refine ⟨148136810614795685517685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790062989945576989427653 148136810614795685517685)
                ·
                  refine ⟨13887825995137095517283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148136810614795685517685 13887825995137095517283)
                  ·
                    rfl

theorem cell23_243418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_243418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243418 prefixEnd_243418 := by exact prefixLift 243418
  have htrace : WordTrace (prefixWord ++ tailWord_243418) baseStart_243418 baseEnd_243418 := by
    simpa [prefixWord, tailWord_243418, baseEnd_243418] using wordTrace_append hprefix tailTrace_243418
  have hstable : (prefixWord ++ tailWord_243418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243418).length < 2 ^ (prefixWord ++ tailWord_243418).sum := by decide
  have hdescent : baseEnd_243418 < baseStart_243418 := by decide
  rcases family_descends (prefixWord ++ tailWord_243418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243458 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_243458 : Nat := 118140960795 + 243458 * 2 ^ 59
def prefixEnd_243458 : Nat := 4983230072969 + 3 ^ 40 * 243458 * 2
def baseEnd_243458 : Nat := 125010973182413703155363

theorem tailTrace_243458 : CollatzResearch.WordTrace tailWord_243458 prefixEnd_243458 125010973182413703155363 := by
  unfold tailWord_243458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219910688000180040302757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5919761834667146774140685 2219910688000180040302757)
  ·
    refine ⟨416233254000033757556767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2219910688000180040302757 416233254000033757556767)
    ·
      refine ⟨624349881000050636335151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416233254000033757556767 624349881000050636335151)
      ·
        refine ⟨936524821500075954502727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624349881000050636335151 936524821500075954502727)
        ·
          refine ⟨1404787232250113931754091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936524821500075954502727 1404787232250113931754091)
          ·
            refine ⟨2107180848375170897631137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404787232250113931754091 2107180848375170897631137)
            ·
              refine ⟨1580385636281378173223353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107180848375170897631137 1580385636281378173223353)
              ·
                refine ⟨1185289227211033629917515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580385636281378173223353 1185289227211033629917515)
                ·
                  refine ⟨1777933840816550444876273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185289227211033629917515 1777933840816550444876273)
                  ·
                    refine ⟨1333450380612412833657205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1777933840816550444876273 1333450380612412833657205)
                    ·
                      refine ⟨125010973182413703155363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1333450380612412833657205 125010973182413703155363)
                      ·
                        rfl

theorem cell23_243458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_243458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243458 prefixEnd_243458 := by exact prefixLift 243458
  have htrace : WordTrace (prefixWord ++ tailWord_243458) baseStart_243458 baseEnd_243458 := by
    simpa [prefixWord, tailWord_243458, baseEnd_243458] using wordTrace_append hprefix tailTrace_243458
  have hstable : (prefixWord ++ tailWord_243458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243458).length < 2 ^ (prefixWord ++ tailWord_243458).sum := by decide
  have hdescent : baseEnd_243458 < baseStart_243458 := by decide
  rcases family_descends (prefixWord ++ tailWord_243458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243468 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 4, 4, 2]
def baseStart_243468 : Nat := 118140960795 + 243468 * 2 ^ 59
def prefixEnd_243468 : Nat := 4983230072969 + 3 ^ 40 * 243468 * 2
def baseEnd_243468 : Nat := 125016107988958664030317

theorem tailTrace_243468 : CollatzResearch.WordTrace tailWord_243468 prefixEnd_243468 125016107988958664030317 := by
  unfold tailWord_243468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440003740982245934537529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5920004987976327912716705 4440003740982245934537529)
  ·
    refine ⟨3330002805736684450903147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4440003740982245934537529 3330002805736684450903147)
    ·
      refine ⟨4995004208605026676354721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3330002805736684450903147 4995004208605026676354721)
      ·
        refine ⟨3746253156453770007266041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4995004208605026676354721 3746253156453770007266041)
        ·
          refine ⟨2809689867340327505449531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746253156453770007266041 2809689867340327505449531)
          ·
            refine ⟨4214534801010491258174297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809689867340327505449531 4214534801010491258174297)
            ·
              refine ⟨3160901100757868443630723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214534801010491258174297 3160901100757868443630723)
              ·
                refine ⟨4741351651136802665446085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160901100757868443630723 4741351651136802665446085)
                ·
                  refine ⟨889003434588150499771141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4741351651136802665446085 889003434588150499771141)
                  ·
                    refine ⟨166688143985278218707089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889003434588150499771141 166688143985278218707089)
                    ·
                      refine ⟨125016107988958664030317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166688143985278218707089 125016107988958664030317)
                      ·
                        rfl

theorem cell23_243468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_243468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243468 prefixEnd_243468 := by exact prefixLift 243468
  have htrace : WordTrace (prefixWord ++ tailWord_243468) baseStart_243468 baseEnd_243468 := by
    simpa [prefixWord, tailWord_243468, baseEnd_243468] using wordTrace_append hprefix tailTrace_243468
  have hstable : (prefixWord ++ tailWord_243468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243468).length < 2 ^ (prefixWord ++ tailWord_243468).sum := by decide
  have hdescent : baseEnd_243468 < baseStart_243468 := by decide
  rcases family_descends (prefixWord ++ tailWord_243468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243471 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 3]
def baseStart_243471 : Nat := 118140960795 + 243471 * 2 ^ 59
def prefixEnd_243471 : Nat := 4983230072969 + 3 ^ 40 * 243471 * 2
def baseEnd_243471 : Nat := 125017648430922152292803

theorem tailTrace_243471 : CollatzResearch.WordTrace tailWord_243471 prefixEnd_243471 125017648430922152292803 := by
  unfold tailWord_243471
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880116900953623381434267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5920077933969082254289511 8880116900953623381434267)
  ·
    refine ⟨13320175351430435072151401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8880116900953623381434267 13320175351430435072151401)
    ·
      refine ⟨9990131513572826304113551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13320175351430435072151401 9990131513572826304113551)
      ·
        refine ⟨14985197270359239456170327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990131513572826304113551 14985197270359239456170327)
        ·
          refine ⟨22477795905538859184255491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985197270359239456170327 22477795905538859184255491)
          ·
            refine ⟨33716693858308288776383237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22477795905538859184255491 33716693858308288776383237)
            ·
              refine ⟨6321880098432804145571857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33716693858308288776383237 6321880098432804145571857)
              ·
                refine ⟨4741410073824603109178893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321880098432804145571857 4741410073824603109178893)
                ·
                  refine ⟨1778028777684226165942085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4741410073824603109178893 1778028777684226165942085)
                  ·
                    refine ⟨333380395815792406114141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1778028777684226165942085 333380395815792406114141)
                    ·
                      refine ⟨125017648430922152292803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333380395815792406114141 125017648430922152292803)
                      ·
                        rfl

theorem cell23_243471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_243471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243471 prefixEnd_243471 := by exact prefixLift 243471
  have htrace : WordTrace (prefixWord ++ tailWord_243471) baseStart_243471 baseEnd_243471 := by
    simpa [prefixWord, tailWord_243471, baseEnd_243471] using wordTrace_append hprefix tailTrace_243471
  have hstable : (prefixWord ++ tailWord_243471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243471).length < 2 ^ (prefixWord ++ tailWord_243471).sum := by decide
  have hdescent : baseEnd_243471 < baseStart_243471 := by decide
  rcases family_descends (prefixWord ++ tailWord_243471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243488 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3]
def baseStart_243488 : Nat := 118140960795 + 243488 * 2 ^ 59
def prefixEnd_243488 : Nat := 4983230072969 + 3 ^ 40 * 243488 * 2
def baseEnd_243488 : Nat := 125026377602048585780225

theorem tailTrace_243488 : CollatzResearch.WordTrace tailWord_243488 prefixEnd_243488 125026377602048585780225 := by
  unfold tailWord_243488
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440368470946017642401559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5920491294594690189868745 4440368470946017642401559)
  ·
    refine ⟨6660552706419026463602339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4440368470946017642401559 6660552706419026463602339)
    ·
      refine ⟨9990829059628539695403509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660552706419026463602339 9990829059628539695403509)
      ·
        refine ⟨936640224340175596444079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9990829059628539695403509 936640224340175596444079)
        ·
          refine ⟨1404960336510263394666119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936640224340175596444079 1404960336510263394666119)
          ·
            refine ⟨2107440504765395091999179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404960336510263394666119 2107440504765395091999179)
            ·
              refine ⟨3161160757148092637998769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107440504765395091999179 3161160757148092637998769)
              ·
                refine ⟨2370870567861069478499077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161160757148092637998769 2370870567861069478499077)
                ·
                  refine ⟨444538231473950527218577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370870567861069478499077 444538231473950527218577)
                  ·
                    refine ⟨333403673605462895413933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 444538231473950527218577 333403673605462895413933)
                    ·
                      refine ⟨125026377602048585780225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333403673605462895413933 125026377602048585780225)
                      ·
                        rfl

theorem cell23_243488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_243488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243488 prefixEnd_243488 := by exact prefixLift 243488
  have htrace : WordTrace (prefixWord ++ tailWord_243488) baseStart_243488 baseEnd_243488 := by
    simpa [prefixWord, tailWord_243488, baseEnd_243488] using wordTrace_append hprefix tailTrace_243488
  have hstable : (prefixWord ++ tailWord_243488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243488).length < 2 ^ (prefixWord ++ tailWord_243488).sum := by decide
  have hdescent : baseEnd_243488 < baseStart_243488 := by decide
  rcases family_descends (prefixWord ++ tailWord_243488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243502 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_243502 : Nat := 118140960795 + 243502 * 2 ^ 59
def prefixEnd_243502 : Nat := 4983230072969 + 3 ^ 40 * 243502 * 2
def baseEnd_243502 : Nat := 125033566331211531005161

theorem tailTrace_243502 : CollatzResearch.WordTrace tailWord_243502 prefixEnd_243502 125033566331211531005161 := by
  unfold tailWord_243502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110155945480164459476595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5920831709227543783875173 1110155945480164459476595)
  ·
    refine ⟨1665233918220246689214893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110155945480164459476595 1665233918220246689214893)
    ·
      refine ⟨624462719332592508455585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1665233918220246689214893 624462719332592508455585)
      ·
        refine ⟨468347039499444381341689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624462719332592508455585 468347039499444381341689)
        ·
          refine ⟨351260279624583286006267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468347039499444381341689 351260279624583286006267)
          ·
            refine ⟨526890419436874929009401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351260279624583286006267 526890419436874929009401)
            ·
              refine ⟨395167814577656196757051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526890419436874929009401 395167814577656196757051)
              ·
                refine ⟨592751721866484295135577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395167814577656196757051 592751721866484295135577)
                ·
                  refine ⟨444563791399863221351683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592751721866484295135577 444563791399863221351683)
                  ·
                    refine ⟨666845687099794832027525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 444563791399863221351683 666845687099794832027525)
                    ·
                      refine ⟨125033566331211531005161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 666845687099794832027525 125033566331211531005161)
                      ·
                        rfl

theorem cell23_243502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_243502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243502 prefixEnd_243502 := by exact prefixLift 243502
  have htrace : WordTrace (prefixWord ++ tailWord_243502) baseStart_243502 baseEnd_243502 := by
    simpa [prefixWord, tailWord_243502, baseEnd_243502] using wordTrace_append hprefix tailTrace_243502
  have hstable : (prefixWord ++ tailWord_243502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243502).length < 2 ^ (prefixWord ++ tailWord_243502).sum := by decide
  have hdescent : baseEnd_243502 < baseStart_243502 := by decide
  rcases family_descends (prefixWord ++ tailWord_243502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243505 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_243505 : Nat := 118140960795 + 243505 * 2 ^ 59
def prefixEnd_243505 : Nat := 4983230072969 + 3 ^ 40 * 243505 * 2
def baseEnd_243505 : Nat := 125035106773175019267647

theorem tailTrace_243505 : CollatzResearch.WordTrace tailWord_243505 prefixEnd_243505 125035106773175019267647 := by
  unfold tailWord_243505
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881356982830447188171969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5920904655220298125447979 8881356982830447188171969)
  ·
    refine ⟨6661017737122835391128977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8881356982830447188171969 6661017737122835391128977)
    ·
      refine ⟨4995763302842126543346733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6661017737122835391128977 4995763302842126543346733)
      ·
        refine ⟨1873411238565797453755025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4995763302842126543346733 1873411238565797453755025)
        ·
          refine ⟨1405058428924348090316269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873411238565797453755025 1405058428924348090316269)
          ·
            refine ⟨526896910846630533868601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1405058428924348090316269 526896910846630533868601)
            ·
              refine ⟨395172683134972900401451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526896910846630533868601 395172683134972900401451)
              ·
                refine ⟨592759024702459350602177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395172683134972900401451 592759024702459350602177)
                ·
                  refine ⟨444569268526844512951633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592759024702459350602177 444569268526844512951633)
                  ·
                    refine ⟨333426951395133384713725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 444569268526844512951633 333426951395133384713725)
                    ·
                      refine ⟨125035106773175019267647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333426951395133384713725 125035106773175019267647)
                      ·
                        rfl

theorem cell23_243505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_243505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243505 prefixEnd_243505 := by exact prefixLift 243505
  have htrace : WordTrace (prefixWord ++ tailWord_243505) baseStart_243505 baseEnd_243505 := by
    simpa [prefixWord, tailWord_243505, baseEnd_243505] using wordTrace_append hprefix tailTrace_243505
  have hstable : (prefixWord ++ tailWord_243505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243505).length < 2 ^ (prefixWord ++ tailWord_243505).sum := by decide
  have hdescent : baseEnd_243505 < baseStart_243505 := by decide
  rcases family_descends (prefixWord ++ tailWord_243505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243538 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_243538 : Nat := 118140960795 + 243538 * 2 ^ 59
def prefixEnd_243538 : Nat := 4983230072969 + 3 ^ 40 * 243538 * 2
def baseEnd_243538 : Nat := 41684017211591130051665

theorem tailTrace_243538 : CollatzResearch.WordTrace tailWord_243538 prefixEnd_243538 41684017211591130051665 := by
  unfold tailWord_243538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220640147927723456030817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5921707061140595882748845 2220640147927723456030817)
  ·
    refine ⟨1665480110945792592023113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2220640147927723456030817 1665480110945792592023113)
    ·
      refine ⟨1249110083209344444017335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1665480110945792592023113 1249110083209344444017335)
      ·
        refine ⟨1873665124814016666026003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249110083209344444017335 1873665124814016666026003)
        ·
          refine ⟨2810497687221024999039005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873665124814016666026003 2810497687221024999039005)
          ·
            refine ⟨1053936632707884374639627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2810497687221024999039005 1053936632707884374639627)
            ·
              refine ⟨1580904949061826561959441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053936632707884374639627 1580904949061826561959441)
              ·
                refine ⟨1185678711796369921469581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580904949061826561959441 1185678711796369921469581)
                ·
                  refine ⟨444629516923638720551093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185678711796369921469581 444629516923638720551093)
                  ·
                    refine ⟨41684017211591130051665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 444629516923638720551093 41684017211591130051665)
                    ·
                      rfl

theorem cell23_243538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_243538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243538 prefixEnd_243538 := by exact prefixLift 243538
  have htrace : WordTrace (prefixWord ++ tailWord_243538) baseStart_243538 baseEnd_243538 := by
    simpa [prefixWord, tailWord_243538, baseEnd_243538] using wordTrace_append hprefix tailTrace_243538
  have hstable : (prefixWord ++ tailWord_243538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243538).length < 2 ^ (prefixWord ++ tailWord_243538).sum := by decide
  have hdescent : baseEnd_243538 < baseStart_243538 := by decide
  rcases family_descends (prefixWord ++ tailWord_243538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243568 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 4, 4]
def baseStart_243568 : Nat := 118140960795 + 243568 * 2 ^ 59
def prefixEnd_243568 : Nat := 4983230072969 + 3 ^ 40 * 243568 * 2
def baseEnd_243568 : Nat := 41689152018136090926619

theorem tailTrace_243568 : CollatzResearch.WordTrace tailWord_243568 prefixEnd_243568 41689152018136090926619 := by
  unfold tailWord_243568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441827390801104473857679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5922436521068139298476905 4441827390801104473857679)
  ·
    refine ⟨6662741086201656710786519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4441827390801104473857679 6662741086201656710786519)
    ·
      refine ⟨9994111629302485066179779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6662741086201656710786519 9994111629302485066179779)
      ·
        refine ⟨14991167443953727599269669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9994111629302485066179779 14991167443953727599269669)
        ·
          refine ⟨2810843895741323924863063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14991167443953727599269669 2810843895741323924863063)
          ·
            refine ⟨4216265843611985887294595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810843895741323924863063 4216265843611985887294595)
            ·
              refine ⟨6324398765417978830941893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216265843611985887294595 6324398765417978830941893)
              ·
                refine ⟨1185824768515871030801605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6324398765417978830941893 1185824768515871030801605)
                ·
                  refine ⟨222342144096725818275301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185824768515871030801605 222342144096725818275301)
                  ·
                    refine ⟨41689152018136090926619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222342144096725818275301 41689152018136090926619)
                    ·
                      rfl

theorem cell23_243568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_243568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243568 prefixEnd_243568 := by exact prefixLift 243568
  have htrace : WordTrace (prefixWord ++ tailWord_243568) baseStart_243568 baseEnd_243568 := by
    simpa [prefixWord, tailWord_243568, baseEnd_243568] using wordTrace_append hprefix tailTrace_243568
  have hstable : (prefixWord ++ tailWord_243568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243568).length < 2 ^ (prefixWord ++ tailWord_243568).sum := by decide
  have hdescent : baseEnd_243568 < baseStart_243568 := by decide
  rcases family_descends (prefixWord ++ tailWord_243568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243571 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6]
def baseStart_243571 : Nat := 118140960795 + 243571 * 2 ^ 59
def prefixEnd_243571 : Nat := 4983230072969 + 3 ^ 40 * 243571 * 2
def baseEnd_243571 : Nat := 125068996496371761042343

theorem tailTrace_243571 : CollatzResearch.WordTrace tailWord_243571 prefixEnd_243571 125068996496371761042343 := by
  unfold tailWord_243571
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883764200591340460074567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5922509467060893640049711 8883764200591340460074567)
  ·
    refine ⟨13325646300887010690111851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8883764200591340460074567 13325646300887010690111851)
    ·
      refine ⟨19988469451330516035167777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13325646300887010690111851 19988469451330516035167777)
      ·
        refine ⟨14991352088497887026375833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19988469451330516035167777 14991352088497887026375833)
        ·
          refine ⟨11243514066373415269781875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14991352088497887026375833 11243514066373415269781875)
          ·
            refine ⟨16865271099560122904672813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243514066373415269781875 16865271099560122904672813)
            ·
              refine ⟨6324476662335046089252305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16865271099560122904672813 6324476662335046089252305)
              ·
                refine ⟨4743357496751284566939229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6324476662335046089252305 4743357496751284566939229)
                ·
                  refine ⟨1778759061281731712602211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4743357496751284566939229 1778759061281731712602211)
                  ·
                    refine ⟨2668138591922597568903317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1778759061281731712602211 2668138591922597568903317)
                    ·
                      refine ⟨125068996496371761042343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2668138591922597568903317 125068996496371761042343)
                      ·
                        rfl

theorem cell23_243571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_243571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243571 prefixEnd_243571 := by exact prefixLift 243571
  have htrace : WordTrace (prefixWord ++ tailWord_243571) baseStart_243571 baseEnd_243571 := by
    simpa [prefixWord, tailWord_243571, baseEnd_243571] using wordTrace_append hprefix tailTrace_243571
  have hstable : (prefixWord ++ tailWord_243571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243571).length < 2 ^ (prefixWord ++ tailWord_243571).sum := by decide
  have hdescent : baseEnd_243571 < baseStart_243571 := by decide
  rcases family_descends (prefixWord ++ tailWord_243571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243588 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_243588 : Nat := 118140960795 + 243588 * 2 ^ 59
def prefixEnd_243588 : Nat := 4983230072969 + 3 ^ 40 * 243588 * 2
def baseEnd_243588 : Nat := 125077725667498194529765

theorem tailTrace_243588 : CollatzResearch.WordTrace tailWord_243588 prefixEnd_243588 125077725667498194529765 := by
  unfold tailWord_243588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442192120764876181721709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5922922827686501575628945 4442192120764876181721709)
  ·
    refine ⟨1665822045286828568145641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4442192120764876181721709 1665822045286828568145641)
    ·
      refine ⟨1249366533965121426109231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1665822045286828568145641 1249366533965121426109231)
      ·
        refine ⟨1874049800947682139163847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249366533965121426109231 1874049800947682139163847)
        ·
          refine ⟨2811074701421523208745771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874049800947682139163847 2811074701421523208745771)
          ·
            refine ⟨4216612052132284813118657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811074701421523208745771 4216612052132284813118657)
            ·
              refine ⟨3162459039099213609838993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216612052132284813118657 3162459039099213609838993)
              ·
                refine ⟨2371844279324410207379245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162459039099213609838993 2371844279324410207379245)
                ·
                  refine ⟨889441604746653827767217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2371844279324410207379245 889441604746653827767217)
                  ·
                    refine ⟨667081203559990370825413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 889441604746653827767217 667081203559990370825413)
                    ·
                      refine ⟨125077725667498194529765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 667081203559990370825413 125077725667498194529765)
                      ·
                        rfl

theorem cell23_243588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_243588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243588 prefixEnd_243588 := by exact prefixLift 243588
  have htrace : WordTrace (prefixWord ++ tailWord_243588) baseStart_243588 baseEnd_243588 := by
    simpa [prefixWord, tailWord_243588, baseEnd_243588] using wordTrace_append hprefix tailTrace_243588
  have hstable : (prefixWord ++ tailWord_243588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243588).length < 2 ^ (prefixWord ++ tailWord_243588).sum := by decide
  have hdescent : baseEnd_243588 < baseStart_243588 := by decide
  rcases family_descends (prefixWord ++ tailWord_243588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243602 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_243602 : Nat := 118140960795 + 243602 * 2 ^ 59
def prefixEnd_243602 : Nat := 4983230072969 + 3 ^ 40 * 243602 * 2
def baseEnd_243602 : Nat := 41694971465553713251567

theorem tailTrace_243602 : CollatzResearch.WordTrace tailWord_243602 prefixEnd_243602 41694971465553713251567 := by
  unfold tailWord_243602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221223715869758188613265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5923263242319355169635373 2221223715869758188613265)
  ·
    refine ⟨1665917786902318641459949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2221223715869758188613265 1665917786902318641459949)
    ·
      refine ⟨624719170088369490547481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1665917786902318641459949 624719170088369490547481)
      ·
        refine ⟨468539377566277117910611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624719170088369490547481 468539377566277117910611)
        ·
          refine ⟨702809066349415676865917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468539377566277117910611 702809066349415676865917)
          ·
            refine ⟨263553399881030878824719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 702809066349415676865917 263553399881030878824719)
            ·
              refine ⟨395330099821546318237079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263553399881030878824719 395330099821546318237079)
              ·
                refine ⟨592995149732319477355619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395330099821546318237079 592995149732319477355619)
                ·
                  refine ⟨889492724598479216033429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592995149732319477355619 889492724598479216033429)
                  ·
                    refine ⟨41694971465553713251567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 889492724598479216033429 41694971465553713251567)
                    ·
                      rfl

theorem cell23_243602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_243602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243602 prefixEnd_243602 := by exact prefixLift 243602
  have htrace : WordTrace (prefixWord ++ tailWord_243602) baseStart_243602 baseEnd_243602 := by
    simpa [prefixWord, tailWord_243602, baseEnd_243602] using wordTrace_append hprefix tailTrace_243602
  have hstable : (prefixWord ++ tailWord_243602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243602).length < 2 ^ (prefixWord ++ tailWord_243602).sum := by decide
  have hdescent : baseEnd_243602 < baseStart_243602 := by decide
  rcases family_descends (prefixWord ++ tailWord_243602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243606 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_243606 : Nat := 118140960795 + 243606 * 2 ^ 59
def prefixEnd_243606 : Nat := 4983230072969 + 3 ^ 40 * 243606 * 2
def baseEnd_243606 : Nat := 41695656106426374701561

theorem tailTrace_243606 : CollatzResearch.WordTrace tailWord_243606 prefixEnd_243606 41695656106426374701561 := by
  unfold tailWord_243606
  simp only [CollatzResearch.WordTrace]
  refine ⟨555315047216533839849917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5923360503643027625065781 555315047216533839849917)
  ·
    refine ⟨208243142706200189943719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 555315047216533839849917 208243142706200189943719)
    ·
      refine ⟨312364714059300284915579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208243142706200189943719 312364714059300284915579)
      ·
        refine ⟨468547071088950427373369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312364714059300284915579 468547071088950427373369)
        ·
          refine ⟨351410303316712820530027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468547071088950427373369 351410303316712820530027)
          ·
            refine ⟨527115454975069230795041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351410303316712820530027 527115454975069230795041)
            ·
              refine ⟨395336591231301923096281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527115454975069230795041 395336591231301923096281)
              ·
                refine ⟨296502443423476442322211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395336591231301923096281 296502443423476442322211)
                ·
                  refine ⟨444753665135214663483317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296502443423476442322211 444753665135214663483317)
                  ·
                    refine ⟨41695656106426374701561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 444753665135214663483317 41695656106426374701561)
                    ·
                      rfl

theorem cell23_243606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_243606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243606 prefixEnd_243606 := by exact prefixLift 243606
  have htrace : WordTrace (prefixWord ++ tailWord_243606) baseStart_243606 baseEnd_243606 := by
    simpa [prefixWord, tailWord_243606, baseEnd_243606] using wordTrace_append hprefix tailTrace_243606
  have hstable : (prefixWord ++ tailWord_243606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243606).length < 2 ^ (prefixWord ++ tailWord_243606).sum := by decide
  have hdescent : baseEnd_243606 < baseStart_243606 := by decide
  rcases family_descends (prefixWord ++ tailWord_243606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243612 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_243612 : Nat := 118140960795 + 243612 * 2 ^ 59
def prefixEnd_243612 : Nat := 4983230072969 + 3 ^ 40 * 243612 * 2
def baseEnd_243612 : Nat := 125090049203206100629655

theorem tailTrace_243612 : CollatzResearch.WordTrace tailWord_243612 prefixEnd_243612 125090049203206100629655 := by
  unfold tailWord_243612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442629796721402231158545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5923506395628536308211393 4442629796721402231158545)
  ·
    refine ⟨3331972347541051673368909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4442629796721402231158545 3331972347541051673368909)
    ·
      refine ⟨1249489630327894377513341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3331972347541051673368909 1249489630327894377513341)
      ·
        refine ⟨468558611372960391567503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1249489630327894377513341 468558611372960391567503)
        ·
          refine ⟨702837917059440587351255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468558611372960391567503 702837917059440587351255)
          ·
            refine ⟨1054256875589160881026883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702837917059440587351255 1054256875589160881026883)
            ·
              refine ⟨1581385313383741321540325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054256875589160881026883 1581385313383741321540325)
              ·
                refine ⟨296509746259451497788811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1581385313383741321540325 296509746259451497788811)
                ·
                  refine ⟨444764619389177246683217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296509746259451497788811 444764619389177246683217)
                  ·
                    refine ⟨333573464541882935012413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 444764619389177246683217 333573464541882935012413)
                    ·
                      refine ⟨125090049203206100629655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333573464541882935012413 125090049203206100629655)
                      ·
                        rfl

theorem cell23_243612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_243612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243612 prefixEnd_243612 := by exact prefixLift 243612
  have htrace : WordTrace (prefixWord ++ tailWord_243612) baseStart_243612 baseEnd_243612 := by
    simpa [prefixWord, tailWord_243612, baseEnd_243612] using wordTrace_append hprefix tailTrace_243612
  have hstable : (prefixWord ++ tailWord_243612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243612).length < 2 ^ (prefixWord ++ tailWord_243612).sum := by decide
  have hdescent : baseEnd_243612 < baseStart_243612 := by decide
  rcases family_descends (prefixWord ++ tailWord_243612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243648 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_243648 : Nat := 118140960795 + 243648 * 2 ^ 59
def prefixEnd_243648 : Nat := 4983230072969 + 3 ^ 40 * 243648 * 2
def baseEnd_243648 : Nat := 125108534506767959779489

theorem tailTrace_243648 : CollatzResearch.WordTrace tailWord_243648 prefixEnd_243648 125108534506767959779489 := by
  unfold tailWord_243648
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443286310656191305313799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5924381747541588407085065 4443286310656191305313799)
  ·
    refine ⟨6664929465984286957970699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4443286310656191305313799 6664929465984286957970699)
    ·
      refine ⟨9997394198976430436956049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664929465984286957970699 9997394198976430436956049)
      ·
        refine ⟨7498045649232322827717037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9997394198976430436956049 7498045649232322827717037)
        ·
          refine ⟨2811767118462121060393889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7498045649232322827717037 2811767118462121060393889)
          ·
            refine ⟨2108825338846590795295417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811767118462121060393889 2108825338846590795295417)
            ·
              refine ⟨1581619004134943096471563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108825338846590795295417 1581619004134943096471563)
              ·
                refine ⟨2372428506202414644707345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581619004134943096471563 2372428506202414644707345)
                ·
                  refine ⟨1779321379651810983530509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2372428506202414644707345 1779321379651810983530509)
                  ·
                    refine ⟨667245517369429118823941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779321379651810983530509 667245517369429118823941)
                    ·
                      refine ⟨125108534506767959779489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 667245517369429118823941 125108534506767959779489)
                      ·
                        rfl

theorem cell23_243648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_243648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243648 prefixEnd_243648 := by exact prefixLift 243648
  have htrace : WordTrace (prefixWord ++ tailWord_243648) baseStart_243648 baseEnd_243648 := by
    simpa [prefixWord, tailWord_243648, baseEnd_243648] using wordTrace_append hprefix tailTrace_243648
  have hstable : (prefixWord ++ tailWord_243648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243648).length < 2 ^ (prefixWord ++ tailWord_243648).sum := by decide
  have hdescent : baseEnd_243648 < baseStart_243648 := by decide
  rcases family_descends (prefixWord ++ tailWord_243648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243658 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_243658 : Nat := 118140960795 + 243658 * 2 ^ 59
def prefixEnd_243658 : Nat := 4983230072969 + 3 ^ 40 * 243658 * 2
def baseEnd_243658 : Nat := 41704556437770973551481

theorem tailTrace_243658 : CollatzResearch.WordTrace tailWord_243658 prefixEnd_243658 41704556437770973551481 := by
  unfold tailWord_243658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221734337819038579622907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5924624900850769545661085 2221734337819038579622907)
  ·
    refine ⟨3332601506728557869434361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2221734337819038579622907 3332601506728557869434361)
    ·
      refine ⟨2499451130046418402075771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3332601506728557869434361 2499451130046418402075771)
      ·
        refine ⟨3749176695069627603113657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499451130046418402075771 3749176695069627603113657)
        ·
          refine ⟨2811882521302220702335243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749176695069627603113657 2811882521302220702335243)
          ·
            refine ⟨4217823781953331053502865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811882521302220702335243 4217823781953331053502865)
            ·
              refine ⟨3163367836464998290127149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217823781953331053502865 3163367836464998290127149)
              ·
                refine ⟨1186262938674374358797681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3163367836464998290127149 1186262938674374358797681)
                ·
                  refine ⟨889697204005780769098261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1186262938674374358797681 889697204005780769098261)
                  ·
                    refine ⟨41704556437770973551481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 889697204005780769098261 41704556437770973551481)
                    ·
                      rfl

theorem cell23_243658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_243658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243658 prefixEnd_243658 := by exact prefixLift 243658
  have htrace : WordTrace (prefixWord ++ tailWord_243658) baseStart_243658 baseEnd_243658 := by
    simpa [prefixWord, tailWord_243658, baseEnd_243658] using wordTrace_append hprefix tailTrace_243658
  have hstable : (prefixWord ++ tailWord_243658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243658).length < 2 ^ (prefixWord ++ tailWord_243658).sum := by decide
  have hdescent : baseEnd_243658 < baseStart_243658 := by decide
  rcases family_descends (prefixWord ++ tailWord_243658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243669 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_243669 : Nat := 118140960795 + 243669 * 2 ^ 59
def prefixEnd_243669 : Nat := 4983230072969 + 3 ^ 40 * 243669 * 2
def baseEnd_243669 : Nat := 125119317600512377616893

theorem tailTrace_243669 : CollatzResearch.WordTrace tailWord_243669 prefixEnd_243669 125119317600512377616893 := by
  unfold tailWord_243669
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887338554236303197142061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5924892369490868798094707 8887338554236303197142061)
  ·
    refine ⟨3332751957838613698928273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8887338554236303197142061 3332751957838613698928273)
    ·
      refine ⟨2499563968378960274196205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3332751957838613698928273 2499563968378960274196205)
      ·
        refine ⟨937336488142110102823577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2499563968378960274196205 937336488142110102823577)
        ·
          refine ⟨703002366106582577117683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937336488142110102823577 703002366106582577117683)
          ·
            refine ⟨1054503549159873865676525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703002366106582577117683 1054503549159873865676525)
            ·
              refine ⟨395438830934952699628697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1054503549159873865676525 395438830934952699628697)
              ·
                refine ⟨296579123201214524721523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395438830934952699628697 296579123201214524721523)
                ·
                  refine ⟨444868684801821787082285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296579123201214524721523 444868684801821787082285)
                  ·
                    refine ⟨166825756800683170155857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444868684801821787082285 166825756800683170155857)
                    ·
                      refine ⟨125119317600512377616893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166825756800683170155857 125119317600512377616893)
                      ·
                        rfl

theorem cell23_243669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_243669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243669 prefixEnd_243669 := by exact prefixLift 243669
  have htrace : WordTrace (prefixWord ++ tailWord_243669) baseStart_243669 baseEnd_243669 := by
    simpa [prefixWord, tailWord_243669, baseEnd_243669] using wordTrace_append hprefix tailTrace_243669
  have hstable : (prefixWord ++ tailWord_243669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243669).length < 2 ^ (prefixWord ++ tailWord_243669).sum := by decide
  have hdescent : baseEnd_243669 < baseStart_243669 := by decide
  rcases family_descends (prefixWord ++ tailWord_243669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243676 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_243676 : Nat := 118140960795 + 243676 * 2 ^ 59
def prefixEnd_243676 : Nat := 4983230072969 + 3 ^ 40 * 243676 * 2
def baseEnd_243676 : Nat := 125122911965093850229361

theorem tailTrace_243676 : CollatzResearch.WordTrace tailWord_243676 prefixEnd_243676 125122911965093850229361 := by
  unfold tailWord_243676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443796932605471696323441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5925062576807295595097921 4443796932605471696323441)
  ·
    refine ⟨3332847699454103772242581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4443796932605471696323441 3332847699454103772242581)
    ·
      refine ⟨156227235911911114323871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3332847699454103772242581 156227235911911114323871)
      ·
        refine ⟨234340853867866671485807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156227235911911114323871 234340853867866671485807)
        ·
          refine ⟨351511280801800007228711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234340853867866671485807 351511280801800007228711)
          ·
            refine ⟨527266921202700010843067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351511280801800007228711 527266921202700010843067)
            ·
              refine ⟨790900381804050016264601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527266921202700010843067 790900381804050016264601)
              ·
                refine ⟨593175286353037512198451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790900381804050016264601 593175286353037512198451)
                ·
                  refine ⟨889762929529556268297677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593175286353037512198451 889762929529556268297677)
                  ·
                    refine ⟨333661098573583600611629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889762929529556268297677 333661098573583600611629)
                    ·
                      refine ⟨125122911965093850229361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333661098573583600611629 125122911965093850229361)
                      ·
                        rfl

theorem cell23_243676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_243676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243676 prefixEnd_243676 := by exact prefixLift 243676
  have htrace : WordTrace (prefixWord ++ tailWord_243676) baseStart_243676 baseEnd_243676 := by
    simpa [prefixWord, tailWord_243676, baseEnd_243676] using wordTrace_append hprefix tailTrace_243676
  have hstable : (prefixWord ++ tailWord_243676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243676).length < 2 ^ (prefixWord ++ tailWord_243676).sum := by decide
  have hdescent : baseEnd_243676 < baseStart_243676 := by decide
  rcases family_descends (prefixWord ++ tailWord_243676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243716 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_243716 : Nat := 118140960795 + 243716 * 2 ^ 59
def prefixEnd_243716 : Nat := 4983230072969 + 3 ^ 40 * 243716 * 2
def baseEnd_243716 : Nat := 125143451191273693729177

theorem tailTrace_243716 : CollatzResearch.WordTrace tailWord_243716 prefixEnd_243716 125143451191273693729177 := by
  unfold tailWord_243716
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444526392533015112051501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5926035190044020149402001 4444526392533015112051501)
  ·
    refine ⟨1666697397199880667019313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4444526392533015112051501 1666697397199880667019313)
    ·
      refine ⟨1250023047899910500264485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1666697397199880667019313 1250023047899910500264485)
      ·
        refine ⟨234379321481233218799591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1250023047899910500264485 234379321481233218799591)
        ·
          refine ⟨351568982221849828199387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234379321481233218799591 351568982221849828199387)
          ·
            refine ⟨527353473332774742299081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351568982221849828199387 527353473332774742299081)
            ·
              refine ⟨395515104999581056724311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527353473332774742299081 395515104999581056724311)
              ·
                refine ⟨593272657499371585086467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395515104999581056724311 593272657499371585086467)
                ·
                  refine ⟨889908986249057377629701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593272657499371585086467 889908986249057377629701)
                  ·
                    refine ⟨166857934921698258305569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889908986249057377629701 166857934921698258305569)
                    ·
                      refine ⟨125143451191273693729177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166857934921698258305569 125143451191273693729177)
                      ·
                        rfl

theorem cell23_243716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_243716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243716 prefixEnd_243716 := by exact prefixLift 243716
  have htrace : WordTrace (prefixWord ++ tailWord_243716) baseStart_243716 baseEnd_243716 := by
    simpa [prefixWord, tailWord_243716, baseEnd_243716] using wordTrace_append hprefix tailTrace_243716
  have hstable : (prefixWord ++ tailWord_243716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243716).length < 2 ^ (prefixWord ++ tailWord_243716).sum := by decide
  have hdescent : baseEnd_243716 < baseStart_243716 := by decide
  rcases family_descends (prefixWord ++ tailWord_243716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243772 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_243772 : Nat := 118140960795 + 243772 * 2 ^ 59
def prefixEnd_243772 : Nat := 4983230072969 + 3 ^ 40 * 243772 * 2
def baseEnd_243772 : Nat := 125172206107925474628919

theorem tailTrace_243772 : CollatzResearch.WordTrace tailWord_243772 prefixEnd_243772 125172206107925474628919 := by
  unfold tailWord_243772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445547636431575894070785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5927396848575434525427713 4445547636431575894070785)
  ·
    refine ⟨3334160727323681920553089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4445547636431575894070785 3334160727323681920553089)
    ·
      refine ⟨2500620545492761440414817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334160727323681920553089 2500620545492761440414817)
      ·
        refine ⟨1875465409119571080311113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2500620545492761440414817 1875465409119571080311113)
        ·
          refine ⟨1406599056839678310233335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875465409119571080311113 1406599056839678310233335)
          ·
            refine ⟨2109898585259517465350003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406599056839678310233335 2109898585259517465350003)
            ·
              refine ⟨3164847877889276198025005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109898585259517465350003 3164847877889276198025005)
              ·
                refine ⟨1186817954208478574259377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3164847877889276198025005 1186817954208478574259377)
                ·
                  refine ⟨890113465656358930694533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1186817954208478574259377 890113465656358930694533)
                  ·
                    refine ⟨166896274810567299505225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890113465656358930694533 166896274810567299505225)
                    ·
                      refine ⟨125172206107925474628919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166896274810567299505225 125172206107925474628919)
                      ·
                        rfl

theorem cell23_243772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_243772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243772 prefixEnd_243772 := by exact prefixLift 243772
  have htrace : WordTrace (prefixWord ++ tailWord_243772) baseStart_243772 baseEnd_243772 := by
    simpa [prefixWord, tailWord_243772, baseEnd_243772] using wordTrace_append hprefix tailTrace_243772
  have hstable : (prefixWord ++ tailWord_243772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243772).length < 2 ^ (prefixWord ++ tailWord_243772).sum := by decide
  have hdescent : baseEnd_243772 < baseStart_243772 := by decide
  rcases family_descends (prefixWord ++ tailWord_243772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243775 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 3]
def baseStart_243775 : Nat := 118140960795 + 243775 * 2 ^ 59
def prefixEnd_243775 : Nat := 4983230072969 + 3 ^ 40 * 243775 * 2
def baseEnd_243775 : Nat := 125173746549888962891405

theorem tailTrace_243775 : CollatzResearch.WordTrace tailWord_243775 prefixEnd_243775 125173746549888962891405 := by
  unfold tailWord_243775
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891204691852283300500779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5927469794568188867000519 8891204691852283300500779)
  ·
    refine ⟨13336807037778424950751169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8891204691852283300500779 13336807037778424950751169)
    ·
      refine ⟨10002605278333818713063377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13336807037778424950751169 10002605278333818713063377)
      ·
        refine ⟨7501953958750364034797533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10002605278333818713063377 7501953958750364034797533)
        ·
          refine ⟨2813232734531386513049075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7501953958750364034797533 2813232734531386513049075)
          ·
            refine ⟨4219849101797079769573613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813232734531386513049075 4219849101797079769573613)
            ·
              refine ⟨1582443413173904913590105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4219849101797079769573613 1582443413173904913590105)
              ·
                refine ⟨1186832559880428685192579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582443413173904913590105 1186832559880428685192579)
                ·
                  refine ⟨1780248839820643027788869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186832559880428685192579 1780248839820643027788869)
                  ·
                    refine ⟨333796657466370567710413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1780248839820643027788869 333796657466370567710413)
                    ·
                      refine ⟨125173746549888962891405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333796657466370567710413 125173746549888962891405)
                      ·
                        rfl

theorem cell23_243775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_243775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243775 prefixEnd_243775 := by exact prefixLift 243775
  have htrace : WordTrace (prefixWord ++ tailWord_243775) baseStart_243775 baseEnd_243775 := by
    simpa [prefixWord, tailWord_243775, baseEnd_243775] using wordTrace_append hprefix tailTrace_243775
  have hstable : (prefixWord ++ tailWord_243775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243775).length < 2 ^ (prefixWord ++ tailWord_243775).sum := by decide
  have hdescent : baseEnd_243775 < baseStart_243775 := by decide
  rcases family_descends (prefixWord ++ tailWord_243775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243782 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_243782 : Nat := 118140960795 + 243782 * 2 ^ 59
def prefixEnd_243782 : Nat := 4983230072969 + 3 ^ 40 * 243782 * 2
def baseEnd_243782 : Nat := 41725780304823478501291

theorem tailTrace_243782 : CollatzResearch.WordTrace tailWord_243782 prefixEnd_243782 41725780304823478501291 := by
  unfold tailWord_243782
  simp only [CollatzResearch.WordTrace]
  refine ⟨277858125088341359250175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5927640001884615664003733 277858125088341359250175)
  ·
    refine ⟨416787187632512038875263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277858125088341359250175 416787187632512038875263)
    ·
      refine ⟨625180781448768058312895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416787187632512038875263 625180781448768058312895)
      ·
        refine ⟨937771172173152087469343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625180781448768058312895 937771172173152087469343)
        ·
          refine ⟨1406656758259728131204015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937771172173152087469343 1406656758259728131204015)
          ·
            refine ⟨2109985137389592196806023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406656758259728131204015 2109985137389592196806023)
            ·
              refine ⟨3164977706084388295209035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109985137389592196806023 3164977706084388295209035)
              ·
                refine ⟨4747466559126582442813553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164977706084388295209035 4747466559126582442813553)
                ·
                  refine ⟨3560599919344936832110165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4747466559126582442813553 3560599919344936832110165)
                  ·
                    refine ⟨41725780304823478501291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3560599919344936832110165 41725780304823478501291)
                    ·
                      rfl

theorem cell23_243782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_243782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243782 prefixEnd_243782 := by exact prefixLift 243782
  have htrace : WordTrace (prefixWord ++ tailWord_243782) baseStart_243782 baseEnd_243782 := by
    simpa [prefixWord, tailWord_243782, baseEnd_243782] using wordTrace_append hprefix tailTrace_243782
  have hstable : (prefixWord ++ tailWord_243782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243782).length < 2 ^ (prefixWord ++ tailWord_243782).sum := by decide
  have hdescent : baseEnd_243782 < baseStart_243782 := by decide
  rcases family_descends (prefixWord ++ tailWord_243782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243799 : List Nat := [1, 1, 3, 2, 2, 1, 5, 3, 1, 4]
def baseStart_243799 : Nat := 118140960795 + 243799 * 2 ^ 59
def prefixEnd_243799 : Nat := 4983230072969 + 3 ^ 40 * 243799 * 2
def baseEnd_243799 : Nat := 41728690028532289663765

theorem tailTrace_243799 : CollatzResearch.WordTrace tailWord_243799 prefixEnd_243799 41728690028532289663765 := by
  unfold tailWord_243799
  simp only [CollatzResearch.WordTrace]
  refine ⟨8892080043765335399374451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5928053362510223599582967 8892080043765335399374451)
  ·
    refine ⟨13338120065648003099061677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8892080043765335399374451 13338120065648003099061677)
    ·
      refine ⟨5001795024618001162148129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13338120065648003099061677 5001795024618001162148129)
      ·
        refine ⟨3751346268463500871611097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5001795024618001162148129 3751346268463500871611097)
        ·
          refine ⟨2813509701347625653708323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3751346268463500871611097 2813509701347625653708323)
          ·
            refine ⟨4220264552021438480562485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813509701347625653708323 4220264552021438480562485)
            ·
              refine ⟨395649801752009857552733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4220264552021438480562485 395649801752009857552733)
              ·
                refine ⟨148368675657003696582275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395649801752009857552733 148368675657003696582275)
                ·
                  refine ⟨222553013485505544873413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148368675657003696582275 222553013485505544873413)
                  ·
                    refine ⟨41728690028532289663765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222553013485505544873413 41728690028532289663765)
                    ·
                      rfl

theorem cell23_243799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_243799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243799 prefixEnd_243799 := by exact prefixLift 243799
  have htrace : WordTrace (prefixWord ++ tailWord_243799) baseStart_243799 baseEnd_243799 := by
    simpa [prefixWord, tailWord_243799, baseEnd_243799] using wordTrace_append hprefix tailTrace_243799
  have hstable : (prefixWord ++ tailWord_243799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243799).length < 2 ^ (prefixWord ++ tailWord_243799).sum := by decide
  have hdescent : baseEnd_243799 < baseStart_243799 := by decide
  rcases family_descends (prefixWord ++ tailWord_243799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243825 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 3, 5]
def baseStart_243825 : Nat := 118140960795 + 243825 * 2 ^ 59
def prefixEnd_243825 : Nat := 4983230072969 + 3 ^ 40 * 243825 * 2
def baseEnd_243825 : Nat := 41733140194204589088725

theorem tailTrace_243825 : CollatzResearch.WordTrace tailWord_243825 prefixEnd_243825 41733140194204589088725 := by
  unfold tailWord_243825
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893028341671141839820929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5928685561114094559880619 8893028341671141839820929)
  ·
    refine ⟨6669771256253356379865697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8893028341671141839820929 6669771256253356379865697)
    ·
      refine ⟨5002328442190017284899273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6669771256253356379865697 5002328442190017284899273)
      ·
        refine ⟨3751746331642512963674455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5002328442190017284899273 3751746331642512963674455)
        ·
          refine ⟨5627619497463769445511683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751746331642512963674455 5627619497463769445511683)
          ·
            refine ⟨8441429246195654168267525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627619497463769445511683 8441429246195654168267525)
            ·
              refine ⟨1582767983661685156550161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8441429246195654168267525 1582767983661685156550161)
              ·
                refine ⟨1187075987746263867412621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582767983661685156550161 1187075987746263867412621)
                ·
                  refine ⟨445153495404848950279733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187075987746263867412621 445153495404848950279733)
                  ·
                    refine ⟨41733140194204589088725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 445153495404848950279733 41733140194204589088725)
                    ·
                      rfl

theorem cell23_243825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_243825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243825 prefixEnd_243825 := by exact prefixLift 243825
  have htrace : WordTrace (prefixWord ++ tailWord_243825) baseStart_243825 baseEnd_243825 := by
    simpa [prefixWord, tailWord_243825, baseEnd_243825] using wordTrace_append hprefix tailTrace_243825
  have hstable : (prefixWord ++ tailWord_243825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243825).length < 2 ^ (prefixWord ++ tailWord_243825).sum := by decide
  have hdescent : baseEnd_243825 < baseStart_243825 := by decide
  rcases family_descends (prefixWord ++ tailWord_243825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243832 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 6, 3, 2]
def baseStart_243832 : Nat := 118140960795 + 243832 * 2 ^ 59
def prefixEnd_243832 : Nat := 4983230072969 + 3 ^ 40 * 243832 * 2
def baseEnd_243832 : Nat := 125203014947195239878643

theorem tailTrace_243832 : CollatzResearch.WordTrace tailWord_243832 prefixEnd_243832 125203014947195239878643 := by
  unfold tailWord_243832
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446641826322891017662875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5928855768430521356883833 4446641826322891017662875)
  ·
    refine ⟨6669962739484336526494313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4446641826322891017662875 6669962739484336526494313)
    ·
      refine ⟨5002472054613252394870735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6669962739484336526494313 5002472054613252394870735)
      ·
        refine ⟨7503708081919878592306103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002472054613252394870735 7503708081919878592306103)
        ·
          refine ⟨11255562122879817888459155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503708081919878592306103 11255562122879817888459155)
          ·
            refine ⟨16883343184319726832688733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11255562122879817888459155 16883343184319726832688733)
            ·
              refine ⟨6331253694119897562258275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16883343184319726832688733 6331253694119897562258275)
              ·
                refine ⟨9496880541179846343387413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331253694119897562258275 9496880541179846343387413)
                ·
                  refine ⟨445166275367805297346285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9496880541179846343387413 445166275367805297346285)
                  ·
                    refine ⟨166937353262926986504857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445166275367805297346285 166937353262926986504857)
                    ·
                      refine ⟨125203014947195239878643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166937353262926986504857 125203014947195239878643)
                      ·
                        rfl

theorem cell23_243832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_243832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243832 prefixEnd_243832 := by exact prefixLift 243832
  have htrace : WordTrace (prefixWord ++ tailWord_243832) baseStart_243832 baseEnd_243832 := by
    simpa [prefixWord, tailWord_243832, baseEnd_243832] using wordTrace_append hprefix tailTrace_243832
  have hstable : (prefixWord ++ tailWord_243832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243832).length < 2 ^ (prefixWord ++ tailWord_243832).sum := by decide
  have hdescent : baseEnd_243832 < baseStart_243832 := by decide
  rcases family_descends (prefixWord ++ tailWord_243832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243849 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 2, 3, 2]
def baseStart_243849 : Nat := 118140960795 + 243849 * 2 ^ 59
def prefixEnd_243849 : Nat := 4983230072969 + 3 ^ 40 * 243849 * 2
def baseEnd_243849 : Nat := 125211744118321673366065

theorem tailTrace_243849 : CollatzResearch.WordTrace tailWord_243849 prefixEnd_243849 125211744118321673366065 := by
  unfold tailWord_243849
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893903693584193938694601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5929269129056129292463067 8893903693584193938694601)
  ·
    refine ⟨6670427770188145454020951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8893903693584193938694601 6670427770188145454020951)
    ·
      refine ⟨10005641655282218181031427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6670427770188145454020951 10005641655282218181031427)
      ·
        refine ⟨15008462482923327271547141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10005641655282218181031427 15008462482923327271547141)
        ·
          refine ⟨2814086715548123863415089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15008462482923327271547141 2814086715548123863415089)
          ·
            refine ⟨2110565036661092897561317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814086715548123863415089 2110565036661092897561317)
            ·
              refine ⟨395730944373954918292747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2110565036661092897561317 395730944373954918292747)
              ·
                refine ⟨593596416560932377439121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395730944373954918292747 593596416560932377439121)
                ·
                  refine ⟨445197312420699283079341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593596416560932377439121 445197312420699283079341)
                  ·
                    refine ⟨166948992157762231154753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445197312420699283079341 166948992157762231154753)
                    ·
                      refine ⟨125211744118321673366065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166948992157762231154753 125211744118321673366065)
                      ·
                        rfl

theorem cell23_243849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 3, 2].length) (baseStart_243849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243849 prefixEnd_243849 := by exact prefixLift 243849
  have htrace : WordTrace (prefixWord ++ tailWord_243849) baseStart_243849 baseEnd_243849 := by
    simpa [prefixWord, tailWord_243849, baseEnd_243849] using wordTrace_append hprefix tailTrace_243849
  have hstable : (prefixWord ++ tailWord_243849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243849).length < 2 ^ (prefixWord ++ tailWord_243849).sum := by decide
  have hdescent : baseEnd_243849 < baseStart_243849 := by decide
  rcases family_descends (prefixWord ++ tailWord_243849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243873 : List Nat := [1, 2, 3, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_243873 : Nat := 118140960795 + 243873 * 2 ^ 59
def prefixEnd_243873 : Nat := 4983230072969 + 3 ^ 40 * 243873 * 2
def baseEnd_243873 : Nat := 125224067654029579465955

theorem tailTrace_243873 : CollatzResearch.WordTrace tailWord_243873 prefixEnd_243873 125224067654029579465955 := by
  unfold tailWord_243873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894779045497246037568273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5929852696998164025045515 8894779045497246037568273)
  ·
    refine ⟨6671084284122934528176205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8894779045497246037568273 6671084284122934528176205)
    ·
      refine ⟨2501656606546100448066077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6671084284122934528176205 2501656606546100448066077)
      ·
        refine ⟨938121227454787668024779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2501656606546100448066077 938121227454787668024779)
        ·
          refine ⟨1407181841182181502037169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938121227454787668024779 1407181841182181502037169)
          ·
            refine ⟨1055386380886636126527877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1407181841182181502037169 1055386380886636126527877)
            ·
              refine ⟨197884946416244273723977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1055386380886636126527877 197884946416244273723977)
              ·
                refine ⟨148413709812183205292983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197884946416244273723977 148413709812183205292983)
                ·
                  refine ⟨222620564718274807939475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148413709812183205292983 222620564718274807939475)
                  ·
                    refine ⟨333930847077412211909213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222620564718274807939475 333930847077412211909213)
                    ·
                      refine ⟨125224067654029579465955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 333930847077412211909213 125224067654029579465955)
                      ·
                        rfl

theorem cell23_243873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_243873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243873 prefixEnd_243873 := by exact prefixLift 243873
  have htrace : WordTrace (prefixWord ++ tailWord_243873) baseStart_243873 baseEnd_243873 := by
    simpa [prefixWord, tailWord_243873, baseEnd_243873] using wordTrace_append hprefix tailTrace_243873
  have hstable : (prefixWord ++ tailWord_243873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243873).length < 2 ^ (prefixWord ++ tailWord_243873).sum := by decide
  have hdescent : baseEnd_243873 < baseStart_243873 := by decide
  rcases family_descends (prefixWord ++ tailWord_243873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243889 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 1, 6]
def baseStart_243889 : Nat := 118140960795 + 243889 * 2 ^ 59
def prefixEnd_243889 : Nat := 4983230072969 + 3 ^ 40 * 243889 * 2
def baseEnd_243889 : Nat := 41744094448167172288627

theorem tailTrace_243889 : CollatzResearch.WordTrace tailWord_243889 prefixEnd_243889 41744094448167172288627 := by
  unfold tailWord_243889
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895362613439280770150721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5930241742292853846767147 8895362613439280770150721)
  ·
    refine ⟨6671521960079460577613041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8895362613439280770150721 6671521960079460577613041)
    ·
      refine ⟨5003641470059595433209781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6671521960079460577613041 5003641470059595433209781)
      ·
        refine ⟨469091387818087071863417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5003641470059595433209781 469091387818087071863417)
        ·
          refine ⟨351818540863565303897563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469091387818087071863417 351818540863565303897563)
          ·
            refine ⟨527727811295347955846345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351818540863565303897563 527727811295347955846345)
            ·
              refine ⟨395795858471510966884759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527727811295347955846345 395795858471510966884759)
              ·
                refine ⟨593693787707266450327139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395795858471510966884759 593693787707266450327139)
                ·
                  refine ⟨890540681560899675490709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593693787707266450327139 890540681560899675490709)
                  ·
                    refine ⟨41744094448167172288627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 890540681560899675490709 41744094448167172288627)
                    ·
                      rfl

theorem cell23_243889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_243889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243889 prefixEnd_243889 := by exact prefixLift 243889
  have htrace : WordTrace (prefixWord ++ tailWord_243889) baseStart_243889 baseEnd_243889 := by
    simpa [prefixWord, tailWord_243889, baseEnd_243889] using wordTrace_append hprefix tailTrace_243889
  have hstable : (prefixWord ++ tailWord_243889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243889).length < 2 ^ (prefixWord ++ tailWord_243889).sum := by decide
  have hdescent : baseEnd_243889 < baseStart_243889 := by decide
  rcases family_descends (prefixWord ++ tailWord_243889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243906 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_243906 : Nat := 118140960795 + 243906 * 2 ^ 59
def prefixEnd_243906 : Nat := 4983230072969 + 3 ^ 40 * 243906 * 2
def baseEnd_243906 : Nat := 41747004171875983451101

theorem tailTrace_243906 : CollatzResearch.WordTrace tailWord_243906 prefixEnd_243906 41747004171875983451101 := by
  unfold tailWord_243906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223995663594423168379893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5930655102918461782346381 2223995663594423168379893)
  ·
    refine ⟨208499593461977172035615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2223995663594423168379893 208499593461977172035615)
    ·
      refine ⟨312749390192965758053423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208499593461977172035615 312749390192965758053423)
      ·
        refine ⟨469124085289448637080135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312749390192965758053423 469124085289448637080135)
        ·
          refine ⟨703686127934172955620203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469124085289448637080135 703686127934172955620203)
          ·
            refine ⟨1055529191901259433430305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703686127934172955620203 1055529191901259433430305)
            ·
              refine ⟨791646893925944575072729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055529191901259433430305 791646893925944575072729)
              ·
                refine ⟨593735170444458431304547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791646893925944575072729 593735170444458431304547)
                ·
                  refine ⟨890602755666687646956821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593735170444458431304547 890602755666687646956821)
                  ·
                    refine ⟨41747004171875983451101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 890602755666687646956821 41747004171875983451101)
                    ·
                      rfl

theorem cell23_243906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_243906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243906 prefixEnd_243906 := by exact prefixLift 243906
  have htrace : WordTrace (prefixWord ++ tailWord_243906) baseStart_243906 baseEnd_243906 := by
    simpa [prefixWord, tailWord_243906, baseEnd_243906] using wordTrace_append hprefix tailTrace_243906
  have hstable : (prefixWord ++ tailWord_243906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243906).length < 2 ^ (prefixWord ++ tailWord_243906).sum := by decide
  have hdescent : baseEnd_243906 < baseStart_243906 := by decide
  rcases family_descends (prefixWord ++ tailWord_243906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243969 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_243969 : Nat := 118140960795 + 243969 * 2 ^ 59
def prefixEnd_243969 : Nat := 4983230072969 + 3 ^ 40 * 243969 * 2
def baseEnd_243969 : Nat := 125273361796861203865513

theorem tailTrace_243969 : CollatzResearch.WordTrace tailWord_243969 prefixEnd_243969 125273361796861203865513 := by
  unfold tailWord_243969
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898280453149454433062961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5932186968766302955375307 8898280453149454433062961)
  ·
    refine ⟨6673710339862090824797221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8898280453149454433062961 6673710339862090824797221)
    ·
      refine ⟨1251320688724142029649479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6673710339862090824797221 1251320688724142029649479)
      ·
        refine ⟨1876981033086213044474219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251320688724142029649479 1876981033086213044474219)
        ·
          refine ⟨2815471549629319566711329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876981033086213044474219 2815471549629319566711329)
          ·
            refine ⟨2111603662221989675033497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2815471549629319566711329 2111603662221989675033497)
            ·
              refine ⟨1583702746666492256275123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111603662221989675033497 1583702746666492256275123)
              ·
                refine ⟨2375554119999738384412685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583702746666492256275123 2375554119999738384412685)
                ·
                  refine ⟨890832794999901894154757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2375554119999738384412685 890832794999901894154757)
                  ·
                    refine ⟨167031149062481605154017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890832794999901894154757 167031149062481605154017)
                    ·
                      refine ⟨125273361796861203865513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167031149062481605154017 125273361796861203865513)
                      ·
                        rfl

theorem cell23_243969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_243969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243969 prefixEnd_243969 := by exact prefixLift 243969
  have htrace : WordTrace (prefixWord ++ tailWord_243969) baseStart_243969 baseEnd_243969 := by
    simpa [prefixWord, tailWord_243969, baseEnd_243969] using wordTrace_append hprefix tailTrace_243969
  have hstable : (prefixWord ++ tailWord_243969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243969).length < 2 ^ (prefixWord ++ tailWord_243969).sum := by decide
  have hdescent : baseEnd_243969 < baseStart_243969 := by decide
  rcases family_descends (prefixWord ++ tailWord_243969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243997 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_243997 : Nat := 118140960795 + 243997 * 2 ^ 59
def prefixEnd_243997 : Nat := 4983230072969 + 3 ^ 40 * 243997 * 2
def baseEnd_243997 : Nat := 125287739255187094315385

theorem tailTrace_243997 : CollatzResearch.WordTrace tailWord_243997 prefixEnd_243997 125287739255187094315385 := by
  unfold tailWord_243997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899301697048015215082245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5932867798032010143388163 8899301697048015215082245)
  ·
    refine ⟨1668619068196502852827921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8899301697048015215082245 1668619068196502852827921)
    ·
      refine ⟨1251464301147377139620941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1668619068196502852827921 1251464301147377139620941)
      ·
        refine ⟨469299112930266427357853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1251464301147377139620941 469299112930266427357853)
        ·
          refine ⟨175987167348849910259195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469299112930266427357853 175987167348849910259195)
          ·
            refine ⟨263980751023274865388793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175987167348849910259195 263980751023274865388793)
            ·
              refine ⟨197985563267456149041595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263980751023274865388793 197985563267456149041595)
              ·
                refine ⟨296978344901184223562393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197985563267456149041595 296978344901184223562393)
                ·
                  refine ⟨222733758675888167671795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296978344901184223562393 222733758675888167671795)
                  ·
                    refine ⟨334100638013832251507693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222733758675888167671795 334100638013832251507693)
                    ·
                      refine ⟨125287739255187094315385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334100638013832251507693 125287739255187094315385)
                      ·
                        rfl

theorem cell23_243997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_243997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243997 prefixEnd_243997 := by exact prefixLift 243997
  have htrace : WordTrace (prefixWord ++ tailWord_243997) baseStart_243997 baseEnd_243997 := by
    simpa [prefixWord, tailWord_243997, baseEnd_243997] using wordTrace_append hprefix tailTrace_243997
  have hstable : (prefixWord ++ tailWord_243997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243997).length < 2 ^ (prefixWord ++ tailWord_243997).sum := by decide
  have hdescent : baseEnd_243997 < baseStart_243997 := by decide
  rcases family_descends (prefixWord ++ tailWord_243997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244042 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_244042 : Nat := 118140960795 + 244042 * 2 ^ 59
def prefixEnd_244042 : Nat := 4983230072969 + 3 ^ 40 * 244042 * 2
def baseEnd_244042 : Nat := 125310845884639418252677

theorem tailTrace_244042 : CollatzResearch.WordTrace tailWord_244042 prefixEnd_244042 125310845884639418252677 := by
  unfold tailWord_244042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2225235745471246975117595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5933961987923325266980253 2225235745471246975117595)
  ·
    refine ⟨3337853618206870462676393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2225235745471246975117595 3337853618206870462676393)
    ·
      refine ⟨2503390213655152847007295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3337853618206870462676393 2503390213655152847007295)
      ·
        refine ⟨3755085320482729270510943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503390213655152847007295 3755085320482729270510943)
        ·
          refine ⟨5632627980724093905766415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755085320482729270510943 5632627980724093905766415)
          ·
            refine ⟨8448941971086140858649623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632627980724093905766415 8448941971086140858649623)
            ·
              refine ⟨12673412956629211287974435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448941971086140858649623 12673412956629211287974435)
              ·
                refine ⟨19010119434943816931961653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12673412956629211287974435 19010119434943816931961653)
                ·
                  refine ⟨1782198697025982837371405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19010119434943816931961653 1782198697025982837371405)
                  ·
                    refine ⟨668324511384743564014277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782198697025982837371405 668324511384743564014277)
                    ·
                      refine ⟨125310845884639418252677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 668324511384743564014277 125310845884639418252677)
                      ·
                        rfl

theorem cell23_244042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_244042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244042 prefixEnd_244042 := by exact prefixLift 244042
  have htrace : WordTrace (prefixWord ++ tailWord_244042) baseStart_244042 baseEnd_244042 := by
    simpa [prefixWord, tailWord_244042, baseEnd_244042] using wordTrace_append hprefix tailTrace_244042
  have hstable : (prefixWord ++ tailWord_244042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244042).length < 2 ^ (prefixWord ++ tailWord_244042).sum := by decide
  have hdescent : baseEnd_244042 < baseStart_244042 := by decide
  rcases family_descends (prefixWord ++ tailWord_244042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244069 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_244069 : Nat := 118140960795 + 244069 * 2 ^ 59
def prefixEnd_244069 : Nat := 4983230072969 + 3 ^ 40 * 244069 * 2
def baseEnd_244069 : Nat := 41774903287436937538351

theorem tailTrace_244069 : CollatzResearch.WordTrace tailWord_244069 prefixEnd_244069 41774903287436937538351 := by
  unfold tailWord_244069
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901927752787171511703261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5934618501858114341135507 8901927752787171511703261)
  ·
    refine ⟨3338222907295189316888723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8901927752787171511703261 3338222907295189316888723)
    ·
      refine ⟨5007334360942783975333085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3338222907295189316888723 5007334360942783975333085)
      ·
        refine ⟨1877750385353543990749907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5007334360942783975333085 1877750385353543990749907)
        ·
          refine ⟨2816625578030315986124861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877750385353543990749907 2816625578030315986124861)
          ·
            refine ⟨1056234591761368494796823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2816625578030315986124861 1056234591761368494796823)
            ·
              refine ⟨1584351887642052742195235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056234591761368494796823 1584351887642052742195235)
              ·
                refine ⟨2376527831463079113292853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584351887642052742195235 2376527831463079113292853)
                ·
                  refine ⟨222799484199663666871205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376527831463079113292853 222799484199663666871205)
                  ·
                    refine ⟨41774903287436937538351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222799484199663666871205 41774903287436937538351)
                    ·
                      rfl

theorem cell23_244069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_244069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244069 prefixEnd_244069 := by exact prefixLift 244069
  have htrace : WordTrace (prefixWord ++ tailWord_244069) baseStart_244069 baseEnd_244069 := by
    simpa [prefixWord, tailWord_244069, baseEnd_244069] using wordTrace_append hprefix tailTrace_244069
  have hstable : (prefixWord ++ tailWord_244069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244069).length < 2 ^ (prefixWord ++ tailWord_244069).sum := by decide
  have hdescent : baseEnd_244069 < baseStart_244069 := by decide
  rcases family_descends (prefixWord ++ tailWord_244069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244079 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 3]
def baseStart_244079 : Nat := 118140960795 + 244079 * 2 ^ 59
def prefixEnd_244079 : Nat := 4983230072969 + 3 ^ 40 * 244079 * 2
def baseEnd_244079 : Nat := 125329844668855773490007

theorem tailTrace_244079 : CollatzResearch.WordTrace tailWord_244079 prefixEnd_244079 125329844668855773490007 := by
  unfold tailWord_244079
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902292482750943219567291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5934861655167295479711527 8902292482750943219567291)
  ·
    refine ⟨13353438724126414829350937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8902292482750943219567291 13353438724126414829350937)
    ·
      refine ⟨10015079043094811122013203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13353438724126414829350937 10015079043094811122013203)
      ·
        refine ⟨15022618564642216683019805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10015079043094811122013203 15022618564642216683019805)
        ·
          refine ⟨5633481961740831256132427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15022618564642216683019805 5633481961740831256132427)
          ·
            refine ⟨8450222942611246884198641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633481961740831256132427 8450222942611246884198641)
            ·
              refine ⟨6337667206958435163148981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8450222942611246884198641 6337667206958435163148981)
              ·
                refine ⟨594156300652353296545217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6337667206958435163148981 594156300652353296545217)
                ·
                  refine ⟨445617225489264972408913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594156300652353296545217 445617225489264972408913)
                  ·
                    refine ⟨334212919116948729306685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445617225489264972408913 334212919116948729306685)
                    ·
                      refine ⟨125329844668855773490007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334212919116948729306685 125329844668855773490007)
                      ·
                        rfl

theorem cell23_244079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_244079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244079 prefixEnd_244079 := by exact prefixLift 244079
  have htrace : WordTrace (prefixWord ++ tailWord_244079) baseStart_244079 baseEnd_244079 := by
    simpa [prefixWord, tailWord_244079, baseEnd_244079] using wordTrace_append hprefix tailTrace_244079
  have hstable : (prefixWord ++ tailWord_244079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244079).length < 2 ^ (prefixWord ++ tailWord_244079).sum := by decide
  have hdescent : baseEnd_244079 < baseStart_244079 := by decide
  rcases family_descends (prefixWord ++ tailWord_244079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244099 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 8]
def baseStart_244099 : Nat := 118140960795 + 244099 * 2 ^ 59
def prefixEnd_244099 : Nat := 4983230072969 + 3 ^ 40 * 244099 * 2
def baseEnd_244099 : Nat := 13926679364660632804435

theorem tailTrace_244099 : CollatzResearch.WordTrace tailWord_244099 prefixEnd_244099 13926679364660632804435 := by
  unfold tailWord_244099
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903021942678486635295351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5935347961785657756863567 8903021942678486635295351)
  ·
    refine ⟨13354532914017729952943027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8903021942678486635295351 13354532914017729952943027)
    ·
      refine ⟨20031799371026594929414541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13354532914017729952943027 20031799371026594929414541)
      ·
        refine ⟨7511924764134973098530453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20031799371026594929414541 7511924764134973098530453)
        ·
          refine ⟨352121473318826863993615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7511924764134973098530453 352121473318826863993615)
          ·
            refine ⟨528182209978240295990423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352121473318826863993615 528182209978240295990423)
            ·
              refine ⟨792273314967360443985635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528182209978240295990423 792273314967360443985635)
              ·
                refine ⟨1188409972451040665978453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792273314967360443985635 1188409972451040665978453)
                ·
                  refine ⟨13926679364660632804435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1188409972451040665978453 13926679364660632804435)
                  ·
                    rfl

theorem cell23_244099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 8].length) (baseStart_244099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244099 prefixEnd_244099 := by exact prefixLift 244099
  have htrace : WordTrace (prefixWord ++ tailWord_244099) baseStart_244099 baseEnd_244099 := by
    simpa [prefixWord, tailWord_244099, baseEnd_244099] using wordTrace_append hprefix tailTrace_244099
  have hstable : (prefixWord ++ tailWord_244099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244099).length < 2 ^ (prefixWord ++ tailWord_244099).sum := by decide
  have hdescent : baseEnd_244099 < baseStart_244099 := by decide
  rcases family_descends (prefixWord ++ tailWord_244099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244153 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 2, 3, 2]
def baseStart_244153 : Nat := 118140960795 + 244153 * 2 ^ 59
def prefixEnd_244153 : Nat := 4983230072969 + 3 ^ 40 * 244153 * 2
def baseEnd_244153 : Nat := 125367842237288483964667

theorem tailTrace_244153 : CollatzResearch.WordTrace tailWord_244153 prefixEnd_244153 125367842237288483964667 := by
  unfold tailWord_244153
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904991484482853857761113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5936660989655235905174075 8904991484482853857761113)
  ·
    refine ⟨6678743613362140393320835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8904991484482853857761113 6678743613362140393320835)
    ·
      refine ⟨10018115420043210589981253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678743613362140393320835 10018115420043210589981253)
      ·
        refine ⟨1878396641258101985621485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10018115420043210589981253 1878396641258101985621485)
        ·
          refine ⟨704398740471788244608057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1878396641258101985621485 704398740471788244608057)
          ·
            refine ⟨528299055353841183456043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704398740471788244608057 528299055353841183456043)
            ·
              refine ⟨792448583030761775184065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528299055353841183456043 792448583030761775184065)
              ·
                refine ⟨594336437273071331388049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792448583030761775184065 594336437273071331388049)
                ·
                  refine ⟨445752327954803498541037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594336437273071331388049 445752327954803498541037)
                  ·
                    refine ⟨167157122983051311952889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445752327954803498541037 167157122983051311952889)
                    ·
                      refine ⟨125367842237288483964667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167157122983051311952889 125367842237288483964667)
                      ·
                        rfl

theorem cell23_244153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_244153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244153 prefixEnd_244153 := by exact prefixLift 244153
  have htrace : WordTrace (prefixWord ++ tailWord_244153) baseStart_244153 baseEnd_244153 := by
    simpa [prefixWord, tailWord_244153, baseEnd_244153] using wordTrace_append hprefix tailTrace_244153
  have hstable : (prefixWord ++ tailWord_244153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244153).length < 2 ^ (prefixWord ++ tailWord_244153).sum := by decide
  have hdescent : baseEnd_244153 < baseStart_244153 := by decide
  rcases family_descends (prefixWord ++ tailWord_244153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244169 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_244169 : Nat := 118140960795 + 244169 * 2 ^ 59
def prefixEnd_244169 : Nat := 4983230072969 + 3 ^ 40 * 244169 * 2
def baseEnd_244169 : Nat := 125376057927760421364593

theorem tailTrace_244169 : CollatzResearch.WordTrace tailWord_244169 prefixEnd_244169 125376057927760421364593 := by
  unfold tailWord_244169
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905575052424888590343561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5937050034949925726895707 8905575052424888590343561)
  ·
    refine ⟨6679181289318666442757671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8905575052424888590343561 6679181289318666442757671)
    ·
      refine ⟨10018771933977999664136507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679181289318666442757671 10018771933977999664136507)
      ·
        refine ⟨15028157900966999496204761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10018771933977999664136507 15028157900966999496204761)
        ·
          refine ⟨11271118425725249622153571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15028157900966999496204761 11271118425725249622153571)
          ·
            refine ⟨16906677638587874433230357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11271118425725249622153571 16906677638587874433230357)
            ·
              refine ⟨792500514308806614057673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16906677638587874433230357 792500514308806614057673)
              ·
                refine ⟨594375385731604960543255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792500514308806614057673 594375385731604960543255)
                ·
                  refine ⟨891563078597407440814883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594375385731604960543255 891563078597407440814883)
                  ·
                    refine ⟨1337344617896111161222325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 891563078597407440814883 1337344617896111161222325)
                    ·
                      refine ⟨125376057927760421364593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1337344617896111161222325 125376057927760421364593)
                      ·
                        rfl

theorem cell23_244169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_244169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244169 prefixEnd_244169 := by exact prefixLift 244169
  have htrace : WordTrace (prefixWord ++ tailWord_244169) baseStart_244169 baseEnd_244169 := by
    simpa [prefixWord, tailWord_244169, baseEnd_244169] using wordTrace_append hprefix tailTrace_244169
  have hstable : (prefixWord ++ tailWord_244169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244169).length < 2 ^ (prefixWord ++ tailWord_244169).sum := by decide
  have hdescent : baseEnd_244169 < baseStart_244169 := by decide
  rcases family_descends (prefixWord ++ tailWord_244169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244186 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_244186 : Nat := 118140960795 + 244186 * 2 ^ 59
def prefixEnd_244186 : Nat := 4983230072969 + 3 ^ 40 * 244186 * 2
def baseEnd_244186 : Nat := 125384787098886854852015

theorem tailTrace_244186 : CollatzResearch.WordTrace tailWord_244186 prefixEnd_244186 125384787098886854852015 := by
  unfold tailWord_244186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226548773340825123428103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5937463395575533662474941 2226548773340825123428103)
  ·
    refine ⟨3339823160011237685142155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2226548773340825123428103 3339823160011237685142155)
    ·
      refine ⟨5009734740016856527713233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3339823160011237685142155 5009734740016856527713233)
      ·
        refine ⟨3757301055012642395784925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5009734740016856527713233 3757301055012642395784925)
        ·
          refine ⟨1408987895629740898419347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3757301055012642395784925 1408987895629740898419347)
          ·
            refine ⟨2113481843444611347629021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408987895629740898419347 2113481843444611347629021)
            ·
              refine ⟨792555691291729255360883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2113481843444611347629021 792555691291729255360883)
              ·
                refine ⟨1188833536937593883041325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792555691291729255360883 1188833536937593883041325)
                ·
                  refine ⟨445812576351597706140497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188833536937593883041325 445812576351597706140497)
                  ·
                    refine ⟨334359432263698279605373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445812576351597706140497 334359432263698279605373)
                    ·
                      refine ⟨125384787098886854852015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334359432263698279605373 125384787098886854852015)
                      ·
                        rfl

theorem cell23_244186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_244186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244186 prefixEnd_244186 := by exact prefixLift 244186
  have htrace : WordTrace (prefixWord ++ tailWord_244186) baseStart_244186 baseEnd_244186 := by
    simpa [prefixWord, tailWord_244186, baseEnd_244186] using wordTrace_append hprefix tailTrace_244186
  have hstable : (prefixWord ++ tailWord_244186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244186).length < 2 ^ (prefixWord ++ tailWord_244186).sum := by decide
  have hdescent : baseEnd_244186 < baseStart_244186 := by decide
  rcases family_descends (prefixWord ++ tailWord_244186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244189 : List Nat := [1, 4, 3, 1, 1, 1, 1, 11]
def baseStart_244189 : Nat := 118140960795 + 244189 * 2 ^ 59
def prefixEnd_244189 : Nat := 4983230072969 + 3 ^ 40 * 244189 * 2
def baseEnd_244189 : Nat := 4643938057068531226463

theorem tailTrace_244189 : CollatzResearch.WordTrace tailWord_244189 prefixEnd_244189 4643938057068531226463 := by
  unfold tailWord_244189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8906304512352432006071621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5937536341568288004047747 8906304512352432006071621)
  ·
    refine ⟨1669932096066081001138429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8906304512352432006071621 1669932096066081001138429)
    ·
      refine ⟨626224536024780375426911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1669932096066081001138429 626224536024780375426911)
      ·
        refine ⟨939336804037170563140367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626224536024780375426911 939336804037170563140367)
        ·
          refine ⟨1409005206055755844710551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939336804037170563140367 1409005206055755844710551)
          ·
            refine ⟨2113507809083633767065827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409005206055755844710551 2113507809083633767065827)
            ·
              refine ⟨3170261713625450650598741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113507809083633767065827 3170261713625450650598741)
              ·
                refine ⟨4643938057068531226463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 3170261713625450650598741 4643938057068531226463)
                ·
                  rfl

theorem cell23_244189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 11].length) (baseStart_244189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244189 prefixEnd_244189 := by exact prefixLift 244189
  have htrace : WordTrace (prefixWord ++ tailWord_244189) baseStart_244189 baseEnd_244189 := by
    simpa [prefixWord, tailWord_244189, baseEnd_244189] using wordTrace_append hprefix tailTrace_244189
  have hstable : (prefixWord ++ tailWord_244189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244189).length < 2 ^ (prefixWord ++ tailWord_244189).sum := by decide
  have hdescent : baseEnd_244189 < baseStart_244189 := by decide
  rcases family_descends (prefixWord ++ tailWord_244189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244203 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 1, 2, 3]
def baseStart_244203 : Nat := 118140960795 + 244203 * 2 ^ 59
def prefixEnd_244203 : Nat := 4983230072969 + 3 ^ 40 * 244203 * 2
def baseEnd_244203 : Nat := 125393516270013288339437

theorem tailTrace_244203 : CollatzResearch.WordTrace tailWord_244203 prefixEnd_244203 125393516270013288339437 := by
  unfold tailWord_244203
  simp only [CollatzResearch.WordTrace]
  refine ⟨8906815134301712397081263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5937876756201141598054175 8906815134301712397081263)
  ·
    refine ⟨13360222701452568595621895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8906815134301712397081263 13360222701452568595621895)
    ·
      refine ⟨20040334052178852893432843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13360222701452568595621895 20040334052178852893432843)
      ·
        refine ⟨30060501078268279340149265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20040334052178852893432843 30060501078268279340149265)
        ·
          refine ⟨22545375808701209505111949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30060501078268279340149265 22545375808701209505111949)
          ·
            refine ⟨8454515928262953564416981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22545375808701209505111949 8454515928262953564416981)
            ·
              refine ⟨198152717068662974166023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8454515928262953564416981 198152717068662974166023)
              ·
                refine ⟨297229075602994461249035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198152717068662974166023 297229075602994461249035)
                ·
                  refine ⟨445843613404491691873553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297229075602994461249035 445843613404491691873553)
                  ·
                    refine ⟨334382710053368768905165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445843613404491691873553 334382710053368768905165)
                    ·
                      refine ⟨125393516270013288339437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334382710053368768905165 125393516270013288339437)
                      ·
                        rfl

theorem cell23_244203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 2, 3].length) (baseStart_244203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244203 prefixEnd_244203 := by exact prefixLift 244203
  have htrace : WordTrace (prefixWord ++ tailWord_244203) baseStart_244203 baseEnd_244203 := by
    simpa [prefixWord, tailWord_244203, baseEnd_244203] using wordTrace_append hprefix tailTrace_244203
  have hstable : (prefixWord ++ tailWord_244203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244203).length < 2 ^ (prefixWord ++ tailWord_244203).sum := by decide
  have hdescent : baseEnd_244203 < baseStart_244203 := by decide
  rcases family_descends (prefixWord ++ tailWord_244203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244210 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_244210 : Nat := 118140960795 + 244210 * 2 ^ 59
def prefixEnd_244210 : Nat := 4983230072969 + 3 ^ 40 * 244210 * 2
def baseEnd_244210 : Nat := 41799036878198253650635

theorem tailTrace_244210 : CollatzResearch.WordTrace tailWord_244210 prefixEnd_244210 41799036878198253650635 := by
  unfold tailWord_244210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226767611319088148146521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5938046963517568395057389 2226767611319088148146521)
  ·
    refine ⟨1670075708489316111109891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2226767611319088148146521 1670075708489316111109891)
    ·
      refine ⟨2505113562733974166664837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670075708489316111109891 2505113562733974166664837)
      ·
        refine ⟨469708793012620156249657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2505113562733974166664837 469708793012620156249657)
        ·
          refine ⟨352281594759465117187243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469708793012620156249657 352281594759465117187243)
          ·
            refine ⟨528422392139197675780865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352281594759465117187243 528422392139197675780865)
            ·
              refine ⟨396316794104398256835649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528422392139197675780865 396316794104398256835649)
              ·
                refine ⟨297237595578298692626737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396316794104398256835649 297237595578298692626737)
                ·
                  refine ⟨222928196683724019470053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297237595578298692626737 222928196683724019470053)
                  ·
                    refine ⟨41799036878198253650635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222928196683724019470053 41799036878198253650635)
                    ·
                      rfl

theorem cell23_244210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_244210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244210 prefixEnd_244210 := by exact prefixLift 244210
  have htrace : WordTrace (prefixWord ++ tailWord_244210) baseStart_244210 baseEnd_244210 := by
    simpa [prefixWord, tailWord_244210, baseEnd_244210] using wordTrace_append hprefix tailTrace_244210
  have hstable : (prefixWord ++ tailWord_244210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244210).length < 2 ^ (prefixWord ++ tailWord_244210).sum := by decide
  have hdescent : baseEnd_244210 < baseStart_244210 := by decide
  rcases family_descends (prefixWord ++ tailWord_244210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244217 : List Nat := [1, 2, 1, 3, 1, 2, 6, 2, 1, 2, 2]
def baseStart_244217 : Nat := 118140960795 + 244217 * 2 ^ 59
def prefixEnd_244217 : Nat := 4983230072969 + 3 ^ 40 * 244217 * 2
def baseEnd_244217 : Nat := 125400704999176233564373

theorem tailTrace_244217 : CollatzResearch.WordTrace tailWord_244217 prefixEnd_244217 125400704999176233564373 := by
  unfold tailWord_244217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907325756250992788090905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5938217170833995192060603 8907325756250992788090905)
  ·
    refine ⟨6680494317188244591068179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8907325756250992788090905 6680494317188244591068179)
    ·
      refine ⟨10020741475782366886602269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680494317188244591068179 10020741475782366886602269)
      ·
        refine ⟨3757778053418387582475851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10020741475782366886602269 3757778053418387582475851)
        ·
          refine ⟨5636667080127581373713777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757778053418387582475851 5636667080127581373713777)
          ·
            refine ⟨4227500310095686030285333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5636667080127581373713777 4227500310095686030285333)
            ·
              refine ⟨198164077035735282669625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4227500310095686030285333 198164077035735282669625)
              ·
                refine ⟨148623057776801462002219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198164077035735282669625 148623057776801462002219)
                ·
                  refine ⟨222934586665202193003329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148623057776801462002219 222934586665202193003329)
                  ·
                    refine ⟨167200939998901644752497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222934586665202193003329 167200939998901644752497)
                    ·
                      refine ⟨125400704999176233564373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167200939998901644752497 125400704999176233564373)
                      ·
                        rfl

theorem cell23_244217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_244217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244217 prefixEnd_244217 := by exact prefixLift 244217
  have htrace : WordTrace (prefixWord ++ tailWord_244217) baseStart_244217 baseEnd_244217 := by
    simpa [prefixWord, tailWord_244217, baseEnd_244217] using wordTrace_append hprefix tailTrace_244217
  have hstable : (prefixWord ++ tailWord_244217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244217).length < 2 ^ (prefixWord ++ tailWord_244217).sum := by decide
  have hdescent : baseEnd_244217 < baseStart_244217 := by decide
  rcases family_descends (prefixWord ++ tailWord_244217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244243 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 1, 3, 2]
def baseStart_244243 : Nat := 118140960795 + 244243 * 2 ^ 59
def prefixEnd_244243 : Nat := 4983230072969 + 3 ^ 40 * 244243 * 2
def baseEnd_244243 : Nat := 125414055496193131839253

theorem tailTrace_244243 : CollatzResearch.WordTrace tailWord_244243 prefixEnd_244243 125414055496193131839253 := by
  unfold tailWord_244243
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908274054156799228537383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5938849369437866152358255 8908274054156799228537383)
  ·
    refine ⟨13362411081235198842806075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8908274054156799228537383 13362411081235198842806075)
    ·
      refine ⟨20043616621852798264209113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13362411081235198842806075 20043616621852798264209113)
      ·
        refine ⟨15032712466389598698156835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20043616621852798264209113 15032712466389598698156835)
        ·
          refine ⟨22549068699584398047235253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15032712466389598698156835 22549068699584398047235253)
          ·
            refine ⟨2113975190586037316928305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22549068699584398047235253 2113975190586037316928305)
            ·
              refine ⟨1585481392939527987696229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113975190586037316928305 1585481392939527987696229)
              ·
                refine ⟨297277761176161497693043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1585481392939527987696229 297277761176161497693043)
                ·
                  refine ⟨445916641764242246539565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297277761176161497693043 445916641764242246539565)
                  ·
                    refine ⟨167218740661590842452337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445916641764242246539565 167218740661590842452337)
                    ·
                      refine ⟨125414055496193131839253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167218740661590842452337 125414055496193131839253)
                      ·
                        rfl

theorem cell23_244243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 3, 2].length) (baseStart_244243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244243 prefixEnd_244243 := by exact prefixLift 244243
  have htrace : WordTrace (prefixWord ++ tailWord_244243) baseStart_244243 baseEnd_244243 := by
    simpa [prefixWord, tailWord_244243, baseEnd_244243] using wordTrace_append hprefix tailTrace_244243
  have hstable : (prefixWord ++ tailWord_244243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244243).length < 2 ^ (prefixWord ++ tailWord_244243).sum := by decide
  have hdescent : baseEnd_244243 < baseStart_244243 := by decide
  rcases family_descends (prefixWord ++ tailWord_244243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244266 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_244266 : Nat := 118140960795 + 244266 * 2 ^ 59
def prefixEnd_244266 : Nat := 4983230072969 + 3 ^ 40 * 244266 * 2
def baseEnd_244266 : Nat := 41808621850415513950549

theorem tailTrace_244266 : CollatzResearch.WordTrace tailWord_244266 prefixEnd_244266 41808621850415513950549 := by
  unfold tailWord_244266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227278233268368539156163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5939408622048982771083101 2227278233268368539156163)
  ·
    refine ⟨3340917349902552808734245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2227278233268368539156163 3340917349902552808734245)
    ·
      refine ⟨626422003106728651637671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3340917349902552808734245 626422003106728651637671)
      ·
        refine ⟨939633004660092977456507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626422003106728651637671 939633004660092977456507)
        ·
          refine ⟨1409449506990139466184761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939633004660092977456507 1409449506990139466184761)
          ·
            refine ⟨1057087130242604599638571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409449506990139466184761 1057087130242604599638571)
            ·
              refine ⟨1585630695363906899457857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057087130242604599638571 1585630695363906899457857)
              ·
                refine ⟨1189223021522930174593393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585630695363906899457857 1189223021522930174593393)
                ·
                  refine ⟨891917266142197630945045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1189223021522930174593393 891917266142197630945045)
                  ·
                    refine ⟨41808621850415513950549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 891917266142197630945045 41808621850415513950549)
                    ·
                      rfl

theorem cell23_244266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_244266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244266 prefixEnd_244266 := by exact prefixLift 244266
  have htrace : WordTrace (prefixWord ++ tailWord_244266) baseStart_244266 baseEnd_244266 := by
    simpa [prefixWord, tailWord_244266, baseEnd_244266] using wordTrace_append hprefix tailTrace_244266
  have hstable : (prefixWord ++ tailWord_244266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244266).length < 2 ^ (prefixWord ++ tailWord_244266).sum := by decide
  have hdescent : baseEnd_244266 < baseStart_244266 := by decide
  rcases family_descends (prefixWord ++ tailWord_244266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244294 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_244294 : Nat := 118140960795 + 244294 * 2 ^ 59
def prefixEnd_244294 : Nat := 4983230072969 + 3 ^ 40 * 244294 * 2
def baseEnd_244294 : Nat := 125440243009572432301519

theorem tailTrace_244294 : CollatzResearch.WordTrace tailWord_244294 prefixEnd_244294 125440243009572432301519 := by
  unfold tailWord_244294
  simp only [CollatzResearch.WordTrace]
  refine ⟨278441693030376091832623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5940089451314689959095957 278441693030376091832623)
  ·
    refine ⟨417662539545564137748935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278441693030376091832623 417662539545564137748935)
    ·
      refine ⟨626493809318346206623403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417662539545564137748935 626493809318346206623403)
      ·
        refine ⟨939740713977519309935105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626493809318346206623403 939740713977519309935105)
        ·
          refine ⟨704805535483139482451329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 939740713977519309935105 704805535483139482451329)
          ·
            refine ⟨528604151612354611838497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704805535483139482451329 528604151612354611838497)
            ·
              refine ⟨396453113709265958878873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528604151612354611838497 396453113709265958878873)
              ·
                refine ⟨297339835281949469159155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396453113709265958878873 297339835281949469159155)
                ·
                  refine ⟨446009752922924203738733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297339835281949469159155 446009752922924203738733)
                  ·
                    refine ⟨167253657346096576402025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446009752922924203738733 167253657346096576402025)
                    ·
                      refine ⟨125440243009572432301519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167253657346096576402025 125440243009572432301519)
                      ·
                        rfl

theorem cell23_244294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_244294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244294 prefixEnd_244294 := by exact prefixLift 244294
  have htrace : WordTrace (prefixWord ++ tailWord_244294) baseStart_244294 baseEnd_244294 := by
    simpa [prefixWord, tailWord_244294, baseEnd_244294] using wordTrace_append hprefix tailTrace_244294
  have hstable : (prefixWord ++ tailWord_244294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244294).length < 2 ^ (prefixWord ++ tailWord_244294).sum := by decide
  have hdescent : baseEnd_244294 < baseStart_244294 := by decide
  rcases family_descends (prefixWord ++ tailWord_244294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244319 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_244319 : Nat := 118140960795 + 244319 * 2 ^ 59
def prefixEnd_244319 : Nat := 4983230072969 + 3 ^ 40 * 244319 * 2
def baseEnd_244319 : Nat := 125453080025934834488903

theorem tailTrace_244319 : CollatzResearch.WordTrace tailWord_244319 prefixEnd_244319 125453080025934834488903 := by
  unfold tailWord_244319
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911046001881464208304011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5940697334587642805536007 8911046001881464208304011)
  ·
    refine ⟨13366569002822196312456017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8911046001881464208304011 13366569002822196312456017)
    ·
      refine ⟨10024926752116647234342013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13366569002822196312456017 10024926752116647234342013)
      ·
        refine ⟨3759347532043742712878255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10024926752116647234342013 3759347532043742712878255)
        ·
          refine ⟨5639021298065614069317383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759347532043742712878255 5639021298065614069317383)
          ·
            refine ⟨8458531947098421103976075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639021298065614069317383 8458531947098421103976075)
            ·
              refine ⟨12687797920647631655964113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458531947098421103976075 12687797920647631655964113)
              ·
                refine ⟨9515848440485723741973085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687797920647631655964113 9515848440485723741973085)
                ·
                  refine ⟨3568443165182146403239907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9515848440485723741973085 3568443165182146403239907)
                  ·
                    refine ⟨5352664747773219604859861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3568443165182146403239907 5352664747773219604859861)
                    ·
                      refine ⟨125453080025934834488903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5352664747773219604859861 125453080025934834488903)
                      ·
                        rfl

theorem cell23_244319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_244319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244319 prefixEnd_244319 := by exact prefixLift 244319
  have htrace : WordTrace (prefixWord ++ tailWord_244319) baseStart_244319 baseEnd_244319 := by
    simpa [prefixWord, tailWord_244319, baseEnd_244319] using wordTrace_append hprefix tailTrace_244319
  have hstable : (prefixWord ++ tailWord_244319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244319).length < 2 ^ (prefixWord ++ tailWord_244319).sum := by decide
  have hdescent : baseEnd_244319 < baseStart_244319 := by decide
  rcases family_descends (prefixWord ++ tailWord_244319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244330 : List Nat := [3, 1, 3, 2, 1, 1, 5, 2, 5]
def baseStart_244330 : Nat := 118140960795 + 244330 * 2 ^ 59
def prefixEnd_244330 : Nat := 4983230072969 + 3 ^ 40 * 244330 * 2
def baseEnd_244330 : Nat := 13939858701459365716817

theorem tailTrace_244330 : CollatzResearch.WordTrace tailWord_244330 prefixEnd_244330 13939858701459365716817 := by
  unfold tailWord_244330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227861801210403271738611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5940964803227742057969629 2227861801210403271738611)
  ·
    refine ⟨3341792701815604907607917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2227861801210403271738611 3341792701815604907607917)
    ·
      refine ⟨1253172263180851840352969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3341792701815604907607917 1253172263180851840352969)
      ·
        refine ⟨939879197385638880264727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253172263180851840352969 939879197385638880264727)
        ·
          refine ⟨1409818796078458320397091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939879197385638880264727 1409818796078458320397091)
          ·
            refine ⟨2114728194117687480595637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409818796078458320397091 2114728194117687480595637)
            ·
              refine ⟨198255768198533201305841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2114728194117687480595637 198255768198533201305841)
              ·
                refine ⟨148691826148899900979381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198255768198533201305841 148691826148899900979381)
                ·
                  refine ⟨13939858701459365716817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148691826148899900979381 13939858701459365716817)
                  ·
                    rfl

theorem cell23_244330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_244330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244330 prefixEnd_244330 := by exact prefixLift 244330
  have htrace : WordTrace (prefixWord ++ tailWord_244330) baseStart_244330 baseEnd_244330 := by
    simpa [prefixWord, tailWord_244330, baseEnd_244330] using wordTrace_append hprefix tailTrace_244330
  have hstable : (prefixWord ++ tailWord_244330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244330).length < 2 ^ (prefixWord ++ tailWord_244330).sum := by decide
  have hdescent : baseEnd_244330 < baseStart_244330 := by decide
  rcases family_descends (prefixWord ++ tailWord_244330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244339 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 2, 8]
def baseStart_244339 : Nat := 118140960795 + 244339 * 2 ^ 59
def prefixEnd_244339 : Nat := 4983230072969 + 3 ^ 40 * 244339 * 2
def baseEnd_244339 : Nat := 41821116546341585412937

theorem tailTrace_244339 : CollatzResearch.WordTrace tailWord_244339 prefixEnd_244339 41821116546341585412937 := by
  unfold tailWord_244339
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911775461809007624032071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5941183641206005082688047 8911775461809007624032071)
  ·
    refine ⟨13367663192713511436048107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8911775461809007624032071 13367663192713511436048107)
    ·
      refine ⟨20051494789070267154072161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13367663192713511436048107 20051494789070267154072161)
      ·
        refine ⟨15038621091802700365554121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20051494789070267154072161 15038621091802700365554121)
        ·
          refine ⟨11278965818852025274165591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15038621091802700365554121 11278965818852025274165591)
          ·
            refine ⟨16918448728278037911248387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11278965818852025274165591 16918448728278037911248387)
            ·
              refine ⟨25377673092417056866872581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16918448728278037911248387 25377673092417056866872581)
              ·
                refine ⟨4758313704828198162538609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25377673092417056866872581 4758313704828198162538609)
                ·
                  refine ⟨3568735278621148621903957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4758313704828198162538609 3568735278621148621903957)
                  ·
                    refine ⟨41821116546341585412937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3568735278621148621903957 41821116546341585412937)
                    ·
                      rfl

theorem cell23_244339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 8].length) (baseStart_244339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244339 prefixEnd_244339 := by exact prefixLift 244339
  have htrace : WordTrace (prefixWord ++ tailWord_244339) baseStart_244339 baseEnd_244339 := by
    simpa [prefixWord, tailWord_244339, baseEnd_244339] using wordTrace_append hprefix tailTrace_244339
  have hstable : (prefixWord ++ tailWord_244339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244339).length < 2 ^ (prefixWord ++ tailWord_244339).sum := by decide
  have hdescent : baseEnd_244339 < baseStart_244339 := by decide
  rcases family_descends (prefixWord ++ tailWord_244339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244341 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_244341 : Nat := 118140960795 + 244341 * 2 ^ 59
def prefixEnd_244341 : Nat := 4983230072969 + 3 ^ 40 * 244341 * 2
def baseEnd_244341 : Nat := 125464376600333748413803

theorem tailTrace_244341 : CollatzResearch.WordTrace tailWord_244341 prefixEnd_244341 125464376600333748413803 := by
  unfold tailWord_244341
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911848407801761965604877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5941232271867841310403251 8911848407801761965604877)
  ·
    refine ⟨3341943152925660737101829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8911848407801761965604877 3341943152925660737101829)
    ·
      refine ⟨626614341173561388206593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3341943152925660737101829 626614341173561388206593)
      ·
        refine ⟨469960755880171041154945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626614341173561388206593 469960755880171041154945)
        ·
          refine ⟨352470566910128280866209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469960755880171041154945 352470566910128280866209)
          ·
            refine ⟨264352925182596210649657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352470566910128280866209 264352925182596210649657)
            ·
              refine ⟨198264693886947157987243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264352925182596210649657 198264693886947157987243)
              ·
                refine ⟨297397040830420736980865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198264693886947157987243 297397040830420736980865)
                ·
                  refine ⟨223047780622815552735649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297397040830420736980865 223047780622815552735649)
                  ·
                    refine ⟨167285835467111664551737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223047780622815552735649 167285835467111664551737)
                    ·
                      refine ⟨125464376600333748413803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167285835467111664551737 125464376600333748413803)
                      ·
                        rfl

theorem cell23_244341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_244341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244341 prefixEnd_244341 := by exact prefixLift 244341
  have htrace : WordTrace (prefixWord ++ tailWord_244341) baseStart_244341 baseEnd_244341 := by
    simpa [prefixWord, tailWord_244341, baseEnd_244341] using wordTrace_append hprefix tailTrace_244341
  have hstable : (prefixWord ++ tailWord_244341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244341).length < 2 ^ (prefixWord ++ tailWord_244341).sum := by decide
  have hdescent : baseEnd_244341 < baseStart_244341 := by decide
  rcases family_descends (prefixWord ++ tailWord_244341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244376 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_244376 : Nat := 118140960795 + 244376 * 2 ^ 59
def prefixEnd_244376 : Nat := 4983230072969 + 3 ^ 40 * 244376 * 2
def baseEnd_244376 : Nat := 125482348423241111476141

theorem tailTrace_244376 : CollatzResearch.WordTrace tailWord_244376 prefixEnd_244376 125482348423241111476141 := by
  unfold tailWord_244376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456562481337481471564491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5942083308449975295419321 4456562481337481471564491)
  ·
    refine ⟨6684843722006222207346737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4456562481337481471564491 6684843722006222207346737)
    ·
      refine ⟨5013632791504666655510053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6684843722006222207346737 5013632791504666655510053)
      ·
        refine ⟨940056148407124997908135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5013632791504666655510053 940056148407124997908135)
        ·
          refine ⟨1410084222610687496862203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940056148407124997908135 1410084222610687496862203)
          ·
            refine ⟨2115126333916031245293305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410084222610687496862203 2115126333916031245293305)
            ·
              refine ⟨1586344750437023433969979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115126333916031245293305 1586344750437023433969979)
              ·
                refine ⟨2379517125655535150954969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586344750437023433969979 2379517125655535150954969)
                ·
                  refine ⟨1784637844241651363216227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2379517125655535150954969 1784637844241651363216227)
                  ·
                    refine ⟨2676956766362477044824341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1784637844241651363216227 2676956766362477044824341)
                    ·
                      refine ⟨125482348423241111476141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2676956766362477044824341 125482348423241111476141)
                      ·
                        rfl

theorem cell23_244376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_244376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244376 prefixEnd_244376 := by exact prefixLift 244376
  have htrace : WordTrace (prefixWord ++ tailWord_244376) baseStart_244376 baseEnd_244376 := by
    simpa [prefixWord, tailWord_244376, baseEnd_244376] using wordTrace_append hprefix tailTrace_244376
  have hstable : (prefixWord ++ tailWord_244376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244376).length < 2 ^ (prefixWord ++ tailWord_244376).sum := by decide
  have hdescent : baseEnd_244376 < baseStart_244376 := by decide
  rcases family_descends (prefixWord ++ tailWord_244376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244417 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_244417 : Nat := 118140960795 + 244417 * 2 ^ 59
def prefixEnd_244417 : Nat := 4983230072969 + 3 ^ 40 * 244417 * 2
def baseEnd_244417 : Nat := 125503401130075451063453

theorem tailTrace_244417 : CollatzResearch.WordTrace tailWord_244417 prefixEnd_244417 125503401130075451063453 := by
  unfold tailWord_244417
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914620355526426945371505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5943080237017617963581003 8914620355526426945371505)
  ·
    refine ⟨6685965266644820209028629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8914620355526426945371505 6685965266644820209028629)
    ·
      refine ⟨313404621873975947298217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6685965266644820209028629 313404621873975947298217)
      ·
        refine ⟨235053466405481960473663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313404621873975947298217 235053466405481960473663)
        ·
          refine ⟨352580199608222940710495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235053466405481960473663 352580199608222940710495)
          ·
            refine ⟨528870299412334411065743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352580199608222940710495 528870299412334411065743)
            ·
              refine ⟨793305449118501616598615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528870299412334411065743 793305449118501616598615)
              ·
                refine ⟨1189958173677752424897923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793305449118501616598615 1189958173677752424897923)
                ·
                  refine ⟨1784937260516628637346885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189958173677752424897923 1784937260516628637346885)
                  ·
                    refine ⟨334675736346867869502541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784937260516628637346885 334675736346867869502541)
                    ·
                      refine ⟨125503401130075451063453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334675736346867869502541 125503401130075451063453)
                      ·
                        rfl

theorem cell23_244417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_244417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244417 prefixEnd_244417 := by exact prefixLift 244417
  have htrace : WordTrace (prefixWord ++ tailWord_244417) baseStart_244417 baseEnd_244417 := by
    simpa [prefixWord, tailWord_244417, baseEnd_244417] using wordTrace_append hprefix tailTrace_244417
  have hstable : (prefixWord ++ tailWord_244417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244417).length < 2 ^ (prefixWord ++ tailWord_244417).sum := by decide
  have hdescent : baseEnd_244417 < baseStart_244417 := by decide
  rcases family_descends (prefixWord ++ tailWord_244417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244433 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 1, 5]
def baseStart_244433 : Nat := 118140960795 + 244433 * 2 ^ 59
def prefixEnd_244433 : Nat := 4983230072969 + 3 ^ 40 * 244433 * 2
def baseEnd_244433 : Nat := 41837205606849129487793

theorem tailTrace_244433 : CollatzResearch.WordTrace tailWord_244433 prefixEnd_244433 41837205606849129487793 := by
  unfold tailWord_244433
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915203923468461677953953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5943469282312307785302635 8915203923468461677953953)
  ·
    refine ⟨6686402942601346258465465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8915203923468461677953953 6686402942601346258465465)
    ·
      refine ⟨5014802206951009693849099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6686402942601346258465465 5014802206951009693849099)
      ·
        refine ⟨7522203310426514540773649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014802206951009693849099 7522203310426514540773649)
        ·
          refine ⟨5641652482819885905580237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7522203310426514540773649 5641652482819885905580237)
          ·
            refine ⟨2115619681057457214592589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5641652482819885905580237 2115619681057457214592589)
            ·
              refine ⟨793357380396546455472221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115619681057457214592589 793357380396546455472221)
              ·
                refine ⟨297509017648704920802083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 793357380396546455472221 297509017648704920802083)
                ·
                  refine ⟨446263526473057381203125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297509017648704920802083 446263526473057381203125)
                  ·
                    refine ⟨41837205606849129487793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 446263526473057381203125 41837205606849129487793)
                    ·
                      rfl

theorem cell23_244433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_244433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244433 prefixEnd_244433 := by exact prefixLift 244433
  have htrace : WordTrace (prefixWord ++ tailWord_244433) baseStart_244433 baseEnd_244433 := by
    simpa [prefixWord, tailWord_244433, baseEnd_244433] using wordTrace_append hprefix tailTrace_244433
  have hstable : (prefixWord ++ tailWord_244433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244433).length < 2 ^ (prefixWord ++ tailWord_244433).sum := by decide
  have hdescent : baseEnd_244433 < baseStart_244433 := by decide
  rcases family_descends (prefixWord ++ tailWord_244433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244437 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 6]
def baseStart_244437 : Nat := 118140960795 + 244437 * 2 ^ 59
def prefixEnd_244437 : Nat := 4983230072969 + 3 ^ 40 * 244437 * 2
def baseEnd_244437 : Nat := 13945963415907263645929

theorem tailTrace_244437 : CollatzResearch.WordTrace tailWord_244437 prefixEnd_244437 13945963415907263645929 := by
  unfold tailWord_244437
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915349815453970361099565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5943566543635980240733043 8915349815453970361099565)
  ·
    refine ⟨3343256180795238885412337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8915349815453970361099565 3343256180795238885412337)
    ·
      refine ⟨2507442135596429164059253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3343256180795238885412337 2507442135596429164059253)
      ·
        refine ⟨235072700212165234130555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2507442135596429164059253 235072700212165234130555)
        ·
          refine ⟨352609050318247851195833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235072700212165234130555 352609050318247851195833)
          ·
            refine ⟨264456787738685888396875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352609050318247851195833 264456787738685888396875)
            ·
              refine ⟨396685181608028832595313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264456787738685888396875 396685181608028832595313)
              ·
                refine ⟨297513886206021624446485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396685181608028832595313 297513886206021624446485)
                ·
                  refine ⟨13945963415907263645929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 297513886206021624446485 13945963415907263645929)
                  ·
                    rfl

theorem cell23_244437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_244437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244437 prefixEnd_244437 := by exact prefixLift 244437
  have htrace : WordTrace (prefixWord ++ tailWord_244437) baseStart_244437 baseEnd_244437 := by
    simpa [prefixWord, tailWord_244437, baseEnd_244437] using wordTrace_append hprefix tailTrace_244437
  have hstable : (prefixWord ++ tailWord_244437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244437).length < 2 ^ (prefixWord ++ tailWord_244437).sum := by decide
  have hdescent : baseEnd_244437 < baseStart_244437 := by decide
  rcases family_descends (prefixWord ++ tailWord_244437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244447 : List Nat := [1, 1, 2, 3, 2, 3, 2, 4, 1, 1, 3]
def baseStart_244447 : Nat := 118140960795 + 244447 * 2 ^ 59
def prefixEnd_244447 : Nat := 4983230072969 + 3 ^ 40 * 244447 * 2
def baseEnd_244447 : Nat := 125518805549710333688315

theorem tailTrace_244447 : CollatzResearch.WordTrace tailWord_244447 prefixEnd_244447 125518805549710333688315 := by
  unfold tailWord_244447
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915714545417742068963595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5943809696945161379309063 8915714545417742068963595)
  ·
    refine ⟨13373571818126613103445393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8915714545417742068963595 13373571818126613103445393)
    ·
      refine ⟨10030178863594959827584045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13373571818126613103445393 10030178863594959827584045)
      ·
        refine ⟨3761317073848109935344017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10030178863594959827584045 3761317073848109935344017)
        ·
          refine ⟨2820987805386082451508013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761317073848109935344017 2820987805386082451508013)
          ·
            refine ⟨1057870427019780919315505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2820987805386082451508013 1057870427019780919315505)
            ·
              refine ⟨793402820264835689486629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057870427019780919315505 793402820264835689486629)
              ·
                refine ⟨148763028799656691778743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793402820264835689486629 148763028799656691778743)
                ·
                  refine ⟨223144543199485037668115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148763028799656691778743 223144543199485037668115)
                  ·
                    refine ⟨334716814799227556502173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223144543199485037668115 334716814799227556502173)
                    ·
                      refine ⟨125518805549710333688315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334716814799227556502173 125518805549710333688315)
                      ·
                        rfl

theorem cell23_244447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_244447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244447 prefixEnd_244447 := by exact prefixLift 244447
  have htrace : WordTrace (prefixWord ++ tailWord_244447) baseStart_244447 baseEnd_244447 := by
    simpa [prefixWord, tailWord_244447, baseEnd_244447] using wordTrace_append hprefix tailTrace_244447
  have hstable : (prefixWord ++ tailWord_244447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244447).length < 2 ^ (prefixWord ++ tailWord_244447).sum := by decide
  have hdescent : baseEnd_244447 < baseStart_244447 := by decide
  rcases family_descends (prefixWord ++ tailWord_244447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244463 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 1, 6]
def baseStart_244463 : Nat := 118140960795 + 244463 * 2 ^ 59
def prefixEnd_244463 : Nat := 4983230072969 + 3 ^ 40 * 244463 * 2
def baseEnd_244463 : Nat := 41842340413394090362747

theorem tailTrace_244463 : CollatzResearch.WordTrace tailWord_244463 prefixEnd_244463 41842340413394090362747 := by
  unfold tailWord_244463
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916298113359776801546043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5944198742239851201030695 8916298113359776801546043)
  ·
    refine ⟨13374447170039665202319065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8916298113359776801546043 13374447170039665202319065)
    ·
      refine ⟨10030835377529748901739299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13374447170039665202319065 10030835377529748901739299)
      ·
        refine ⟨15046253066294623352608949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10030835377529748901739299 15046253066294623352608949)
        ·
          refine ⟨1410586224965120939307089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15046253066294623352608949 1410586224965120939307089)
          ·
            refine ⟨1057939668723840704480317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410586224965120939307089 1057939668723840704480317)
            ·
              refine ⟨396727375771440264180119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057939668723840704480317 396727375771440264180119)
              ·
                refine ⟨595091063657160396270179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396727375771440264180119 595091063657160396270179)
                ·
                  refine ⟨892636595485740594405269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595091063657160396270179 892636595485740594405269)
                  ·
                    refine ⟨41842340413394090362747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 892636595485740594405269 41842340413394090362747)
                    ·
                      rfl

theorem cell23_244463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_244463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244463 prefixEnd_244463 := by exact prefixLift 244463
  have htrace : WordTrace (prefixWord ++ tailWord_244463) baseStart_244463 baseEnd_244463 := by
    simpa [prefixWord, tailWord_244463, baseEnd_244463] using wordTrace_append hprefix tailTrace_244463
  have hstable : (prefixWord ++ tailWord_244463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244463).length < 2 ^ (prefixWord ++ tailWord_244463).sum := by decide
  have hdescent : baseEnd_244463 < baseStart_244463 := by decide
  rcases family_descends (prefixWord ++ tailWord_244463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244470 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_244470 : Nat := 118140960795 + 244470 * 2 ^ 59
def prefixEnd_244470 : Nat := 4983230072969 + 3 ^ 40 * 244470 * 2
def baseEnd_244470 : Nat := 125530615604763743700709

theorem tailTrace_244470 : CollatzResearch.WordTrace tailWord_244470 prefixEnd_244470 125530615604763743700709 := by
  unfold tailWord_244470
  simp only [CollatzResearch.WordTrace]
  refine ⟨557284589020901062315679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5944368949556277998033909 557284589020901062315679)
  ·
    refine ⟨835926883531351593473519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 557284589020901062315679 835926883531351593473519)
    ·
      refine ⟨1253890325297027390210279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835926883531351593473519 1253890325297027390210279)
      ·
        refine ⟨1880835487945541085315419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1253890325297027390210279 1880835487945541085315419)
        ·
          refine ⟨2821253231918311627973129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880835487945541085315419 2821253231918311627973129)
          ·
            refine ⟨2115939923938733720979847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821253231918311627973129 2115939923938733720979847)
            ·
              refine ⟨3173909885908100581469771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115939923938733720979847 3173909885908100581469771)
              ·
                refine ⟨4760864828862150872204657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173909885908100581469771 4760864828862150872204657)
                ·
                  refine ⟨3570648621646613154153493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4760864828862150872204657 3570648621646613154153493)
                  ·
                    refine ⟨167374154139684991600945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3570648621646613154153493 167374154139684991600945)
                    ·
                      refine ⟨125530615604763743700709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167374154139684991600945 125530615604763743700709)
                      ·
                        rfl

theorem cell23_244470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_244470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244470 prefixEnd_244470 := by exact prefixLift 244470
  have htrace : WordTrace (prefixWord ++ tailWord_244470) baseStart_244470 baseEnd_244470 := by
    simpa [prefixWord, tailWord_244470, baseEnd_244470] using wordTrace_append hprefix tailTrace_244470
  have hstable : (prefixWord ++ tailWord_244470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244470).length < 2 ^ (prefixWord ++ tailWord_244470).sum := by decide
  have hdescent : baseEnd_244470 < baseStart_244470 := by decide
  rcases family_descends (prefixWord ++ tailWord_244470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244473 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 3]
def baseStart_244473 : Nat := 118140960795 + 244473 * 2 ^ 59
def prefixEnd_244473 : Nat := 4983230072969 + 3 ^ 40 * 244473 * 2
def baseEnd_244473 : Nat := 125532156046727231963195

theorem tailTrace_244473 : CollatzResearch.WordTrace tailWord_244473 prefixEnd_244473 125532156046727231963195 := by
  unfold tailWord_244473
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916662843323548509410073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5944441895549032339606715 8916662843323548509410073)
  ·
    refine ⟨6687497132492661382057555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8916662843323548509410073 6687497132492661382057555)
    ·
      refine ⟨10031245698738992073086333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6687497132492661382057555 10031245698738992073086333)
      ·
        refine ⟨3761717137027122027407375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10031245698738992073086333 3761717137027122027407375)
        ·
          refine ⟨5642575705540683041111063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761717137027122027407375 5642575705540683041111063)
          ·
            refine ⟨8463863558311024561666595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642575705540683041111063 8463863558311024561666595)
            ·
              refine ⟨12695795337466536842499893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463863558311024561666595 12695795337466536842499893)
              ·
                refine ⟨1190230812887487828984365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12695795337466536842499893 1190230812887487828984365)
                ·
                  refine ⟨446336554832807935869137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190230812887487828984365 446336554832807935869137)
                  ·
                    refine ⟨334752416124605951901853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446336554832807935869137 334752416124605951901853)
                    ·
                      refine ⟨125532156046727231963195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334752416124605951901853 125532156046727231963195)
                      ·
                        rfl

theorem cell23_244473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_244473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244473 prefixEnd_244473 := by exact prefixLift 244473
  have htrace : WordTrace (prefixWord ++ tailWord_244473) baseStart_244473 baseEnd_244473 := by
    simpa [prefixWord, tailWord_244473, baseEnd_244473] using wordTrace_append hprefix tailTrace_244473
  have hstable : (prefixWord ++ tailWord_244473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244473).length < 2 ^ (prefixWord ++ tailWord_244473).sum := by decide
  have hdescent : baseEnd_244473 < baseStart_244473 := by decide
  rcases family_descends (prefixWord ++ tailWord_244473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244490 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_244490 : Nat := 118140960795 + 244490 * 2 ^ 59
def prefixEnd_244490 : Nat := 4983230072969 + 3 ^ 40 * 244490 * 2
def baseEnd_244490 : Nat := 125540885217853665450617

theorem tailTrace_244490 : CollatzResearch.WordTrace tailWord_244490 prefixEnd_244490 125540885217853665450617 := by
  unfold tailWord_244490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229320721065490103194731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5944855256174640275185949 2229320721065490103194731)
  ·
    refine ⟨3343981081598235154792097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229320721065490103194731 3343981081598235154792097)
    ·
      refine ⟨2507985811198676366094073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3343981081598235154792097 2507985811198676366094073)
      ·
        refine ⟨1880989358399007274570555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2507985811198676366094073 1880989358399007274570555)
        ·
          refine ⟨2821484037598510911855833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880989358399007274570555 2821484037598510911855833)
          ·
            refine ⟨2116113028198883183891875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821484037598510911855833 2116113028198883183891875)
            ·
              refine ⟨3174169542298324775837813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116113028198883183891875 3174169542298324775837813)
              ·
                refine ⟨297578394590467947734795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3174169542298324775837813 297578394590467947734795)
                ·
                  refine ⟨446367591885701921602193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297578394590467947734795 446367591885701921602193)
                  ·
                    refine ⟨334775693914276441201645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446367591885701921602193 334775693914276441201645)
                    ·
                      refine ⟨125540885217853665450617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334775693914276441201645 125540885217853665450617)
                      ·
                        rfl

theorem cell23_244490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_244490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244490 prefixEnd_244490 := by exact prefixLift 244490
  have htrace : WordTrace (prefixWord ++ tailWord_244490) baseStart_244490 baseEnd_244490 := by
    simpa [prefixWord, tailWord_244490, baseEnd_244490] using wordTrace_append hprefix tailTrace_244490
  have hstable : (prefixWord ++ tailWord_244490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244490).length < 2 ^ (prefixWord ++ tailWord_244490).sum := by decide
  have hdescent : baseEnd_244490 < baseStart_244490 := by decide
  rcases family_descends (prefixWord ++ tailWord_244490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244498 : List Nat := [3, 2, 4, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_244498 : Nat := 118140960795 + 244498 * 2 ^ 59
def prefixEnd_244498 : Nat := 4983230072969 + 3 ^ 40 * 244498 * 2
def baseEnd_244498 : Nat := 125544993063089634150581

theorem tailTrace_244498 : CollatzResearch.WordTrace tailWord_244498 prefixEnd_244498 125544993063089634150581 := by
  unfold tailWord_244498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229393667058244444767537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5945049778821985186046765 2229393667058244444767537)
  ·
    refine ⟨1672045250293683333575653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2229393667058244444767537 1672045250293683333575653)
    ·
      refine ⟨313508484430065625045435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1672045250293683333575653 313508484430065625045435)
      ·
        refine ⟨470262726645098437568153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313508484430065625045435 470262726645098437568153)
        ·
          refine ⟨352697044983823828176115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470262726645098437568153 352697044983823828176115)
          ·
            refine ⟨529045567475735742264173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352697044983823828176115 529045567475735742264173)
            ·
              refine ⟨198392087803400903349065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529045567475735742264173 198392087803400903349065)
              ·
                refine ⟨148794065852550677511799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198392087803400903349065 148794065852550677511799)
                ·
                  refine ⟨223191098778826016267699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148794065852550677511799 223191098778826016267699)
                  ·
                    refine ⟨334786648168239024401549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223191098778826016267699 334786648168239024401549)
                    ·
                      refine ⟨125544993063089634150581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334786648168239024401549 125544993063089634150581)
                      ·
                        rfl

theorem cell23_244498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_244498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244498 prefixEnd_244498 := by exact prefixLift 244498
  have htrace : WordTrace (prefixWord ++ tailWord_244498) baseStart_244498 baseEnd_244498 := by
    simpa [prefixWord, tailWord_244498, baseEnd_244498] using wordTrace_append hprefix tailTrace_244498
  have hstable : (prefixWord ++ tailWord_244498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244498).length < 2 ^ (prefixWord ++ tailWord_244498).sum := by decide
  have hdescent : baseEnd_244498 < baseStart_244498 := by decide
  rcases family_descends (prefixWord ++ tailWord_244498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244514 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_244514 : Nat := 118140960795 + 244514 * 2 ^ 59
def prefixEnd_244514 : Nat := 4983230072969 + 3 ^ 40 * 244514 * 2
def baseEnd_244514 : Nat := 41851069584520523850169

theorem tailTrace_244514 : CollatzResearch.WordTrace tailWord_244514 prefixEnd_244514 41851069584520523850169 := by
  unfold tailWord_244514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229539559043753127913149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5945438824116675007768397 2229539559043753127913149)
  ·
    refine ⟨836077334641407422967431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2229539559043753127913149 836077334641407422967431)
    ·
      refine ⟨1254116001962111134451147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836077334641407422967431 1254116001962111134451147)
      ·
        refine ⟨1881174002943166701676721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254116001962111134451147 1881174002943166701676721)
        ·
          refine ⟨1410880502207375026257541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881174002943166701676721 1410880502207375026257541)
          ·
            refine ⟨264540094163882817423289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1410880502207375026257541 264540094163882817423289)
            ·
              refine ⟨198405070622912113067467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264540094163882817423289 198405070622912113067467)
              ·
                refine ⟨297607605934368169601201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198405070622912113067467 297607605934368169601201)
                ·
                  refine ⟨223205704450776127200901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297607605934368169601201 223205704450776127200901)
                  ·
                    refine ⟨41851069584520523850169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223205704450776127200901 41851069584520523850169)
                    ·
                      rfl

theorem cell23_244514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_244514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244514 prefixEnd_244514 := by exact prefixLift 244514
  have htrace : WordTrace (prefixWord ++ tailWord_244514) baseStart_244514 baseEnd_244514 := by
    simpa [prefixWord, tailWord_244514, baseEnd_244514] using wordTrace_append hprefix tailTrace_244514
  have hstable : (prefixWord ++ tailWord_244514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244514).length < 2 ^ (prefixWord ++ tailWord_244514).sum := by decide
  have hdescent : baseEnd_244514 < baseStart_244514 := by decide
  rcases family_descends (prefixWord ++ tailWord_244514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244520 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_244520 : Nat := 118140960795 + 244520 * 2 ^ 59
def prefixEnd_244520 : Nat := 4983230072969 + 3 ^ 40 * 244520 * 2
def baseEnd_244520 : Nat := 125556289637488548075479

theorem tailTrace_244520 : CollatzResearch.WordTrace tailWord_244520 prefixEnd_244520 125556289637488548075479 := by
  unfold tailWord_244520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459188537076637768185507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5945584716102183690914009 4459188537076637768185507)
  ·
    refine ⟨6688782805614956652278261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459188537076637768185507 6688782805614956652278261)
    ·
      refine ⟨627073388026402186151087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6688782805614956652278261 627073388026402186151087)
      ·
        refine ⟨940610082039603279226631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627073388026402186151087 940610082039603279226631)
        ·
          refine ⟨1410915123059404918839947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940610082039603279226631 1410915123059404918839947)
          ·
            refine ⟨2116372684589107378259921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410915123059404918839947 2116372684589107378259921)
            ·
              refine ⟨1587279513441830533694941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116372684589107378259921 1587279513441830533694941)
              ·
                refine ⟨595229817540686450135603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587279513441830533694941 595229817540686450135603)
                ·
                  refine ⟨892844726311029675203405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595229817540686450135603 892844726311029675203405)
                  ·
                    refine ⟨334816772366636128201277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892844726311029675203405 334816772366636128201277)
                    ·
                      refine ⟨125556289637488548075479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 334816772366636128201277 125556289637488548075479)
                      ·
                        rfl

theorem cell23_244520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_244520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244520 prefixEnd_244520 := by exact prefixLift 244520
  have htrace : WordTrace (prefixWord ++ tailWord_244520) baseStart_244520 baseEnd_244520 := by
    simpa [prefixWord, tailWord_244520, baseEnd_244520] using wordTrace_append hprefix tailTrace_244520
  have hstable : (prefixWord ++ tailWord_244520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244520).length < 2 ^ (prefixWord ++ tailWord_244520).sum := by decide
  have hdescent : baseEnd_244520 < baseStart_244520 := by decide
  rcases family_descends (prefixWord ++ tailWord_244520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244583 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 9]
def baseStart_244583 : Nat := 118140960795 + 244583 * 2 ^ 59
def prefixEnd_244583 : Nat := 4983230072969 + 3 ^ 40 * 244583 * 2
def baseEnd_244583 : Nat := 13954293213191311287521

theorem tailTrace_244583 : CollatzResearch.WordTrace tailWord_244583 prefixEnd_244583 13954293213191311287521 := by
  unfold tailWord_244583
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920674872925037295914403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5947116581950024863942935 8920674872925037295914403)
  ·
    refine ⟨13381012309387555943871605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8920674872925037295914403 13381012309387555943871605)
    ·
      refine ⟨1254469904005083369737963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13381012309387555943871605 1254469904005083369737963)
      ·
        refine ⟨1881704856007625054606945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254469904005083369737963 1881704856007625054606945)
        ·
          refine ⟨1411278642005718790955209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881704856007625054606945 1411278642005718790955209)
          ·
            refine ⟨1058458981504289093216407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411278642005718790955209 1058458981504289093216407)
            ·
              refine ⟨1587688472256433639824611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058458981504289093216407 1587688472256433639824611)
              ·
                refine ⟨2381532708384650459736917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587688472256433639824611 2381532708384650459736917)
                ·
                  refine ⟨13954293213191311287521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2381532708384650459736917 13954293213191311287521)
                  ·
                    rfl

theorem cell23_244583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 9].length) (baseStart_244583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244583 prefixEnd_244583 := by exact prefixLift 244583
  have htrace : WordTrace (prefixWord ++ tailWord_244583) baseStart_244583 baseEnd_244583 := by
    simpa [prefixWord, tailWord_244583, baseEnd_244583] using wordTrace_append hprefix tailTrace_244583
  have hstable : (prefixWord ++ tailWord_244583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244583).length < 2 ^ (prefixWord ++ tailWord_244583).sum := by decide
  have hdescent : baseEnd_244583 < baseStart_244583 := by decide
  rcases family_descends (prefixWord ++ tailWord_244583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244598 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_244598 : Nat := 118140960795 + 244598 * 2 ^ 59
def prefixEnd_244598 : Nat := 4983230072969 + 3 ^ 40 * 244598 * 2
def baseEnd_244598 : Nat := 125596341128539242900121

theorem tailTrace_244598 : CollatzResearch.WordTrace tailWord_244598 prefixEnd_244598 125596341128539242900121 := by
  unfold tailWord_244598
  simp only [CollatzResearch.WordTrace]
  refine ⟨557576372991918428606903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5947481311913796571806965 557576372991918428606903)
  ·
    refine ⟨836364559487877642910355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 557576372991918428606903 836364559487877642910355)
    ·
      refine ⟨1254546839231816464365533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836364559487877642910355 1254546839231816464365533)
      ·
        refine ⟨470455064711931174137075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1254546839231816464365533 470455064711931174137075)
        ·
          refine ⟨705682597067896761205613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470455064711931174137075 705682597067896761205613)
          ·
            refine ⟨264630973900461285452105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705682597067896761205613 264630973900461285452105)
            ·
              refine ⟨198473230425345964089079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264630973900461285452105 198473230425345964089079)
              ·
                refine ⟨297709845638018946133619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198473230425345964089079 297709845638018946133619)
                ·
                  refine ⟨446564768457028419200429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297709845638018946133619 446564768457028419200429)
                  ·
                    refine ⟨167461788171385657200161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446564768457028419200429 167461788171385657200161)
                    ·
                      refine ⟨125596341128539242900121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167461788171385657200161 125596341128539242900121)
                      ·
                        rfl

theorem cell23_244598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_244598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244598 prefixEnd_244598 := by exact prefixLift 244598
  have htrace : WordTrace (prefixWord ++ tailWord_244598) baseStart_244598 baseEnd_244598 := by
    simpa [prefixWord, tailWord_244598, baseEnd_244598] using wordTrace_append hprefix tailTrace_244598
  have hstable : (prefixWord ++ tailWord_244598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244598).length < 2 ^ (prefixWord ++ tailWord_244598).sum := by decide
  have hdescent : baseEnd_244598 < baseStart_244598 := by decide
  rcases family_descends (prefixWord ++ tailWord_244598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244620 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 7, 2]
def baseStart_244620 : Nat := 118140960795 + 244620 * 2 ^ 59
def prefixEnd_244620 : Nat := 4983230072969 + 3 ^ 40 * 244620 * 2
def baseEnd_244620 : Nat := 125607637702938156825019

theorem tailTrace_244620 : CollatzResearch.WordTrace tailWord_244620 prefixEnd_244620 125607637702938156825019 := by
  unfold tailWord_244620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461012186895496307505657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5948016249193995076674209 4461012186895496307505657)
  ·
    refine ⟨3345759140171622230629243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4461012186895496307505657 3345759140171622230629243)
    ·
      refine ⟨5018638710257433345943865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345759140171622230629243 5018638710257433345943865)
      ·
        refine ⟨3763979032693075009457899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5018638710257433345943865 3763979032693075009457899)
        ·
          refine ⟨5645968549039612514186849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763979032693075009457899 5645968549039612514186849)
          ·
            refine ⟨4234476411779709385640137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645968549039612514186849 4234476411779709385640137)
            ·
              refine ⟨3175857308834782039230103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234476411779709385640137 3175857308834782039230103)
              ·
                refine ⟨4763785963252173058845155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175857308834782039230103 4763785963252173058845155)
                ·
                  refine ⟨7145678944878259588267733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763785963252173058845155 7145678944878259588267733)
                  ·
                    refine ⟨167476850270584209100025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7145678944878259588267733 167476850270584209100025)
                    ·
                      refine ⟨125607637702938156825019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167476850270584209100025 125607637702938156825019)
                      ·
                        rfl

theorem cell23_244620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_244620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244620 prefixEnd_244620 := by exact prefixLift 244620
  have htrace : WordTrace (prefixWord ++ tailWord_244620) baseStart_244620 baseEnd_244620 := by
    simpa [prefixWord, tailWord_244620, baseEnd_244620] using wordTrace_append hprefix tailTrace_244620
  have hstable : (prefixWord ++ tailWord_244620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244620).length < 2 ^ (prefixWord ++ tailWord_244620).sum := by decide
  have hdescent : baseEnd_244620 < baseStart_244620 := by decide
  rcases family_descends (prefixWord ++ tailWord_244620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244663 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_244663 : Nat := 118140960795 + 244663 * 2 ^ 59
def prefixEnd_244663 : Nat := 4983230072969 + 3 ^ 40 * 244663 * 2
def baseEnd_244663 : Nat := 125629717371081488587321

theorem tailTrace_244663 : CollatzResearch.WordTrace tailWord_244663 prefixEnd_244663 125629717371081488587321 := by
  unfold tailWord_244663
  simp only [CollatzResearch.WordTrace]
  refine ⟨8923592712635210958826643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5949061808423473972551095 8923592712635210958826643)
  ·
    refine ⟨13385389068952816438239965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8923592712635210958826643 13385389068952816438239965)
    ·
      refine ⟨5019520900857306164339987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13385389068952816438239965 5019520900857306164339987)
      ·
        refine ⟨7529281351285959246509981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019520900857306164339987 7529281351285959246509981)
        ·
          refine ⟨2823480506732234717441243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7529281351285959246509981 2823480506732234717441243)
          ·
            refine ⟨4235220760098352076161865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823480506732234717441243 4235220760098352076161865)
            ·
              refine ⟨3176415570073764057121399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4235220760098352076161865 3176415570073764057121399)
              ·
                refine ⟨4764623355110646085682099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176415570073764057121399 4764623355110646085682099)
                ·
                  refine ⟨7146935032665969128523149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764623355110646085682099 7146935032665969128523149)
                  ·
                    refine ⟨2680100637249738423196181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7146935032665969128523149 2680100637249738423196181)
                    ·
                      refine ⟨125629717371081488587321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2680100637249738423196181 125629717371081488587321)
                      ·
                        rfl

theorem cell23_244663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_244663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244663 prefixEnd_244663 := by exact prefixLift 244663
  have htrace : WordTrace (prefixWord ++ tailWord_244663) baseStart_244663 baseEnd_244663 := by
    simpa [prefixWord, tailWord_244663, baseEnd_244663] using wordTrace_append hprefix tailTrace_244663
  have hstable : (prefixWord ++ tailWord_244663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244663).length < 2 ^ (prefixWord ++ tailWord_244663).sum := by decide
  have hdescent : baseEnd_244663 < baseStart_244663 := by decide
  rcases family_descends (prefixWord ++ tailWord_244663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244713 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_244713 : Nat := 118140960795 + 244713 * 2 ^ 59
def prefixEnd_244713 : Nat := 4983230072969 + 3 ^ 40 * 244713 * 2
def baseEnd_244713 : Nat := 125655391403806292962091

theorem tailTrace_244713 : CollatzResearch.WordTrace tailWord_244713 prefixEnd_244713 125655391403806292962091 := by
  unfold tailWord_244713
  simp only [CollatzResearch.WordTrace]
  refine ⟨8925416362454069498146793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5950277574969379665431195 8925416362454069498146793)
  ·
    refine ⟨6694062271840552123610095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8925416362454069498146793 6694062271840552123610095)
    ·
      refine ⟨10041093407760828185415143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6694062271840552123610095 10041093407760828185415143)
      ·
        refine ⟨15061640111641242278122715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10041093407760828185415143 15061640111641242278122715)
        ·
          refine ⟨22592460167461863417184073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15061640111641242278122715 22592460167461863417184073)
          ·
            refine ⟨16944345125596397562888055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22592460167461863417184073 16944345125596397562888055)
            ·
              refine ⟨25416517688394596344332083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16944345125596397562888055 25416517688394596344332083)
              ·
                refine ⟨38124776532591894516498125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25416517688394596344332083 38124776532591894516498125)
                ·
                  refine ⟨14296791199721960443686797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38124776532591894516498125 14296791199721960443686797)
                  ·
                    refine ⟨5361296699895735166382549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14296791199721960443686797 5361296699895735166382549)
                    ·
                      refine ⟨125655391403806292962091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5361296699895735166382549 125655391403806292962091)
                      ·
                        rfl

theorem cell23_244713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_244713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244713 prefixEnd_244713 := by exact prefixLift 244713
  have htrace : WordTrace (prefixWord ++ tailWord_244713) baseStart_244713 baseEnd_244713 := by
    simpa [prefixWord, tailWord_244713, baseEnd_244713] using wordTrace_append hprefix tailTrace_244713
  have hstable : (prefixWord ++ tailWord_244713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244713).length < 2 ^ (prefixWord ++ tailWord_244713).sum := by decide
  have hdescent : baseEnd_244713 < baseStart_244713 := by decide
  rcases family_descends (prefixWord ++ tailWord_244713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244757 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_244757 : Nat := 118140960795 + 244757 * 2 ^ 59
def prefixEnd_244757 : Nat := 4983230072969 + 3 ^ 40 * 244757 * 2
def baseEnd_244757 : Nat := 125677984552604120811889

theorem tailTrace_244757 : CollatzResearch.WordTrace tailWord_244757 prefixEnd_244757 125677984552604120811889 := by
  unfold tailWord_244757
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927021174294665012748525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5951347449529776675165683 8927021174294665012748525)
  ·
    refine ⟨3347632940360499379780697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8927021174294665012748525 3347632940360499379780697)
    ·
      refine ⟨2510724705270374534835523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3347632940360499379780697 2510724705270374534835523)
      ·
        refine ⟨3766087057905561802253285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2510724705270374534835523 3766087057905561802253285)
        ·
          refine ⟨706141323357292837922491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3766087057905561802253285 706141323357292837922491)
          ·
            refine ⟨1059211985035939256883737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706141323357292837922491 1059211985035939256883737)
            ·
              refine ⟨794408988776954442662803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059211985035939256883737 794408988776954442662803)
              ·
                refine ⟨1191613483165431663994205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794408988776954442662803 1191613483165431663994205)
                ·
                  refine ⟨446855056187036873997827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191613483165431663994205 446855056187036873997827)
                  ·
                    refine ⟨670282584280555310996741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446855056187036873997827 670282584280555310996741)
                    ·
                      refine ⟨125677984552604120811889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 670282584280555310996741 125677984552604120811889)
                      ·
                        rfl

theorem cell23_244757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_244757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244757 prefixEnd_244757 := by exact prefixLift 244757
  have htrace : WordTrace (prefixWord ++ tailWord_244757) baseStart_244757 baseEnd_244757 := by
    simpa [prefixWord, tailWord_244757, baseEnd_244757] using wordTrace_append hprefix tailTrace_244757
  have hstable : (prefixWord ++ tailWord_244757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244757).length < 2 ^ (prefixWord ++ tailWord_244757).sum := by decide
  have hdescent : baseEnd_244757 < baseStart_244757 := by decide
  rcases family_descends (prefixWord ++ tailWord_244757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244801 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 1, 6]
def baseStart_244801 : Nat := 118140960795 + 244801 * 2 ^ 59
def prefixEnd_244801 : Nat := 4983230072969 + 3 ^ 40 * 244801 * 2
def baseEnd_244801 : Nat := 41900192567133982887229

theorem tailTrace_244801 : CollatzResearch.WordTrace tailWord_244801 prefixEnd_244801 41900192567133982887229 := by
  unfold tailWord_244801
  simp only [CollatzResearch.WordTrace]
  refine ⟨8928625986135260527350257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5952417324090173684900171 8928625986135260527350257)
  ·
    refine ⟨6696469489601445395512693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8928625986135260527350257 6696469489601445395512693)
    ·
      refine ⟨627794014650135505829315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6696469489601445395512693 627794014650135505829315)
      ·
        refine ⟨941691021975203258743973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627794014650135505829315 941691021975203258743973)
        ·
          refine ⟨176567066620350611014495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 941691021975203258743973 176567066620350611014495)
          ·
            refine ⟨264850599930525916521743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176567066620350611014495 264850599930525916521743)
            ·
              refine ⟨397275899895788874782615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264850599930525916521743 397275899895788874782615)
              ·
                refine ⟨595913849843683312173923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397275899895788874782615 595913849843683312173923)
                ·
                  refine ⟨893870774765524968260885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595913849843683312173923 893870774765524968260885)
                  ·
                    refine ⟨41900192567133982887229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 893870774765524968260885 41900192567133982887229)
                    ·
                      rfl

theorem cell23_244801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_244801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244801 prefixEnd_244801 := by exact prefixLift 244801
  have htrace : WordTrace (prefixWord ++ tailWord_244801) baseStart_244801 baseEnd_244801 := by
    simpa [prefixWord, tailWord_244801, baseEnd_244801] using wordTrace_append hprefix tailTrace_244801
  have hstable : (prefixWord ++ tailWord_244801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244801).length < 2 ^ (prefixWord ++ tailWord_244801).sum := by decide
  have hdescent : baseEnd_244801 < baseStart_244801 := by decide
  rcases family_descends (prefixWord ++ tailWord_244801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244810 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_244810 : Nat := 118140960795 + 244810 * 2 ^ 59
def prefixEnd_244810 : Nat := 4983230072969 + 3 ^ 40 * 244810 * 2
def baseEnd_244810 : Nat := 41901733009097471149715

theorem tailTrace_244810 : CollatzResearch.WordTrace tailWord_244810 prefixEnd_244810 41901733009097471149715 := by
  unfold tailWord_244810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232238560775663766106971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5952636162068436709618589 2232238560775663766106971)
  ·
    refine ⟨3348357841163495649160457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2232238560775663766106971 3348357841163495649160457)
    ·
      refine ⟨2511268380872621736870343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3348357841163495649160457 2511268380872621736870343)
      ·
        refine ⟨3766902571308932605305515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511268380872621736870343 3766902571308932605305515)
        ·
          refine ⟨5650353856963398907958273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766902571308932605305515 5650353856963398907958273)
          ·
            refine ⟨4237765392722549180968705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5650353856963398907958273 4237765392722549180968705)
            ·
              refine ⟨3178324044541911885726529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237765392722549180968705 3178324044541911885726529)
              ·
                refine ⟨2383743033406433914294897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178324044541911885726529 2383743033406433914294897)
                ·
                  refine ⟨1787807275054825435721173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383743033406433914294897 1787807275054825435721173)
                  ·
                    refine ⟨41901733009097471149715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1787807275054825435721173 41901733009097471149715)
                    ·
                      rfl

theorem cell23_244810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_244810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244810 prefixEnd_244810 := by exact prefixLift 244810
  have htrace : WordTrace (prefixWord ++ tailWord_244810) baseStart_244810 baseEnd_244810 := by
    simpa [prefixWord, tailWord_244810, baseEnd_244810] using wordTrace_append hprefix tailTrace_244810
  have hstable : (prefixWord ++ tailWord_244810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244810).length < 2 ^ (prefixWord ++ tailWord_244810).sum := by decide
  have hdescent : baseEnd_244810 < baseStart_244810 := by decide
  rcases family_descends (prefixWord ++ tailWord_244810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244862 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_244862 : Nat := 118140960795 + 244862 * 2 ^ 59
def prefixEnd_244862 : Nat := 4983230072969 + 3 ^ 40 * 244862 * 2
def baseEnd_244862 : Nat := 125731900021326209998907

theorem tailTrace_244862 : CollatzResearch.WordTrace tailWord_244862 prefixEnd_244862 125731900021326209998907 := by
  unfold tailWord_244862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116356354864283493165105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5953900559276178630213893 1116356354864283493165105)
  ·
    refine ⟨837267266148212619873829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1116356354864283493165105 837267266148212619873829)
    ·
      refine ⟨156987612402789866226343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 837267266148212619873829 156987612402789866226343)
      ·
        refine ⟨235481418604184799339515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156987612402789866226343 235481418604184799339515)
        ·
          refine ⟨353222127906277199009273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235481418604184799339515 353222127906277199009273)
          ·
            refine ⟨264916595929707899256955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353222127906277199009273 264916595929707899256955)
            ·
              refine ⟨397374893894561848885433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264916595929707899256955 397374893894561848885433)
              ·
                refine ⟨298031170420921386664075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397374893894561848885433 298031170420921386664075)
                ·
                  refine ⟨447046755631382079996113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298031170420921386664075 447046755631382079996113)
                  ·
                    refine ⟨335285066723536559997085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 447046755631382079996113 335285066723536559997085)
                    ·
                      refine ⟨125731900021326209998907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 335285066723536559997085 125731900021326209998907)
                      ·
                        rfl

theorem cell23_244862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_244862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244862 prefixEnd_244862 := by exact prefixLift 244862
  have htrace : WordTrace (prefixWord ++ tailWord_244862) baseStart_244862 baseEnd_244862 := by
    simpa [prefixWord, tailWord_244862, baseEnd_244862] using wordTrace_append hprefix tailTrace_244862
  have hstable : (prefixWord ++ tailWord_244862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244862).length < 2 ^ (prefixWord ++ tailWord_244862).sum := by decide
  have hdescent : baseEnd_244862 < baseStart_244862 := by decide
  rcases family_descends (prefixWord ++ tailWord_244862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244868 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_244868 : Nat := 118140960795 + 244868 * 2 ^ 59
def prefixEnd_244868 : Nat := 4983230072969 + 3 ^ 40 * 244868 * 2
def baseEnd_244868 : Nat := 125734980905253186523879

theorem tailTrace_244868 : CollatzResearch.WordTrace tailWord_244868 prefixEnd_244868 125734980905253186523879 := by
  unfold tailWord_244868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465534838446265485019629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5954046451261687313359505 4465534838446265485019629)
  ·
    refine ⟨1674575564417349556882361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4465534838446265485019629 1674575564417349556882361)
    ·
      refine ⟨1255931673313012167661771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1674575564417349556882361 1255931673313012167661771)
      ·
        refine ⟨1883897509969518251492657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255931673313012167661771 1883897509969518251492657)
        ·
          refine ⟨1412923132477138688619493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1883897509969518251492657 1412923132477138688619493)
          ·
            refine ⟨264923087339463504116155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1412923132477138688619493 264923087339463504116155)
            ·
              refine ⟨397384631009195256174233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264923087339463504116155 397384631009195256174233)
              ·
                refine ⟨298038473256896442130675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397384631009195256174233 298038473256896442130675)
                ·
                  refine ⟨447057709885344663196013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298038473256896442130675 447057709885344663196013)
                  ·
                    refine ⟨167646641207004248698505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447057709885344663196013 167646641207004248698505)
                    ·
                      refine ⟨125734980905253186523879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167646641207004248698505 125734980905253186523879)
                      ·
                        rfl

theorem cell23_244868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_244868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244868 prefixEnd_244868 := by exact prefixLift 244868
  have htrace : WordTrace (prefixWord ++ tailWord_244868) baseStart_244868 baseEnd_244868 := by
    simpa [prefixWord, tailWord_244868, baseEnd_244868] using wordTrace_append hprefix tailTrace_244868
  have hstable : (prefixWord ++ tailWord_244868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244868).length < 2 ^ (prefixWord ++ tailWord_244868).sum := by decide
  have hdescent : baseEnd_244868 < baseStart_244868 := by decide
  rcases family_descends (prefixWord ++ tailWord_244868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244880 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_244880 : Nat := 118140960795 + 244880 * 2 ^ 59
def prefixEnd_244880 : Nat := 4983230072969 + 3 ^ 40 * 244880 * 2
def baseEnd_244880 : Nat := 125741142673107139573823

theorem tailTrace_244880 : CollatzResearch.WordTrace tailWord_244880 prefixEnd_244880 125741142673107139573823 := by
  unfold tailWord_244880
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465753676424528509738047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5954338235232704679650729 4465753676424528509738047)
  ·
    refine ⟨6698630514636792764607071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4465753676424528509738047 6698630514636792764607071)
    ·
      refine ⟨10047945771955189146910607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6698630514636792764607071 10047945771955189146910607)
      ·
        refine ⟨15071918657932783720365911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10047945771955189146910607 15071918657932783720365911)
        ·
          refine ⟨22607877986899175580548867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071918657932783720365911 22607877986899175580548867)
          ·
            refine ⟨33911816980348763370823301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22607877986899175580548867 33911816980348763370823301)
            ·
              refine ⟨6358465683815393132029369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33911816980348763370823301 6358465683815393132029369)
              ·
                refine ⟨4768849262861544849022027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6358465683815393132029369 4768849262861544849022027)
                ·
                  refine ⟨7153273894292317273533041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768849262861544849022027 7153273894292317273533041)
                  ·
                    refine ⟨5364955420719237955149781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7153273894292317273533041 5364955420719237955149781)
                    ·
                      refine ⟨125741142673107139573823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5364955420719237955149781 125741142673107139573823)
                      ·
                        rfl

theorem cell23_244880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_244880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244880 prefixEnd_244880 := by exact prefixLift 244880
  have htrace : WordTrace (prefixWord ++ tailWord_244880) baseStart_244880 baseEnd_244880 := by
    simpa [prefixWord, tailWord_244880, baseEnd_244880] using wordTrace_append hprefix tailTrace_244880
  have hstable : (prefixWord ++ tailWord_244880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244880).length < 2 ^ (prefixWord ++ tailWord_244880).sum := by decide
  have hdescent : baseEnd_244880 < baseStart_244880 := by decide
  rcases family_descends (prefixWord ++ tailWord_244880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244914 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_244914 : Nat := 118140960795 + 244914 * 2 ^ 59
def prefixEnd_244914 : Nat := 4983230072969 + 3 ^ 40 * 244914 * 2
def baseEnd_244914 : Nat := 125758601015360006548667

theorem tailTrace_244914 : CollatzResearch.WordTrace tailWord_244914 prefixEnd_244914 125758601015360006548667 := by
  unfold tailWord_244914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233186858681470206553449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5955164956483920550809197 2233186858681470206553449)
  ·
    refine ⟨1674890144011102654915087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2233186858681470206553449 1674890144011102654915087)
    ·
      refine ⟨2512335216016653982372631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674890144011102654915087 2512335216016653982372631)
      ·
        refine ⟨3768502824024980973558947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512335216016653982372631 3768502824024980973558947)
        ·
          refine ⟨5652754236037471460338421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768502824024980973558947 5652754236037471460338421)
          ·
            refine ⟨529945709628512949406727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5652754236037471460338421 529945709628512949406727)
            ·
              refine ⟨794918564442769424110091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529945709628512949406727 794918564442769424110091)
              ·
                refine ⟨1192377846664154136165137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794918564442769424110091 1192377846664154136165137)
                ·
                  refine ⟨894283384998115602123853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192377846664154136165137 894283384998115602123853)
                  ·
                    refine ⟨335356269374293350796445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894283384998115602123853 335356269374293350796445)
                    ·
                      refine ⟨125758601015360006548667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 335356269374293350796445 125758601015360006548667)
                      ·
                        rfl

theorem cell23_244914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_244914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244914 prefixEnd_244914 := by exact prefixLift 244914
  have htrace : WordTrace (prefixWord ++ tailWord_244914) baseStart_244914 baseEnd_244914 := by
    simpa [prefixWord, tailWord_244914, baseEnd_244914] using wordTrace_append hprefix tailTrace_244914
  have hstable : (prefixWord ++ tailWord_244914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244914).length < 2 ^ (prefixWord ++ tailWord_244914).sum := by decide
  have hdescent : baseEnd_244914 < baseStart_244914 := by decide
  rcases family_descends (prefixWord ++ tailWord_244914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244964 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_244964 : Nat := 118140960795 + 244964 * 2 ^ 59
def prefixEnd_244964 : Nat := 4983230072969 + 3 ^ 40 * 244964 * 2
def baseEnd_244964 : Nat := 41928091682694936974479

theorem tailTrace_244964 : CollatzResearch.WordTrace tailWord_244964 prefixEnd_244964 41928091682694936974479 := by
  unfold tailWord_244964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467285542272369682766973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5956380723029826243689297 4467285542272369682766973)
  ·
    refine ⟨1675232078352138631037615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4467285542272369682766973 1675232078352138631037615)
    ·
      refine ⟨2512848117528207946556423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1675232078352138631037615 2512848117528207946556423)
      ·
        refine ⟨3769272176292311919834635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512848117528207946556423 3769272176292311919834635)
        ·
          refine ⟨5653908264438467879751953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769272176292311919834635 5653908264438467879751953)
          ·
            refine ⟨4240431198328850909813965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653908264438467879751953 4240431198328850909813965)
            ·
              refine ⟨1590161699373319091180237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4240431198328850909813965 1590161699373319091180237)
              ·
                refine ⟨596310637264994659192589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590161699373319091180237 596310637264994659192589)
                ·
                  refine ⟨223616488974372997197221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596310637264994659192589 223616488974372997197221)
                  ·
                    refine ⟨41928091682694936974479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223616488974372997197221 41928091682694936974479)
                    ·
                      rfl

theorem cell23_244964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_244964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244964 prefixEnd_244964 := by exact prefixLift 244964
  have htrace : WordTrace (prefixWord ++ tailWord_244964) baseStart_244964 baseEnd_244964 := by
    simpa [prefixWord, tailWord_244964, baseEnd_244964] using wordTrace_append hprefix tailTrace_244964
  have hstable : (prefixWord ++ tailWord_244964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244964).length < 2 ^ (prefixWord ++ tailWord_244964).sum := by decide
  have hdescent : baseEnd_244964 < baseStart_244964 := by decide
  rcases family_descends (prefixWord ++ tailWord_244964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244974 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_244974 : Nat := 118140960795 + 244974 * 2 ^ 59
def prefixEnd_244974 : Nat := 4983230072969 + 3 ^ 40 * 244974 * 2
def baseEnd_244974 : Nat := 125789409854629771798391

theorem tailTrace_244974 : CollatzResearch.WordTrace tailWord_244974 prefixEnd_244974 125789409854629771798391 := by
  unfold tailWord_244974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116866976813563884174747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5956623876339007382265317 1116866976813563884174747)
  ·
    refine ⟨1675300465220345826262121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1116866976813563884174747 1675300465220345826262121)
    ·
      refine ⟨1256475348915259369696591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1675300465220345826262121 1256475348915259369696591)
      ·
        refine ⟨1884713023372889054544887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256475348915259369696591 1884713023372889054544887)
        ·
          refine ⟨2827069535059333581817331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884713023372889054544887 2827069535059333581817331)
          ·
            refine ⟨4240604302589000372725997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827069535059333581817331 4240604302589000372725997)
            ·
              refine ⟨1590226613470875139772249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4240604302589000372725997 1590226613470875139772249)
              ·
                refine ⟨1192669960103156354829187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590226613470875139772249 1192669960103156354829187)
                ·
                  refine ⟨1789004940154734532243781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192669960103156354829187 1789004940154734532243781)
                  ·
                    refine ⟨335438426279012724795709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789004940154734532243781 335438426279012724795709)
                    ·
                      refine ⟨125789409854629771798391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 335438426279012724795709 125789409854629771798391)
                      ·
                        rfl

theorem cell23_244974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_244974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_244974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_244974 prefixEnd_244974 := by exact prefixLift 244974
  have htrace : WordTrace (prefixWord ++ tailWord_244974) baseStart_244974 baseEnd_244974 := by
    simpa [prefixWord, tailWord_244974, baseEnd_244974] using wordTrace_append hprefix tailTrace_244974
  have hstable : (prefixWord ++ tailWord_244974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244974).length < 2 ^ (prefixWord ++ tailWord_244974).sum := by decide
  have hdescent : baseEnd_244974 < baseStart_244974 := by decide
  rcases family_descends (prefixWord ++ tailWord_244974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245007 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 7, 5]
def baseStart_245007 : Nat := 118140960795 + 245007 * 2 ^ 59
def prefixEnd_245007 : Nat := 4983230072969 + 3 ^ 40 * 245007 * 2
def baseEnd_245007 : Nat := 41935451572076047561913

theorem tailTrace_245007 : CollatzResearch.WordTrace tailWord_245007 prefixEnd_245007 41935451572076047561913 := by
  unfold tailWord_245007
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936139423388957709349275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5957426282259305139566183 8936139423388957709349275)
  ·
    refine ⟨13404209135083436564023913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936139423388957709349275 13404209135083436564023913)
    ·
      refine ⟨10053156851312577423017935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13404209135083436564023913 10053156851312577423017935)
      ·
        refine ⟨15079735276968866134526903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053156851312577423017935 15079735276968866134526903)
        ·
          refine ⟨22619602915453299201790355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15079735276968866134526903 22619602915453299201790355)
          ·
            refine ⟨33929404373179948802685533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22619602915453299201790355 33929404373179948802685533)
            ·
              refine ⟨12723526639942480801007075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33929404373179948802685533 12723526639942480801007075)
              ·
                refine ⟨19085289959913721201510613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12723526639942480801007075 19085289959913721201510613)
                ·
                  refine ⟨447311483435477840660405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19085289959913721201510613 447311483435477840660405)
                  ·
                    refine ⟨41935451572076047561913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 447311483435477840660405 41935451572076047561913)
                    ·
                      rfl

theorem cell23_245007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_245007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245007 prefixEnd_245007 := by exact prefixLift 245007
  have htrace : WordTrace (prefixWord ++ tailWord_245007) baseStart_245007 baseEnd_245007 := by
    simpa [prefixWord, tailWord_245007, baseEnd_245007] using wordTrace_append hprefix tailTrace_245007
  have hstable : (prefixWord ++ tailWord_245007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245007).length < 2 ^ (prefixWord ++ tailWord_245007).sum := by decide
  have hdescent : baseEnd_245007 < baseStart_245007 := by decide
  rcases family_descends (prefixWord ++ tailWord_245007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245041 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 1, 5]
def baseStart_245041 : Nat := 118140960795 + 245041 * 2 ^ 59
def prefixEnd_245041 : Nat := 4983230072969 + 3 ^ 40 * 245041 * 2
def baseEnd_245041 : Nat := 41941271019493669886861

theorem tailTrace_245041 : CollatzResearch.WordTrace tailWord_245041 prefixEnd_245041 41941271019493669886861 := by
  unfold tailWord_245041
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937379505265781516086977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5958253003510521010724651 8937379505265781516086977)
  ·
    refine ⟨6703034628949336137065233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8937379505265781516086977 6703034628949336137065233)
    ·
      refine ⟨5027275971712002102798925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6703034628949336137065233 5027275971712002102798925)
      ·
        refine ⟨1885228489392000788549597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5027275971712002102798925 1885228489392000788549597)
        ·
          refine ⟨706960683522000295706099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1885228489392000788549597 706960683522000295706099)
          ·
            refine ⟨1060441025283000443559149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706960683522000295706099 1060441025283000443559149)
            ·
              refine ⟨397665384481125166334681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060441025283000443559149 397665384481125166334681)
              ·
                refine ⟨298249038360843874751011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397665384481125166334681 298249038360843874751011)
                ·
                  refine ⟨447373557541265812126517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298249038360843874751011 447373557541265812126517)
                  ·
                    refine ⟨41941271019493669886861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 447373557541265812126517 41941271019493669886861)
                    ·
                      rfl

theorem cell23_245041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_245041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245041 prefixEnd_245041 := by exact prefixLift 245041
  have htrace : WordTrace (prefixWord ++ tailWord_245041) baseStart_245041 baseEnd_245041 := by
    simpa [prefixWord, tailWord_245041, baseEnd_245041] using wordTrace_append hprefix tailTrace_245041
  have hstable : (prefixWord ++ tailWord_245041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245041).length < 2 ^ (prefixWord ++ tailWord_245041).sum := by decide
  have hdescent : baseEnd_245041 < baseStart_245041 := by decide
  rcases family_descends (prefixWord ++ tailWord_245041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245047 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_245047 : Nat := 118140960795 + 245047 * 2 ^ 59
def prefixEnd_245047 : Nat := 4983230072969 + 3 ^ 40 * 245047 * 2
def baseEnd_245047 : Nat := 125826893942407986185555

theorem tailTrace_245047 : CollatzResearch.WordTrace tailWord_245047 prefixEnd_245047 125826893942407986185555 := by
  unfold tailWord_245047
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937598343244044540805395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5958398895496029693870263 8937598343244044540805395)
  ·
    refine ⟨13406397514866066811208093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8937598343244044540805395 13406397514866066811208093)
    ·
      refine ⟨5027399068074775054203035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13406397514866066811208093 5027399068074775054203035)
      ·
        refine ⟨7541098602112162581304553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5027399068074775054203035 7541098602112162581304553)
        ·
          refine ⟨5655823951584121935978415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7541098602112162581304553 5655823951584121935978415)
          ·
            refine ⟨8483735927376182903967623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655823951584121935978415 8483735927376182903967623)
            ·
              refine ⟨12725603891064274355951435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8483735927376182903967623 12725603891064274355951435)
              ·
                refine ⟨19088405836596411533927153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12725603891064274355951435 19088405836596411533927153)
                ·
                  refine ⟨14316304377447308650445365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19088405836596411533927153 14316304377447308650445365)
                  ·
                    refine ⟨1342153535385685185979253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14316304377447308650445365 1342153535385685185979253)
                    ·
                      refine ⟨125826893942407986185555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1342153535385685185979253 125826893942407986185555)
                      ·
                        rfl

theorem cell23_245047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_245047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245047 prefixEnd_245047 := by exact prefixLift 245047
  have htrace : WordTrace (prefixWord ++ tailWord_245047) baseStart_245047 baseEnd_245047 := by
    simpa [prefixWord, tailWord_245047, baseEnd_245047] using wordTrace_append hprefix tailTrace_245047
  have hstable : (prefixWord ++ tailWord_245047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245047).length < 2 ^ (prefixWord ++ tailWord_245047).sum := by decide
  have hdescent : baseEnd_245047 < baseStart_245047 := by decide
  rcases family_descends (prefixWord ++ tailWord_245047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245074 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_245074 : Nat := 118140960795 + 245074 * 2 ^ 59
def prefixEnd_245074 : Nat := 4983230072969 + 3 ^ 40 * 245074 * 2
def baseEnd_245074 : Nat := 125840757920079380547931

theorem tailTrace_245074 : CollatzResearch.WordTrace tailWord_245074 prefixEnd_245074 125840757920079380547931 := by
  unfold tailWord_245074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234645778536557038009569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5959055409430818768025517 2234645778536557038009569)
  ·
    refine ⟨1675984333902417778507177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2234645778536557038009569 1675984333902417778507177)
    ·
      refine ⟨1256988250426813333880383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1675984333902417778507177 1256988250426813333880383)
      ·
        refine ⟨1885482375640220000820575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256988250426813333880383 1885482375640220000820575)
        ·
          refine ⟨2828223563460330001230863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885482375640220000820575 2828223563460330001230863)
          ·
            refine ⟨4242335345190495001846295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828223563460330001230863 4242335345190495001846295)
            ·
              refine ⟨6363503017785742502769443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242335345190495001846295 6363503017785742502769443)
              ·
                refine ⟨9545254526678613754154165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363503017785742502769443 9545254526678613754154165)
                ·
                  refine ⟨894867611876120039451953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9545254526678613754154165 894867611876120039451953)
                  ·
                    refine ⟨671150708907090029588965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894867611876120039451953 671150708907090029588965)
                    ·
                      refine ⟨125840757920079380547931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 671150708907090029588965 125840757920079380547931)
                      ·
                        rfl

theorem cell23_245074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_245074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245074 prefixEnd_245074 := by exact prefixLift 245074
  have htrace : WordTrace (prefixWord ++ tailWord_245074) baseStart_245074 baseEnd_245074 := by
    simpa [prefixWord, tailWord_245074, baseEnd_245074] using wordTrace_append hprefix tailTrace_245074
  have hstable : (prefixWord ++ tailWord_245074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245074).length < 2 ^ (prefixWord ++ tailWord_245074).sum := by decide
  have hdescent : baseEnd_245074 < baseStart_245074 := by decide
  rcases family_descends (prefixWord ++ tailWord_245074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245091 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 4]
def baseStart_245091 : Nat := 118140960795 + 245091 * 2 ^ 59
def prefixEnd_245091 : Nat := 4983230072969 + 3 ^ 40 * 245091 * 2
def baseEnd_245091 : Nat := 125849487091205814035353

theorem tailTrace_245091 : CollatzResearch.WordTrace tailWord_245091 prefixEnd_245091 125849487091205814035353 := by
  unfold tailWord_245091
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939203155084640055407127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5959468770056426703604751 8939203155084640055407127)
  ·
    refine ⟨13408804732626960083110691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8939203155084640055407127 13408804732626960083110691)
    ·
      refine ⟨20113207098940440124666037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13408804732626960083110691 20113207098940440124666037)
      ·
        refine ⟨1885613165525666261687441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20113207098940440124666037 1885613165525666261687441)
        ·
          refine ⟨1414209874144249696265581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885613165525666261687441 1414209874144249696265581)
          ·
            refine ⟨530328702804093636099593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1414209874144249696265581 530328702804093636099593)
            ·
              refine ⟨397746527103070227074695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530328702804093636099593 397746527103070227074695)
              ·
                refine ⟨596619790654605340612043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397746527103070227074695 596619790654605340612043)
                ·
                  refine ⟨894929685981908010918065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596619790654605340612043 894929685981908010918065)
                  ·
                    refine ⟨671197264486431008188549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894929685981908010918065 671197264486431008188549)
                    ·
                      refine ⟨125849487091205814035353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 671197264486431008188549 125849487091205814035353)
                      ·
                        rfl

theorem cell23_245091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_245091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245091 prefixEnd_245091 := by exact prefixLift 245091
  have htrace : WordTrace (prefixWord ++ tailWord_245091) baseStart_245091 baseEnd_245091 := by
    simpa [prefixWord, tailWord_245091, baseEnd_245091] using wordTrace_append hprefix tailTrace_245091
  have hstable : (prefixWord ++ tailWord_245091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245091).length < 2 ^ (prefixWord ++ tailWord_245091).sum := by decide
  have hdescent : baseEnd_245091 < baseStart_245091 := by decide
  rcases family_descends (prefixWord ++ tailWord_245091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245095 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_245095 : Nat := 118140960795 + 245095 * 2 ^ 59
def prefixEnd_245095 : Nat := 4983230072969 + 3 ^ 40 * 245095 * 2
def baseEnd_245095 : Nat := 125851541013823798385335

theorem tailTrace_245095 : CollatzResearch.WordTrace tailWord_245095 prefixEnd_245095 125851541013823798385335 := by
  unfold tailWord_245095
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939349047070148738552739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5959566031380099159035159 8939349047070148738552739)
  ·
    refine ⟨13409023570605223107829109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8939349047070148738552739 13409023570605223107829109)
    ·
      refine ⟨1257095959744239666358979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13409023570605223107829109 1257095959744239666358979)
      ·
        refine ⟨1885643939616359499538469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257095959744239666358979 1885643939616359499538469)
        ·
          refine ⟨353558238678067406163463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1885643939616359499538469 353558238678067406163463)
          ·
            refine ⟨530337358017101109245195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353558238678067406163463 530337358017101109245195)
            ·
              refine ⟨795506037025651663867793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530337358017101109245195 795506037025651663867793)
              ·
                refine ⟨596629527769238747900845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795506037025651663867793 596629527769238747900845)
                ·
                  refine ⟨223736072913464530462817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596629527769238747900845 223736072913464530462817)
                  ·
                    refine ⟨167802054685098397847113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223736072913464530462817 167802054685098397847113)
                    ·
                      refine ⟨125851541013823798385335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167802054685098397847113 125851541013823798385335)
                      ·
                        rfl

theorem cell23_245095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_245095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245095 prefixEnd_245095 := by exact prefixLift 245095
  have htrace : WordTrace (prefixWord ++ tailWord_245095) baseStart_245095 baseEnd_245095 := by
    simpa [prefixWord, tailWord_245095, baseEnd_245095] using wordTrace_append hprefix tailTrace_245095
  have hstable : (prefixWord ++ tailWord_245095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245095).length < 2 ^ (prefixWord ++ tailWord_245095).sum := by decide
  have hdescent : baseEnd_245095 < baseStart_245095 := by decide
  rcases family_descends (prefixWord ++ tailWord_245095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245101 : List Nat := [1, 5, 1, 1, 1, 4, 3, 7]
def baseStart_245101 : Nat := 118140960795 + 245101 * 2 ^ 59
def prefixEnd_245101 : Nat := 4983230072969 + 3 ^ 40 * 245101 * 2
def baseEnd_245101 : Nat := 4661282292509287959641

theorem tailTrace_245101 : CollatzResearch.WordTrace tailWord_245101 prefixEnd_245101 4661282292509287959641 := by
  unfold tailWord_245101
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939567885048411763271157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5959711923365607842180771 8939567885048411763271157)
  ·
    refine ⟨838084489223288602806671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8939567885048411763271157 838084489223288602806671)
    ·
      refine ⟨1257126733834932904210007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838084489223288602806671 1257126733834932904210007)
      ·
        refine ⟨1885690100752399356315011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257126733834932904210007 1885690100752399356315011)
        ·
          refine ⟨2828535151128599034472517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885690100752399356315011 2828535151128599034472517)
          ·
            refine ⟨530350340836612318963597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2828535151128599034472517 530350340836612318963597)
            ·
              refine ⟨198881377813729619611349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530350340836612318963597 198881377813729619611349)
              ·
                refine ⟨4661282292509287959641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 198881377813729619611349 4661282292509287959641)
                ·
                  rfl

theorem cell23_245101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 7].length) (baseStart_245101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245101 prefixEnd_245101 := by exact prefixLift 245101
  have htrace : WordTrace (prefixWord ++ tailWord_245101) baseStart_245101 baseEnd_245101 := by
    simpa [prefixWord, tailWord_245101, baseEnd_245101] using wordTrace_append hprefix tailTrace_245101
  have hstable : (prefixWord ++ tailWord_245101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245101).length < 2 ^ (prefixWord ++ tailWord_245101).sum := by decide
  have hdescent : baseEnd_245101 < baseStart_245101 := by decide
  rcases family_descends (prefixWord ++ tailWord_245101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245111 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_245111 : Nat := 118140960795 + 245111 * 2 ^ 59
def prefixEnd_245111 : Nat := 4983230072969 + 3 ^ 40 * 245111 * 2
def baseEnd_245111 : Nat := 125859756704295735785261

theorem tailTrace_245111 : CollatzResearch.WordTrace tailWord_245111 prefixEnd_245111 125859756704295735785261 := by
  unfold tailWord_245111
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939932615012183471135187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5959955076674788980756791 8939932615012183471135187)
  ·
    refine ⟨13409898922518275206702781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8939932615012183471135187 13409898922518275206702781)
    ·
      refine ⟨5028712095944353202513543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13409898922518275206702781 5028712095944353202513543)
      ·
        refine ⟨7543068143916529803770315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028712095944353202513543 7543068143916529803770315)
        ·
          refine ⟨11314602215874794705655473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543068143916529803770315 11314602215874794705655473)
          ·
            refine ⟨8485951661906096029241605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11314602215874794705655473 8485951661906096029241605)
            ·
              refine ⟨1591115936607393005482801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8485951661906096029241605 1591115936607393005482801)
              ·
                refine ⟨1193336952455544754112101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591115936607393005482801 1193336952455544754112101)
                ·
                  refine ⟨223750678585414641396019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193336952455544754112101 223750678585414641396019)
                  ·
                    refine ⟨335626017878121962094029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223750678585414641396019 335626017878121962094029)
                    ·
                      refine ⟨125859756704295735785261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 335626017878121962094029 125859756704295735785261)
                      ·
                        rfl

theorem cell23_245111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_245111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245111 prefixEnd_245111 := by exact prefixLift 245111
  have htrace : WordTrace (prefixWord ++ tailWord_245111) baseStart_245111 baseEnd_245111 := by
    simpa [prefixWord, tailWord_245111, baseEnd_245111] using wordTrace_append hprefix tailTrace_245111
  have hstable : (prefixWord ++ tailWord_245111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245111).length < 2 ^ (prefixWord ++ tailWord_245111).sum := by decide
  have hdescent : baseEnd_245111 < baseStart_245111 := by decide
  rcases family_descends (prefixWord ++ tailWord_245111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245118 : List Nat := [4, 2, 3, 2, 1, 1, 10]
def baseStart_245118 : Nat := 118140960795 + 245118 * 2 ^ 59
def prefixEnd_245118 : Nat := 4983230072969 + 3 ^ 40 * 245118 * 2
def baseEnd_245118 : Nat := 1553868531714533437009

theorem tailTrace_245118 : CollatzResearch.WordTrace tailWord_245118 prefixEnd_245118 1553868531714533437009 := by
  unfold tailWord_245118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117523490748352958330001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5960125283991215777760005 1117523490748352958330001)
  ·
    refine ⟨838142618061264718747501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1117523490748352958330001 838142618061264718747501)
    ·
      refine ⟨314303481772974269530313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 838142618061264718747501 314303481772974269530313)
      ·
        refine ⟨235727611329730702147735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314303481772974269530313 235727611329730702147735)
        ·
          refine ⟨353591416994596053221603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235727611329730702147735 353591416994596053221603)
          ·
            refine ⟨530387125491894079832405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353591416994596053221603 530387125491894079832405)
            ·
              refine ⟨1553868531714533437009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 530387125491894079832405 1553868531714533437009)
              ·
                rfl

theorem cell23_245118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 10].length) (baseStart_245118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245118 prefixEnd_245118 := by exact prefixLift 245118
  have htrace : WordTrace (prefixWord ++ tailWord_245118) baseStart_245118 baseEnd_245118 := by
    simpa [prefixWord, tailWord_245118, baseEnd_245118] using wordTrace_append hprefix tailTrace_245118
  have hstable : (prefixWord ++ tailWord_245118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245118).length < 2 ^ (prefixWord ++ tailWord_245118).sum := by decide
  have hdescent : baseEnd_245118 < baseStart_245118 := by decide
  rcases family_descends (prefixWord ++ tailWord_245118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245122 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_245122 : Nat := 118140960795 + 245122 * 2 ^ 59
def prefixEnd_245122 : Nat := 4983230072969 + 3 ^ 40 * 245122 * 2
def baseEnd_245122 : Nat := 41955134997165064249237

theorem tailTrace_245122 : CollatzResearch.WordTrace tailWord_245122 prefixEnd_245122 41955134997165064249237 := by
  unfold tailWord_245122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235083454493083087446405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5960222545314888233190413 2235083454493083087446405)
  ·
    refine ⟨419078147717453078896201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2235083454493083087446405 419078147717453078896201)
    ·
      refine ⟨314308610788089809172151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419078147717453078896201 314308610788089809172151)
      ·
        refine ⟨471462916182134713758227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314308610788089809172151 471462916182134713758227)
        ·
          refine ⟨707194374273202070637341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471462916182134713758227 707194374273202070637341)
          ·
            refine ⟨265197890352450776489003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707194374273202070637341 265197890352450776489003)
            ·
              refine ⟨397796835528676164733505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265197890352450776489003 397796835528676164733505)
              ·
                refine ⟨298347626646507123550129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397796835528676164733505 298347626646507123550129)
                ·
                  refine ⟨223760719984880342662597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298347626646507123550129 223760719984880342662597)
                  ·
                    refine ⟨41955134997165064249237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223760719984880342662597 41955134997165064249237)
                    ·
                      rfl

theorem cell23_245122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_245122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245122 prefixEnd_245122 := by exact prefixLift 245122
  have htrace : WordTrace (prefixWord ++ tailWord_245122) baseStart_245122 baseEnd_245122 := by
    simpa [prefixWord, tailWord_245122, baseEnd_245122] using wordTrace_append hprefix tailTrace_245122
  have hstable : (prefixWord ++ tailWord_245122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245122).length < 2 ^ (prefixWord ++ tailWord_245122).sum := by decide
  have hdescent : baseEnd_245122 < baseStart_245122 := by decide
  rcases family_descends (prefixWord ++ tailWord_245122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245128 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_245128 : Nat := 118140960795 + 245128 * 2 ^ 59
def prefixEnd_245128 : Nat := 4983230072969 + 3 ^ 40 * 245128 * 2
def baseEnd_245128 : Nat := 125868485875422169272683

theorem tailTrace_245128 : CollatzResearch.WordTrace tailWord_245128 prefixEnd_245128 125868485875422169272683 := by
  unfold tailWord_245128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470276327975297687252019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5960368437300396916336025 4470276327975297687252019)
  ·
    refine ⟨6705414491962946530878029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4470276327975297687252019 6705414491962946530878029)
    ·
      refine ⟨2514530434486104949079261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6705414491962946530878029 2514530434486104949079261)
      ·
        refine ⟨942948912932289355904723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2514530434486104949079261 942948912932289355904723)
        ·
          refine ⟨1414423369398434033857085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942948912932289355904723 1414423369398434033857085)
          ·
            refine ⟨530408763524412762696407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1414423369398434033857085 530408763524412762696407)
            ·
              refine ⟨795613145286619144044611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530408763524412762696407 795613145286619144044611)
              ·
                refine ⟨1193419717929928716066917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795613145286619144044611 1193419717929928716066917)
                ·
                  refine ⟨223766197111861634262547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193419717929928716066917 223766197111861634262547)
                  ·
                    refine ⟨335649295667792451393821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223766197111861634262547 335649295667792451393821)
                    ·
                      refine ⟨125868485875422169272683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 335649295667792451393821 125868485875422169272683)
                      ·
                        rfl

theorem cell23_245128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_245128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245128 prefixEnd_245128 := by exact prefixLift 245128
  have htrace : WordTrace (prefixWord ++ tailWord_245128) baseStart_245128 baseEnd_245128 := by
    simpa [prefixWord, tailWord_245128, baseEnd_245128] using wordTrace_append hprefix tailTrace_245128
  have hstable : (prefixWord ++ tailWord_245128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245128).length < 2 ^ (prefixWord ++ tailWord_245128).sum := by decide
  have hdescent : baseEnd_245128 < baseStart_245128 := by decide
  rcases family_descends (prefixWord ++ tailWord_245128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245145 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 2, 1, 3]
def baseStart_245145 : Nat := 118140960795 + 245145 * 2 ^ 59
def prefixEnd_245145 : Nat := 4983230072969 + 3 ^ 40 * 245145 * 2
def baseEnd_245145 : Nat := 125877215046548602760105

theorem tailTrace_245145 : CollatzResearch.WordTrace tailWord_245145 prefixEnd_245145 125877215046548602760105 := by
  unfold tailWord_245145
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941172696889007277872889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5960781797926004851915259 8941172696889007277872889)
  ·
    refine ⟨6705879522666755458404667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8941172696889007277872889 6705879522666755458404667)
    ·
      refine ⟨10058819284000133187607001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705879522666755458404667 10058819284000133187607001)
      ·
        refine ⟨7544114463000099890705251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10058819284000133187607001 7544114463000099890705251)
        ·
          refine ⟨11316171694500149836057877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544114463000099890705251 11316171694500149836057877)
          ·
            refine ⟨530445548179694523565213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11316171694500149836057877 530445548179694523565213)
            ·
              refine ⟨198917080567385446336955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530445548179694523565213 198917080567385446336955)
              ·
                refine ⟨298375620851078169505433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198917080567385446336955 298375620851078169505433)
                ·
                  refine ⟨223781715638308627129075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298375620851078169505433 223781715638308627129075)
                  ·
                    refine ⟨335672573457462940693613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223781715638308627129075 335672573457462940693613)
                    ·
                      refine ⟨125877215046548602760105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 335672573457462940693613 125877215046548602760105)
                      ·
                        rfl

theorem cell23_245145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_245145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245145 prefixEnd_245145 := by exact prefixLift 245145
  have htrace : WordTrace (prefixWord ++ tailWord_245145) baseStart_245145 baseEnd_245145 := by
    simpa [prefixWord, tailWord_245145, baseEnd_245145] using wordTrace_append hprefix tailTrace_245145
  have hstable : (prefixWord ++ tailWord_245145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245145).length < 2 ^ (prefixWord ++ tailWord_245145).sum := by decide
  have hdescent : baseEnd_245145 < baseStart_245145 := by decide
  rcases family_descends (prefixWord ++ tailWord_245145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245164 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_245164 : Nat := 118140960795 + 245164 * 2 ^ 59
def prefixEnd_245164 : Nat := 4983230072969 + 3 ^ 40 * 245164 * 2
def baseEnd_245164 : Nat := 125886971178984028422517

theorem tailTrace_245164 : CollatzResearch.WordTrace tailWord_245164 prefixEnd_245164 125886971178984028422517 := by
  unfold tailWord_245164
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470932841910086761407273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5961243789213449015209697 4470932841910086761407273)
  ·
    refine ⟨3353199631432565071055455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4470932841910086761407273 3353199631432565071055455)
    ·
      refine ⟨5029799447148847606583183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353199631432565071055455 5029799447148847606583183)
      ·
        refine ⟨7544699170723271409874775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029799447148847606583183 7544699170723271409874775)
        ·
          refine ⟨11317048756084907114812163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544699170723271409874775 11317048756084907114812163)
          ·
            refine ⟨16975573134127360672218245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11317048756084907114812163 16975573134127360672218245)
            ·
              refine ⟨3182919962648880126040921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16975573134127360672218245 3182919962648880126040921)
              ·
                refine ⟨2387189971986660094530691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182919962648880126040921 2387189971986660094530691)
                ·
                  refine ⟨3580784957979990141796037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387189971986660094530691 3580784957979990141796037)
                  ·
                    refine ⟨671397179621248151586757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580784957979990141796037 671397179621248151586757)
                    ·
                      refine ⟨125886971178984028422517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 671397179621248151586757 125886971178984028422517)
                      ·
                        rfl

theorem cell23_245164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_245164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245164 prefixEnd_245164 := by exact prefixLift 245164
  have htrace : WordTrace (prefixWord ++ tailWord_245164) baseStart_245164 baseEnd_245164 := by
    simpa [prefixWord, tailWord_245164, baseEnd_245164] using wordTrace_append hprefix tailTrace_245164
  have hstable : (prefixWord ++ tailWord_245164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245164).length < 2 ^ (prefixWord ++ tailWord_245164).sum := by decide
  have hdescent : baseEnd_245164 < baseStart_245164 := by decide
  rcases family_descends (prefixWord ++ tailWord_245164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245238 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_245238 : Nat := 118140960795 + 245238 * 2 ^ 59
def prefixEnd_245238 : Nat := 4983230072969 + 3 ^ 40 * 245238 * 2
def baseEnd_245238 : Nat := 41974989582472246299059

theorem tailTrace_245238 : CollatzResearch.WordTrace tailWord_245238 prefixEnd_245238 41974989582472246299059 := by
  unfold tailWord_245238
  simp only [CollatzResearch.WordTrace]
  refine ⟨559035292847005260063023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5963043123701389440672245 559035292847005260063023)
  ·
    refine ⟨838552939270507890094535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 559035292847005260063023 838552939270507890094535)
    ·
      refine ⟨1257829408905761835141803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838552939270507890094535 1257829408905761835141803)
      ·
        refine ⟨1886744113358642752712705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257829408905761835141803 1886744113358642752712705)
        ·
          refine ⟨1415058085018982064534529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1886744113358642752712705 1415058085018982064534529)
          ·
            refine ⟨1061293563764236548400897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415058085018982064534529 1061293563764236548400897)
            ·
              refine ⟨795970172823177411300673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061293563764236548400897 795970172823177411300673)
              ·
                refine ⟨596977629617383058475505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795970172823177411300673 596977629617383058475505)
                ·
                  refine ⟨447733222213037293856629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596977629617383058475505 447733222213037293856629)
                  ·
                    refine ⟨41974989582472246299059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 447733222213037293856629 41974989582472246299059)
                    ·
                      rfl

theorem cell23_245238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_245238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245238 prefixEnd_245238 := by exact prefixLift 245238
  have htrace : WordTrace (prefixWord ++ tailWord_245238) baseStart_245238 baseEnd_245238 := by
    simpa [prefixWord, tailWord_245238, baseEnd_245238] using wordTrace_append hprefix tailTrace_245238
  have hstable : (prefixWord ++ tailWord_245238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245238).length < 2 ^ (prefixWord ++ tailWord_245238).sum := by decide
  have hdescent : baseEnd_245238 < baseStart_245238 := by decide
  rcases family_descends (prefixWord ++ tailWord_245238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245258 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_245258 : Nat := 118140960795 + 245258 * 2 ^ 59
def prefixEnd_245258 : Nat := 4983230072969 + 3 ^ 40 * 245258 * 2
def baseEnd_245258 : Nat := 125935238360506660647085

theorem tailTrace_245258 : CollatzResearch.WordTrace tailWord_245258 prefixEnd_245258 125935238360506660647085 := by
  unfold tailWord_245258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236323536369906894184107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5963529430319751717824285 2236323536369906894184107)
  ·
    refine ⟨3354485304554860341276161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2236323536369906894184107 3354485304554860341276161)
    ·
      refine ⟨2515863978416145255957121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3354485304554860341276161 2515863978416145255957121)
      ·
        refine ⟨1886897983812108941967841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2515863978416145255957121 1886897983812108941967841)
        ·
          refine ⟨1415173487859081706475881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1886897983812108941967841 1415173487859081706475881)
          ·
            refine ⟨1061380115894311279856911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415173487859081706475881 1061380115894311279856911)
            ·
              refine ⟨1592070173841466919785367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061380115894311279856911 1592070173841466919785367)
              ·
                refine ⟨2388105260762200379678051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592070173841466919785367 2388105260762200379678051)
                ·
                  refine ⟨3582157891143300569517077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388105260762200379678051 3582157891143300569517077)
                  ·
                    refine ⟨167913651147342214196113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3582157891143300569517077 167913651147342214196113)
                    ·
                      refine ⟨125935238360506660647085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167913651147342214196113 125935238360506660647085)
                      ·
                        rfl

theorem cell23_245258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_245258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245258 prefixEnd_245258 := by exact prefixLift 245258
  have htrace : WordTrace (prefixWord ++ tailWord_245258) baseStart_245258 baseEnd_245258 := by
    simpa [prefixWord, tailWord_245258, baseEnd_245258] using wordTrace_append hprefix tailTrace_245258
  have hstable : (prefixWord ++ tailWord_245258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245258).length < 2 ^ (prefixWord ++ tailWord_245258).sum := by decide
  have hdescent : baseEnd_245258 < baseStart_245258 := by decide
  rcases family_descends (prefixWord ++ tailWord_245258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245301 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_245301 : Nat := 118140960795 + 245301 * 2 ^ 59
def prefixEnd_245301 : Nat := 4983230072969 + 3 ^ 40 * 245301 * 2
def baseEnd_245301 : Nat := 125957318028649992409387

theorem tailTrace_245301 : CollatzResearch.WordTrace tailWord_245301 prefixEnd_245301 125957318028649992409387 := by
  unfold tailWord_245301
  simp only [CollatzResearch.WordTrace]
  refine ⟨8946862484323845920551757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5964574989549230613701171 8946862484323845920551757)
  ·
    refine ⟨3355073431621442220206909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8946862484323845920551757 3355073431621442220206909)
    ·
      refine ⟨1258152536858040832577591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3355073431621442220206909 1258152536858040832577591)
      ·
        refine ⟨1887228805287061248866387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258152536858040832577591 1887228805287061248866387)
        ·
          refine ⟨2830843207930591873299581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887228805287061248866387 2830843207930591873299581)
          ·
            refine ⟨1061566202973971952487343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2830843207930591873299581 1061566202973971952487343)
            ·
              refine ⟨1592349304460957928731015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061566202973971952487343 1592349304460957928731015)
              ·
                refine ⟨2388523956691436893096523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592349304460957928731015 2388523956691436893096523)
                ·
                  refine ⟨3582785935037155339644785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388523956691436893096523 3582785935037155339644785)
                  ·
                    refine ⟨2687089451277866504733589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3582785935037155339644785 2687089451277866504733589)
                    ·
                      refine ⟨125957318028649992409387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2687089451277866504733589 125957318028649992409387)
                      ·
                        rfl

theorem cell23_245301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_245301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245301 prefixEnd_245301 := by exact prefixLift 245301
  have htrace : WordTrace (prefixWord ++ tailWord_245301) baseStart_245301 baseEnd_245301 := by
    simpa [prefixWord, tailWord_245301, baseEnd_245301] using wordTrace_append hprefix tailTrace_245301
  have hstable : (prefixWord ++ tailWord_245301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245301).length < 2 ^ (prefixWord ++ tailWord_245301).sum := by decide
  have hdescent : baseEnd_245301 < baseStart_245301 := by decide
  rcases family_descends (prefixWord ++ tailWord_245301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245302 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_245302 : Nat := 118140960795 + 245302 * 2 ^ 59
def prefixEnd_245302 : Nat := 4983230072969 + 3 ^ 40 * 245302 * 2
def baseEnd_245302 : Nat := 41985943836434829498961

theorem tailTrace_245302 : CollatzResearch.WordTrace tailWord_245302 prefixEnd_245302 41985943836434829498961 := by
  unfold tailWord_245302
  simp only [CollatzResearch.WordTrace]
  refine ⟨559181184832513943208635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5964599304880148727558773 559181184832513943208635)
  ·
    refine ⟨838771777248770914812953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 559181184832513943208635 838771777248770914812953)
    ·
      refine ⟨629078832936578186109715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 838771777248770914812953 629078832936578186109715)
      ·
        refine ⟨943618249404867279164573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629078832936578186109715 943618249404867279164573)
        ·
          refine ⟨353856843526825229686715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 943618249404867279164573 353856843526825229686715)
          ·
            refine ⟨530785265290237844530073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353856843526825229686715 530785265290237844530073)
            ·
              refine ⟨398088948967678383397555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530785265290237844530073 398088948967678383397555)
              ·
                refine ⟨597133423451517575096333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398088948967678383397555 597133423451517575096333)
                ·
                  refine ⟨223925033794319090661125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597133423451517575096333 223925033794319090661125)
                  ·
                    refine ⟨41985943836434829498961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223925033794319090661125 41985943836434829498961)
                    ·
                      rfl

theorem cell23_245302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_245302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245302 prefixEnd_245302 := by exact prefixLift 245302
  have htrace : WordTrace (prefixWord ++ tailWord_245302) baseStart_245302 baseEnd_245302 := by
    simpa [prefixWord, tailWord_245302, baseEnd_245302] using wordTrace_append hprefix tailTrace_245302
  have hstable : (prefixWord ++ tailWord_245302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245302).length < 2 ^ (prefixWord ++ tailWord_245302).sum := by decide
  have hdescent : baseEnd_245302 < baseStart_245302 := by decide
  rcases family_descends (prefixWord ++ tailWord_245302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245328 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 1, 5]
def baseStart_245328 : Nat := 118140960795 + 245328 * 2 ^ 59
def prefixEnd_245328 : Nat := 4983230072969 + 3 ^ 40 * 245328 * 2
def baseEnd_245328 : Nat := 41990394002107128923921

theorem tailTrace_245328 : CollatzResearch.WordTrace tailWord_245328 prefixEnd_245328 41990394002107128923921 := by
  unfold tailWord_245328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473923627613014765892319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5965231503484019687856425 4473923627613014765892319)
  ·
    refine ⟨6710885441419522148838479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4473923627613014765892319 6710885441419522148838479)
    ·
      refine ⟨10066328162129283223257719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6710885441419522148838479 10066328162129283223257719)
      ·
        refine ⟨15099492243193924834886579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10066328162129283223257719 15099492243193924834886579)
        ·
          refine ⟨22649238364790887252329869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15099492243193924834886579 22649238364790887252329869)
          ·
            refine ⟨8493464386796582719623701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22649238364790887252329869 8493464386796582719623701)
            ·
              refine ⟨398131143131089814982361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8493464386796582719623701 398131143131089814982361)
              ·
                refine ⟨298598357348317361236771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398131143131089814982361 298598357348317361236771)
                ·
                  refine ⟨447897536022476041855157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298598357348317361236771 447897536022476041855157)
                  ·
                    refine ⟨41990394002107128923921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 447897536022476041855157 41990394002107128923921)
                    ·
                      rfl

theorem cell23_245328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_245328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245328 prefixEnd_245328 := by exact prefixLift 245328
  have htrace : WordTrace (prefixWord ++ tailWord_245328) baseStart_245328 baseEnd_245328 := by
    simpa [prefixWord, tailWord_245328, baseEnd_245328] using wordTrace_append hprefix tailTrace_245328
  have hstable : (prefixWord ++ tailWord_245328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245328).length < 2 ^ (prefixWord ++ tailWord_245328).sum := by decide
  have hdescent : baseEnd_245328 < baseStart_245328 := by decide
  rcases family_descends (prefixWord ++ tailWord_245328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245352 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_245352 : Nat := 118140960795 + 245352 * 2 ^ 59
def prefixEnd_245352 : Nat := 4983230072969 + 3 ^ 40 * 245352 * 2
def baseEnd_245352 : Nat := 125983505542029292871653

theorem tailTrace_245352 : CollatzResearch.WordTrace tailWord_245352 prefixEnd_245352 125983505542029292871653 := by
  unfold tailWord_245352
  simp only [CollatzResearch.WordTrace]
  refine ⟨4474361303569540815329155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5965815071426054420438873 4474361303569540815329155)
  ·
    refine ⟨6711541955354311222993733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4474361303569540815329155 6711541955354311222993733)
    ·
      refine ⟨1258414116628933354311325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6711541955354311222993733 1258414116628933354311325)
      ·
        refine ⟨471905293735850007866747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1258414116628933354311325 471905293735850007866747)
        ·
          refine ⟨707857940603775011800121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471905293735850007866747 707857940603775011800121)
          ·
            refine ⟨530893455452831258850091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707857940603775011800121 530893455452831258850091)
            ·
              refine ⟨796340183179246888275137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530893455452831258850091 796340183179246888275137)
              ·
                refine ⟨597255137384435166206353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796340183179246888275137 597255137384435166206353)
                ·
                  refine ⟨447941353038326374654765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597255137384435166206353 447941353038326374654765)
                  ·
                    refine ⟨167978007389372390495537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447941353038326374654765 167978007389372390495537)
                    ·
                      refine ⟨125983505542029292871653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 167978007389372390495537 125983505542029292871653)
                      ·
                        rfl

theorem cell23_245352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_245352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245352 prefixEnd_245352 := by exact prefixLift 245352
  have htrace : WordTrace (prefixWord ++ tailWord_245352) baseStart_245352 baseEnd_245352 := by
    simpa [prefixWord, tailWord_245352, baseEnd_245352] using wordTrace_append hprefix tailTrace_245352
  have hstable : (prefixWord ++ tailWord_245352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245352).length < 2 ^ (prefixWord ++ tailWord_245352).sum := by decide
  have hdescent : baseEnd_245352 < baseStart_245352 := by decide
  rcases family_descends (prefixWord ++ tailWord_245352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245371 : List Nat := [1, 1, 1, 1, 1, 4, 6, 8]
def baseStart_245371 : Nat := 118140960795 + 245371 * 2 ^ 59
def prefixEnd_245371 : Nat := 4983230072969 + 3 ^ 40 * 245371 * 2
def baseEnd_245371 : Nat := 4666417099054248834595

theorem tailTrace_245371 : CollatzResearch.WordTrace tailWord_245371 prefixEnd_245371 4666417099054248834595 := by
  unfold tailWord_245371
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949415594070247875599967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5966277062713498583733311 8949415594070247875599967)
  ·
    refine ⟨13424123391105371813399951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8949415594070247875599967 13424123391105371813399951)
    ·
      refine ⟨20136185086658057720099927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13424123391105371813399951 20136185086658057720099927)
      ·
        refine ⟨30204277629987086580149891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20136185086658057720099927 30204277629987086580149891)
        ·
          refine ⟨45306416444980629870224837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30204277629987086580149891 45306416444980629870224837)
          ·
            refine ⟨8494953083433868100667157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45306416444980629870224837 8494953083433868100667157)
            ·
              refine ⟨398200925785962567218773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8494953083433868100667157 398200925785962567218773)
              ·
                refine ⟨4666417099054248834595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 398200925785962567218773 4666417099054248834595)
                ·
                  rfl

theorem cell23_245371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 8].length) (baseStart_245371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245371 prefixEnd_245371 := by exact prefixLift 245371
  have htrace : WordTrace (prefixWord ++ tailWord_245371) baseStart_245371 baseEnd_245371 := by
    simpa [prefixWord, tailWord_245371, baseEnd_245371] using wordTrace_append hprefix tailTrace_245371
  have hstable : (prefixWord ++ tailWord_245371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245371).length < 2 ^ (prefixWord ++ tailWord_245371).sum := by decide
  have hdescent : baseEnd_245371 < baseStart_245371 := by decide
  rcases family_descends (prefixWord ++ tailWord_245371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245385 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 3]
def baseStart_245385 : Nat := 118140960795 + 245385 * 2 ^ 59
def prefixEnd_245385 : Nat := 4983230072969 + 3 ^ 40 * 245385 * 2
def baseEnd_245385 : Nat := 126000450403627663759001

theorem tailTrace_245385 : CollatzResearch.WordTrace tailWord_245385 prefixEnd_245385 126000450403627663759001 := by
  unfold tailWord_245385
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949926216019528266609609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5966617477346352177739739 8949926216019528266609609)
  ·
    refine ⟨6712444662014646199957207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8949926216019528266609609 6712444662014646199957207)
    ·
      refine ⟨10068666993021969299935811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6712444662014646199957207 10068666993021969299935811)
      ·
        refine ⟨15103000489532953949903717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10068666993021969299935811 15103000489532953949903717)
        ·
          refine ⟨2831812591787428865606947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15103000489532953949903717 2831812591787428865606947)
          ·
            refine ⟨4247718887681143298410421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831812591787428865606947 4247718887681143298410421)
            ·
              refine ⟨398223645720107184225977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4247718887681143298410421 398223645720107184225977)
              ·
                refine ⟨298667734290080388169483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398223645720107184225977 298667734290080388169483)
                ·
                  refine ⟨448001601435120582254225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298667734290080388169483 448001601435120582254225)
                  ·
                    refine ⟨336001201076340436690669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 448001601435120582254225 336001201076340436690669)
                    ·
                      refine ⟨126000450403627663759001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 336001201076340436690669 126000450403627663759001)
                      ·
                        rfl

theorem cell23_245385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_245385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245385 prefixEnd_245385 := by exact prefixLift 245385
  have htrace : WordTrace (prefixWord ++ tailWord_245385) baseStart_245385 baseEnd_245385 := by
    simpa [prefixWord, tailWord_245385, baseEnd_245385] using wordTrace_append hprefix tailTrace_245385
  have hstable : (prefixWord ++ tailWord_245385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245385).length < 2 ^ (prefixWord ++ tailWord_245385).sum := by decide
  have hdescent : baseEnd_245385 < baseStart_245385 := by decide
  rcases family_descends (prefixWord ++ tailWord_245385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245410 : List Nat := [3, 3, 1, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_245410 : Nat := 118140960795 + 245410 * 2 ^ 59
def prefixEnd_245410 : Nat := 4983230072969 + 3 ^ 40 * 245410 * 2
def baseEnd_245410 : Nat := 126013287419990065946387

theorem tailTrace_245410 : CollatzResearch.WordTrace tailWord_245410 prefixEnd_245410 126013287419990065946387 := by
  unfold tailWord_245410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237709510232239384067421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5967225360619305024179789 2237709510232239384067421)
  ·
    refine ⟨839141066337089769025283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2237709510232239384067421 839141066337089769025283)
    ·
      refine ⟨1258711599505634653537925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839141066337089769025283 1258711599505634653537925)
      ·
        refine ⟨236008424907306497538361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1258711599505634653537925 236008424907306497538361)
        ·
          refine ⟨177006318680479873153771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236008424907306497538361 177006318680479873153771)
          ·
            refine ⟨265509478020719809730657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177006318680479873153771 265509478020719809730657)
            ·
              refine ⟨199132108515539857297993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265509478020719809730657 199132108515539857297993)
              ·
                refine ⟨149349081386654892973495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199132108515539857297993 149349081386654892973495)
                ·
                  refine ⟨224023622079982339460243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149349081386654892973495 224023622079982339460243)
                  ·
                    refine ⟨336035433119973509190365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224023622079982339460243 336035433119973509190365)
                    ·
                      refine ⟨126013287419990065946387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 336035433119973509190365 126013287419990065946387)
                      ·
                        rfl

theorem cell23_245410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_245410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245410 prefixEnd_245410 := by exact prefixLift 245410
  have htrace : WordTrace (prefixWord ++ tailWord_245410) baseStart_245410 baseEnd_245410 := by
    simpa [prefixWord, tailWord_245410, baseEnd_245410] using wordTrace_append hprefix tailTrace_245410
  have hstable : (prefixWord ++ tailWord_245410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245410).length < 2 ^ (prefixWord ++ tailWord_245410).sum := by decide
  have hdescent : baseEnd_245410 < baseStart_245410 := by decide
  rcases family_descends (prefixWord ++ tailWord_245410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245422 : List Nat := [4, 1, 4, 1, 2, 2, 1, 8]
def baseStart_245422 : Nat := 118140960795 + 245422 * 2 ^ 59
def prefixEnd_245422 : Nat := 4983230072969 + 3 ^ 40 * 245422 * 2
def baseEnd_245422 : Nat := 4667387006957185888753

theorem tailTrace_245422 : CollatzResearch.WordTrace tailWord_245422 prefixEnd_245422 4667387006957185888753 := by
  unfold tailWord_245422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118909464610685448213315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5967517144590322390471013 1118909464610685448213315)
  ·
    refine ⟨1678364196916028172319973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1118909464610685448213315 1678364196916028172319973)
    ·
      refine ⟨314693286921755282309995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1678364196916028172319973 314693286921755282309995)
      ·
        refine ⟨472039930382632923464993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314693286921755282309995 472039930382632923464993)
        ·
          refine ⟨354029947786974692598745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472039930382632923464993 354029947786974692598745)
          ·
            refine ⟨265522460840231019449059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354029947786974692598745 265522460840231019449059)
            ·
              refine ⟨398283691260346529173589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265522460840231019449059 398283691260346529173589)
              ·
                refine ⟨4667387006957185888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 398283691260346529173589 4667387006957185888753)
                ·
                  rfl

theorem cell23_245422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_245422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245422 prefixEnd_245422 := by exact prefixLift 245422
  have htrace : WordTrace (prefixWord ++ tailWord_245422) baseStart_245422 baseEnd_245422 := by
    simpa [prefixWord, tailWord_245422, baseEnd_245422] using wordTrace_append hprefix tailTrace_245422
  have hstable : (prefixWord ++ tailWord_245422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245422).length < 2 ^ (prefixWord ++ tailWord_245422).sum := by decide
  have hdescent : baseEnd_245422 < baseStart_245422 := by decide
  rcases family_descends (prefixWord ++ tailWord_245422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245485 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_245485 : Nat := 118140960795 + 245485 * 2 ^ 59
def prefixEnd_245485 : Nat := 4983230072969 + 3 ^ 40 * 245485 * 2
def baseEnd_245485 : Nat := 126051798469077272508541

theorem tailTrace_245485 : CollatzResearch.WordTrace tailWord_245485 prefixEnd_245485 126051798469077272508541 := by
  unfold tailWord_245485
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953573515657245345249909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5969049010438163563499939 8953573515657245345249909)
  ·
    refine ⟨839397517092866751117179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8953573515657245345249909 839397517092866751117179)
    ·
      refine ⟨1259096275639300126675769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839397517092866751117179 1259096275639300126675769)
      ·
        refine ⟨944322206729475095006827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1259096275639300126675769 944322206729475095006827)
        ·
          refine ⟨1416483310094212642510241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944322206729475095006827 1416483310094212642510241)
          ·
            refine ⟨1062362482570659481882681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416483310094212642510241 1062362482570659481882681)
            ·
              refine ⟨796771861927994611412011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062362482570659481882681 796771861927994611412011)
              ·
                refine ⟨1195157792891991917118017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796771861927994611412011 1195157792891991917118017)
                ·
                  refine ⟨896368344668993937838513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1195157792891991917118017 896368344668993937838513)
                  ·
                    refine ⟨672276258501745453378885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 896368344668993937838513 672276258501745453378885)
                    ·
                      refine ⟨126051798469077272508541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 672276258501745453378885 126051798469077272508541)
                      ·
                        rfl

theorem cell23_245485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_245485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245485 prefixEnd_245485 := by exact prefixLift 245485
  have htrace : WordTrace (prefixWord ++ tailWord_245485) baseStart_245485 baseEnd_245485 := by
    simpa [prefixWord, tailWord_245485, baseEnd_245485] using wordTrace_append hprefix tailTrace_245485
  have hstable : (prefixWord ++ tailWord_245485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245485).length < 2 ^ (prefixWord ++ tailWord_245485).sum := by decide
  have hdescent : baseEnd_245485 < baseStart_245485 := by decide
  rcases family_descends (prefixWord ++ tailWord_245485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245488 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3]
def baseStart_245488 : Nat := 118140960795 + 245488 * 2 ^ 59
def prefixEnd_245488 : Nat := 4983230072969 + 3 ^ 40 * 245488 * 2
def baseEnd_245488 : Nat := 126053338911040760771027

theorem tailTrace_245488 : CollatzResearch.WordTrace tailWord_245488 prefixEnd_245488 126053338911040760771027 := by
  unfold tailWord_245488
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476841467323188428804559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5969121956430917905072745 4476841467323188428804559)
  ·
    refine ⟨6715262200984782643206839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4476841467323188428804559 6715262200984782643206839)
    ·
      refine ⟨10072893301477173964810259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715262200984782643206839 10072893301477173964810259)
      ·
        refine ⟨15109339952215760947215389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10072893301477173964810259 15109339952215760947215389)
        ·
          refine ⟨5666002482080910355205771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15109339952215760947215389 5666002482080910355205771)
          ·
            refine ⟨8499003723121365532808657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666002482080910355205771 8499003723121365532808657)
            ·
              refine ⟨6374252792341024149606493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8499003723121365532808657 6374252792341024149606493)
              ·
                refine ⟨2390344797127884056102435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6374252792341024149606493 2390344797127884056102435)
                ·
                  refine ⟨3585517195691826084153653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390344797127884056102435 3585517195691826084153653)
                  ·
                    refine ⟨336142237096108695389405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3585517195691826084153653 336142237096108695389405)
                    ·
                      refine ⟨126053338911040760771027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 336142237096108695389405 126053338911040760771027)
                      ·
                        rfl

theorem cell23_245488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_245488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245488 prefixEnd_245488 := by exact prefixLift 245488
  have htrace : WordTrace (prefixWord ++ tailWord_245488) baseStart_245488 baseEnd_245488 := by
    simpa [prefixWord, tailWord_245488, baseEnd_245488] using wordTrace_append hprefix tailTrace_245488
  have hstable : (prefixWord ++ tailWord_245488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245488).length < 2 ^ (prefixWord ++ tailWord_245488).sum := by decide
  have hdescent : baseEnd_245488 < baseStart_245488 := by decide
  rcases family_descends (prefixWord ++ tailWord_245488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245525 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_245525 : Nat := 118140960795 + 245525 * 2 ^ 59
def prefixEnd_245525 : Nat := 4983230072969 + 3 ^ 40 * 245525 * 2
def baseEnd_245525 : Nat := 42024112565085705336119

theorem tailTrace_245525 : CollatzResearch.WordTrace tailWord_245525 prefixEnd_245525 42024112565085705336119 := by
  unfold tailWord_245525
  simp only [CollatzResearch.WordTrace]
  refine ⟨8955032435512332176706029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5970021623674888117804019 8955032435512332176706029)
  ·
    refine ⟨3358137163317124566264761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8955032435512332176706029 3358137163317124566264761)
    ·
      refine ⟨2518602872487843424698571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3358137163317124566264761 2518602872487843424698571)
      ·
        refine ⟨3777904308731765137047857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2518602872487843424698571 3777904308731765137047857)
        ·
          refine ⟨2833428231548823852785893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3777904308731765137047857 2833428231548823852785893)
          ·
            refine ⟨531267793415404472397355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2833428231548823852785893 531267793415404472397355)
            ·
              refine ⟨796901690123106708596033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531267793415404472397355 796901690123106708596033)
              ·
                refine ⟨597676267592330031447025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796901690123106708596033 597676267592330031447025)
                ·
                  refine ⟨448257200694247523585269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597676267592330031447025 448257200694247523585269)
                  ·
                    refine ⟨42024112565085705336119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 448257200694247523585269 42024112565085705336119)
                    ·
                      rfl

theorem cell23_245525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_245525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245525 prefixEnd_245525 := by exact prefixLift 245525
  have htrace : WordTrace (prefixWord ++ tailWord_245525) baseStart_245525 baseEnd_245525 := by
    simpa [prefixWord, tailWord_245525, baseEnd_245525] using wordTrace_append hprefix tailTrace_245525
  have hstable : (prefixWord ++ tailWord_245525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245525).length < 2 ^ (prefixWord ++ tailWord_245525).sum := by decide
  have hdescent : baseEnd_245525 < baseStart_245525 := by decide
  rcases family_descends (prefixWord ++ tailWord_245525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245562 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_245562 : Nat := 118140960795 + 245562 * 2 ^ 59
def prefixEnd_245562 : Nat := 4983230072969 + 3 ^ 40 * 245562 * 2
def baseEnd_245562 : Nat := 126091336479473471245687

theorem tailTrace_245562 : CollatzResearch.WordTrace tailWord_245562 prefixEnd_245562 126091336479473471245687 := by
  unfold tailWord_245562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239095484094571873950735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5970921290918858330535293 2239095484094571873950735)
  ·
    refine ⟨3358643226141857810926103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239095484094571873950735 3358643226141857810926103)
    ·
      refine ⟨5037964839212786716389155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358643226141857810926103 5037964839212786716389155)
      ·
        refine ⟨7556947258819180074583733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037964839212786716389155 7556947258819180074583733)
        ·
          refine ⟨708463805514298131992225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7556947258819180074583733 708463805514298131992225)
          ·
            refine ⟨531347854135723598994169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708463805514298131992225 531347854135723598994169)
            ·
              refine ⟨398510890601792699245627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531347854135723598994169 398510890601792699245627)
              ·
                refine ⟨597766335902689048868441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398510890601792699245627 597766335902689048868441)
                ·
                  refine ⟨448324751927016786651331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597766335902689048868441 448324751927016786651331)
                  ·
                    refine ⟨672487127890525179976997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 448324751927016786651331 672487127890525179976997)
                    ·
                      refine ⟨126091336479473471245687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 672487127890525179976997 126091336479473471245687)
                      ·
                        rfl

theorem cell23_245562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_245562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245562 prefixEnd_245562 := by exact prefixLift 245562
  have htrace : WordTrace (prefixWord ++ tailWord_245562) baseStart_245562 baseEnd_245562 := by
    simpa [prefixWord, tailWord_245562, baseEnd_245562] using wordTrace_append hprefix tailTrace_245562
  have hstable : (prefixWord ++ tailWord_245562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245562).length < 2 ^ (prefixWord ++ tailWord_245562).sum := by decide
  have hdescent : baseEnd_245562 < baseStart_245562 := by decide
  rcases family_descends (prefixWord ++ tailWord_245562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245585 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 6]
def baseStart_245585 : Nat := 118140960795 + 245585 * 2 ^ 59
def prefixEnd_245585 : Nat := 4983230072969 + 3 ^ 40 * 245585 * 2
def baseEnd_245585 : Nat := 14011460726058542362009

theorem tailTrace_245585 : CollatzResearch.WordTrace tailWord_245585 prefixEnd_245585 14011460726058542362009 := by
  unfold tailWord_245585
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957220815294962423890209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5971480543529974949260139 8957220815294962423890209)
  ·
    refine ⟨6717915611471221817917657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8957220815294962423890209 6717915611471221817917657)
    ·
      refine ⟨5038436708603416363438243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6717915611471221817917657 5038436708603416363438243)
      ·
        refine ⟨7557655062905124545157365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038436708603416363438243 7557655062905124545157365)
        ·
          refine ⟨708530162147355426108503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7557655062905124545157365 708530162147355426108503)
          ·
            refine ⟨1062795243221033139162755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708530162147355426108503 1062795243221033139162755)
            ·
              refine ⟨1594192864831549708744133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062795243221033139162755 1594192864831549708744133)
              ·
                refine ⟨298911162155915570389525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1594192864831549708744133 298911162155915570389525)
                ·
                  refine ⟨14011460726058542362009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 298911162155915570389525 14011460726058542362009)
                  ·
                    rfl

theorem cell23_245585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 6].length) (baseStart_245585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245585 prefixEnd_245585 := by exact prefixLift 245585
  have htrace : WordTrace (prefixWord ++ tailWord_245585) baseStart_245585 baseEnd_245585 := by
    simpa [prefixWord, tailWord_245585, baseEnd_245585] using wordTrace_append hprefix tailTrace_245585
  have hstable : (prefixWord ++ tailWord_245585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245585).length < 2 ^ (prefixWord ++ tailWord_245585).sum := by decide
  have hdescent : baseEnd_245585 < baseStart_245585 := by decide
  rcases family_descends (prefixWord ++ tailWord_245585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245589 : List Nat := [1, 3, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_245589 : Nat := 118140960795 + 245589 * 2 ^ 59
def prefixEnd_245589 : Nat := 4983230072969 + 3 ^ 40 * 245589 * 2
def baseEnd_245589 : Nat := 42035066819048288536021

theorem tailTrace_245589 : CollatzResearch.WordTrace tailWord_245589 prefixEnd_245589 42035066819048288536021 := by
  unfold tailWord_245589
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957366707280471107035821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5971577804853647404690547 8957366707280471107035821)
  ·
    refine ⟨3359012515230176665138433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8957366707280471107035821 3359012515230176665138433)
    ·
      refine ⟨2519259386422632498853825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3359012515230176665138433 2519259386422632498853825)
      ·
        refine ⟨1889444539816974374140369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2519259386422632498853825 1889444539816974374140369)
        ·
          refine ⟨1417083404862730780605277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1889444539816974374140369 1417083404862730780605277)
          ·
            refine ⟨531406276823524042726979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1417083404862730780605277 531406276823524042726979)
            ·
              refine ⟨797109415235286064090469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531406276823524042726979 797109415235286064090469)
              ·
                refine ⟨149458015356616137016963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797109415235286064090469 149458015356616137016963)
                ·
                  refine ⟨224187023034924205525445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149458015356616137016963 224187023034924205525445)
                  ·
                    refine ⟨42035066819048288536021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224187023034924205525445 42035066819048288536021)
                    ·
                      rfl

theorem cell23_245589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_245589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245589 prefixEnd_245589 := by exact prefixLift 245589
  have htrace : WordTrace (prefixWord ++ tailWord_245589) baseStart_245589 baseEnd_245589 := by
    simpa [prefixWord, tailWord_245589, baseEnd_245589] using wordTrace_append hprefix tailTrace_245589
  have hstable : (prefixWord ++ tailWord_245589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245589).length < 2 ^ (prefixWord ++ tailWord_245589).sum := by decide
  have hdescent : baseEnd_245589 < baseStart_245589 := by decide
  rcases family_descends (prefixWord ++ tailWord_245589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245602 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 6]
def baseStart_245602 : Nat := 118140960795 + 245602 * 2 ^ 59
def prefixEnd_245602 : Nat := 4983230072969 + 3 ^ 40 * 245602 * 2
def baseEnd_245602 : Nat := 14012430633961479416167

theorem tailTrace_245602 : CollatzResearch.WordTrace tailWord_245602 prefixEnd_245602 14012430633961479416167 := by
  unfold tailWord_245602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239460214058343581814765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5971893904155582884839373 2239460214058343581814765)
  ·
    refine ⟨839797580271878843180537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2239460214058343581814765 839797580271878843180537)
    ·
      refine ⟨629848185203909132385403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839797580271878843180537 629848185203909132385403)
      ·
        refine ⟨944772277805863698578105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629848185203909132385403 944772277805863698578105)
        ·
          refine ⟨708579208354397773933579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944772277805863698578105 708579208354397773933579)
          ·
            refine ⟨1062868812531596660900369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708579208354397773933579 1062868812531596660900369)
            ·
              refine ⟨797151609398697495675277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062868812531596660900369 797151609398697495675277)
              ·
                refine ⟨298931853524511560878229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 797151609398697495675277 298931853524511560878229)
                ·
                  refine ⟨14012430633961479416167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 298931853524511560878229 14012430633961479416167)
                  ·
                    rfl

theorem cell23_245602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_245602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245602 prefixEnd_245602 := by exact prefixLift 245602
  have htrace : WordTrace (prefixWord ++ tailWord_245602) baseStart_245602 baseEnd_245602 := by
    simpa [prefixWord, tailWord_245602, baseEnd_245602] using wordTrace_append hprefix tailTrace_245602
  have hstable : (prefixWord ++ tailWord_245602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245602).length < 2 ^ (prefixWord ++ tailWord_245602).sum := by decide
  have hdescent : baseEnd_245602 < baseStart_245602 := by decide
  rcases family_descends (prefixWord ++ tailWord_245602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245612 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_245612 : Nat := 118140960795 + 245612 * 2 ^ 59
def prefixEnd_245612 : Nat := 4983230072969 + 3 ^ 40 * 245612 * 2
def baseEnd_245612 : Nat := 126117010512198275620457

theorem tailTrace_245612 : CollatzResearch.WordTrace tailWord_245612 prefixEnd_245612 126117010512198275620457 := by
  unfold tailWord_245612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4479102793098573017561545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5972137057464764023415393 4479102793098573017561545)
  ·
    refine ⟨3359327094823929763171159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4479102793098573017561545 3359327094823929763171159)
    ·
      refine ⟨5038990642235894644756739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3359327094823929763171159 5038990642235894644756739)
      ·
        refine ⟨7558485963353841967135109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038990642235894644756739 7558485963353841967135109)
        ·
          refine ⟨1417216118128845368837833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7558485963353841967135109 1417216118128845368837833)
          ·
            refine ⟨1062912088596634026628375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417216118128845368837833 1062912088596634026628375)
            ·
              refine ⟨1594368132894951039942563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062912088596634026628375 1594368132894951039942563)
              ·
                refine ⟨2391552199342426559913845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594368132894951039942563 2391552199342426559913845)
                ·
                  refine ⟨224208018688352489991923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2391552199342426559913845 224208018688352489991923)
                  ·
                    refine ⟨336312028032528734987885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224208018688352489991923 336312028032528734987885)
                    ·
                      refine ⟨126117010512198275620457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 336312028032528734987885 126117010512198275620457)
                      ·
                        rfl

theorem cell23_245612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_245612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245612 prefixEnd_245612 := by exact prefixLift 245612
  have htrace : WordTrace (prefixWord ++ tailWord_245612) baseStart_245612 baseEnd_245612 := by
    simpa [prefixWord, tailWord_245612, baseEnd_245612] using wordTrace_append hprefix tailTrace_245612
  have hstable : (prefixWord ++ tailWord_245612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245612).length < 2 ^ (prefixWord ++ tailWord_245612).sum := by decide
  have hdescent : baseEnd_245612 < baseStart_245612 := by decide
  rcases family_descends (prefixWord ++ tailWord_245612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245655 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_245655 : Nat := 118140960795 + 245655 * 2 ^ 59
def prefixEnd_245655 : Nat := 4983230072969 + 3 ^ 40 * 245655 * 2
def baseEnd_245655 : Nat := 126139090180341607382759

theorem tailTrace_245655 : CollatzResearch.WordTrace tailWord_245655 prefixEnd_245655 126139090180341607382759 := by
  unfold tailWord_245655
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959773925041364378938419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5973182616694242919292279 8959773925041364378938419)
  ·
    refine ⟨13439660887562046568407629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8959773925041364378938419 13439660887562046568407629)
    ·
      refine ⟨5039872832835767463152861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13439660887562046568407629 5039872832835767463152861)
      ·
        refine ⟨1889952312313412798682323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5039872832835767463152861 1889952312313412798682323)
        ·
          refine ⟨2834928468470119198023485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889952312313412798682323 2834928468470119198023485)
          ·
            refine ⟨1063098175676294699258807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2834928468470119198023485 1063098175676294699258807)
            ·
              refine ⟨1594647263514442048888211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063098175676294699258807 1594647263514442048888211)
              ·
                refine ⟨2391970895271663073332317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594647263514442048888211 2391970895271663073332317)
                ·
                  refine ⟨896989085726873652499619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2391970895271663073332317 896989085726873652499619)
                  ·
                    refine ⟨1345483628590310478749429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 896989085726873652499619 1345483628590310478749429)
                    ·
                      refine ⟨126139090180341607382759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1345483628590310478749429 126139090180341607382759)
                      ·
                        rfl

theorem cell23_245655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_245655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245655 prefixEnd_245655 := by exact prefixLift 245655
  have htrace : WordTrace (prefixWord ++ tailWord_245655) baseStart_245655 baseEnd_245655 := by
    simpa [prefixWord, tailWord_245655, baseEnd_245655] using wordTrace_append hprefix tailTrace_245655
  have hstable : (prefixWord ++ tailWord_245655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245655).length < 2 ^ (prefixWord ++ tailWord_245655).sum := by decide
  have hdescent : baseEnd_245655 < baseStart_245655 := by decide
  rcases family_descends (prefixWord ++ tailWord_245655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245719 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_245719 : Nat := 118140960795 + 245719 * 2 ^ 59
def prefixEnd_245719 : Nat := 4983230072969 + 3 ^ 40 * 245719 * 2
def baseEnd_245719 : Nat := 126171952942229356982465

theorem tailTrace_245719 : CollatzResearch.WordTrace tailWord_245719 prefixEnd_245719 126171952942229356982465 := by
  unfold tailWord_245719
  simp only [CollatzResearch.WordTrace]
  refine ⟨8962108196809503309268211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5974738797873002206178807 8962108196809503309268211)
  ·
    refine ⟨13443162295214254963902317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8962108196809503309268211 13443162295214254963902317)
    ·
      refine ⟨5041185860705345611463369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13443162295214254963902317 5041185860705345611463369)
      ·
        refine ⟨3780889395529009208597527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5041185860705345611463369 3780889395529009208597527)
        ·
          refine ⟨5671334093293513812896291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780889395529009208597527 5671334093293513812896291)
          ·
            refine ⟨8507001139940270719344437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671334093293513812896291 8507001139940270719344437)
            ·
              refine ⟨797531356869400379938541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8507001139940270719344437 797531356869400379938541)
              ·
                refine ⟨299074258826025142476953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 797531356869400379938541 299074258826025142476953)
                ·
                  refine ⟨224305694119518856857715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299074258826025142476953 224305694119518856857715)
                  ·
                    refine ⟨336458541179278285286573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224305694119518856857715 336458541179278285286573)
                    ·
                      refine ⟨126171952942229356982465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 336458541179278285286573 126171952942229356982465)
                      ·
                        rfl

theorem cell23_245719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_245719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245719 prefixEnd_245719 := by exact prefixLift 245719
  have htrace : WordTrace (prefixWord ++ tailWord_245719) baseStart_245719 baseEnd_245719 := by
    simpa [prefixWord, tailWord_245719, baseEnd_245719] using wordTrace_append hprefix tailTrace_245719
  have hstable : (prefixWord ++ tailWord_245719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245719).length < 2 ^ (prefixWord ++ tailWord_245719).sum := by decide
  have hdescent : baseEnd_245719 < baseStart_245719 := by decide
  rcases family_descends (prefixWord ++ tailWord_245719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245759 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 4, 2, 2]
def baseStart_245759 : Nat := 118140960795 + 245759 * 2 ^ 59
def prefixEnd_245759 : Nat := 4983230072969 + 3 ^ 40 * 245759 * 2
def baseEnd_245759 : Nat := 126192492168409200482281

theorem tailTrace_245759 : CollatzResearch.WordTrace tailWord_245759 prefixEnd_245759 126192492168409200482281 := by
  unfold tailWord_245759
  simp only [CollatzResearch.WordTrace]
  refine ⟨8963567116664590140724331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5975711411109726760482887 8963567116664590140724331)
  ·
    refine ⟨13445350674996885211086497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8963567116664590140724331 13445350674996885211086497)
    ·
      refine ⟨10084013006247663908314873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13445350674996885211086497 10084013006247663908314873)
      ·
        refine ⟨7563009754685747931236155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10084013006247663908314873 7563009754685747931236155)
        ·
          refine ⟨11344514632028621896854233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563009754685747931236155 11344514632028621896854233)
          ·
            refine ⟨8508385974021466422640675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11344514632028621896854233 8508385974021466422640675)
            ·
              refine ⟨12762578961032199633961013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8508385974021466422640675 12762578961032199633961013)
              ·
                refine ⟨1196491777596768715683845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12762578961032199633961013 1196491777596768715683845)
                ·
                  refine ⟨224342208299394134190721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1196491777596768715683845 224342208299394134190721)
                  ·
                    refine ⟨168256656224545600643041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224342208299394134190721 168256656224545600643041)
                    ·
                      refine ⟨126192492168409200482281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 168256656224545600643041 126192492168409200482281)
                      ·
                        rfl

theorem cell23_245759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_245759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245759 prefixEnd_245759 := by exact prefixLift 245759
  have htrace : WordTrace (prefixWord ++ tailWord_245759) baseStart_245759 baseEnd_245759 := by
    simpa [prefixWord, tailWord_245759, baseEnd_245759] using wordTrace_append hprefix tailTrace_245759
  have hstable : (prefixWord ++ tailWord_245759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245759).length < 2 ^ (prefixWord ++ tailWord_245759).sum := by decide
  have hdescent : baseEnd_245759 < baseStart_245759 := by decide
  rcases family_descends (prefixWord ++ tailWord_245759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245772 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_245772 : Nat := 118140960795 + 245772 * 2 ^ 59
def prefixEnd_245772 : Nat := 4983230072969 + 3 ^ 40 * 245772 * 2
def baseEnd_245772 : Nat := 126199167416917649619721

theorem tailTrace_245772 : CollatzResearch.WordTrace tailWord_245772 prefixEnd_245772 126199167416917649619721 := by
  unfold tailWord_245772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4482020632808746680473785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5976027510411662240631713 4482020632808746680473785)
  ·
    refine ⟨3361515474606560010355339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4482020632808746680473785 3361515474606560010355339)
    ·
      refine ⟨5042273211909840015533009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3361515474606560010355339 5042273211909840015533009)
      ·
        refine ⟨3781704908932380011649757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5042273211909840015533009 3781704908932380011649757)
        ·
          refine ⟨1418139340849642504368659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3781704908932380011649757 1418139340849642504368659)
          ·
            refine ⟨2127209011274463756552989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418139340849642504368659 2127209011274463756552989)
            ·
              refine ⟨797703379227923908707371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2127209011274463756552989 797703379227923908707371)
              ·
                refine ⟨1196555068841885863061057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797703379227923908707371 1196555068841885863061057)
                ·
                  refine ⟨897416301631414397295793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1196555068841885863061057 897416301631414397295793)
                  ·
                    refine ⟨673062226223560797971845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 897416301631414397295793 673062226223560797971845)
                    ·
                      refine ⟨126199167416917649619721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 673062226223560797971845 126199167416917649619721)
                      ·
                        rfl

theorem cell23_245772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_245772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245772 prefixEnd_245772 := by exact prefixLift 245772
  have htrace : WordTrace (prefixWord ++ tailWord_245772) baseStart_245772 baseEnd_245772 := by
    simpa [prefixWord, tailWord_245772, baseEnd_245772] using wordTrace_append hprefix tailTrace_245772
  have hstable : (prefixWord ++ tailWord_245772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245772).length < 2 ^ (prefixWord ++ tailWord_245772).sum := by decide
  have hdescent : baseEnd_245772 < baseStart_245772 := by decide
  rcases family_descends (prefixWord ++ tailWord_245772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245832 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_245832 : Nat := 118140960795 + 245832 * 2 ^ 59
def prefixEnd_245832 : Nat := 4983230072969 + 3 ^ 40 * 245832 * 2
def baseEnd_245832 : Nat := 126229976256187414869445

theorem tailTrace_245832 : CollatzResearch.WordTrace tailWord_245832 prefixEnd_245832 126229976256187414869445 := by
  unfold tailWord_245832
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483114822700061804065875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5977486430266749072087833 4483114822700061804065875)
  ·
    refine ⟨6724672234050092706098813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483114822700061804065875 6724672234050092706098813)
    ·
      refine ⟨2521752087768784764787055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6724672234050092706098813 2521752087768784764787055)
      ·
        refine ⟨3782628131653177147180583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521752087768784764787055 3782628131653177147180583)
        ·
          refine ⟨5673942197479765720770875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782628131653177147180583 5673942197479765720770875)
          ·
            refine ⟨8510913296219648581156313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673942197479765720770875 8510913296219648581156313)
            ·
              refine ⟨6383184972164736435867235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8510913296219648581156313 6383184972164736435867235)
              ·
                refine ⟨9574777458247104653800853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383184972164736435867235 9574777458247104653800853)
                ·
                  refine ⟨448817693355333030646915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9574777458247104653800853 448817693355333030646915)
                  ·
                    refine ⟨673226540032999545970373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 448817693355333030646915 673226540032999545970373)
                    ·
                      refine ⟨126229976256187414869445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 673226540032999545970373 126229976256187414869445)
                      ·
                        rfl

theorem cell23_245832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_245832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245832 prefixEnd_245832 := by exact prefixLift 245832
  have htrace : WordTrace (prefixWord ++ tailWord_245832) baseStart_245832 baseEnd_245832 := by
    simpa [prefixWord, tailWord_245832, baseEnd_245832] using wordTrace_append hprefix tailTrace_245832
  have hstable : (prefixWord ++ tailWord_245832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245832).length < 2 ^ (prefixWord ++ tailWord_245832).sum := by decide
  have hdescent : baseEnd_245832 < baseStart_245832 := by decide
  rcases family_descends (prefixWord ++ tailWord_245832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245846 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_245846 : Nat := 118140960795 + 245846 * 2 ^ 59
def prefixEnd_245846 : Nat := 4983230072969 + 3 ^ 40 * 245846 * 2
def baseEnd_245846 : Nat := 42079054995116786698127

theorem tailTrace_245846 : CollatzResearch.WordTrace tailWord_245846 prefixEnd_245846 42079054995116786698127 := by
  unfold tailWord_245846
  simp only [CollatzResearch.WordTrace]
  refine ⟨560421266709337749946337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5977826844899602666094261 560421266709337749946337)
  ·
    refine ⟨420315950032003312459753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 560421266709337749946337 420315950032003312459753)
    ·
      refine ⟨315236962524002484344815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420315950032003312459753 315236962524002484344815)
      ·
        refine ⟨472855443786003726517223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315236962524002484344815 472855443786003726517223)
        ·
          refine ⟨709283165679005589775835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472855443786003726517223 709283165679005589775835)
          ·
            refine ⟨1063924748518508384663753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709283165679005589775835 1063924748518508384663753)
            ·
              refine ⟨797943561388881288497815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063924748518508384663753 797943561388881288497815)
              ·
                refine ⟨1196915342083321932746723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797943561388881288497815 1196915342083321932746723)
                ·
                  refine ⟨1795373013124982899120085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196915342083321932746723 1795373013124982899120085)
                  ·
                    refine ⟨42079054995116786698127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1795373013124982899120085 42079054995116786698127)
                    ·
                      rfl

theorem cell23_245846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_245846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245846 prefixEnd_245846 := by exact prefixLift 245846
  have htrace : WordTrace (prefixWord ++ tailWord_245846) baseStart_245846 baseEnd_245846 := by
    simpa [prefixWord, tailWord_245846, baseEnd_245846] using wordTrace_append hprefix tailTrace_245846
  have hstable : (prefixWord ++ tailWord_245846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245846).length < 2 ^ (prefixWord ++ tailWord_245846).sum := by decide
  have hdescent : baseEnd_245846 < baseStart_245846 := by decide
  rcases family_descends (prefixWord ++ tailWord_245846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245866 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_245866 : Nat := 118140960795 + 245866 * 2 ^ 59
def prefixEnd_245866 : Nat := 4983230072969 + 3 ^ 40 * 245866 * 2
def baseEnd_245866 : Nat := 126247434598440281844289

theorem tailTrace_245866 : CollatzResearch.WordTrace tailWord_245866 prefixEnd_245866 126247434598440281844289 := by
  unfold tailWord_245866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241867431819236853717363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5978313151517964943246301 2241867431819236853717363)
  ·
    refine ⟨3362801147728855280576045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2241867431819236853717363 3362801147728855280576045)
    ·
      refine ⟨1261050430398320730216017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3362801147728855280576045 1261050430398320730216017)
      ·
        refine ⟨945787822798740547662013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1261050430398320730216017 945787822798740547662013)
        ·
          refine ⟨354670433549527705373255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 945787822798740547662013 354670433549527705373255)
          ·
            refine ⟨532005650324291558059883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354670433549527705373255 532005650324291558059883)
            ·
              refine ⟨798008475486437337089825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532005650324291558059883 798008475486437337089825)
              ·
                refine ⟨598506356614828002817369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798008475486437337089825 598506356614828002817369)
                ·
                  refine ⟨448879767461121002113027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598506356614828002817369 448879767461121002113027)
                  ·
                    refine ⟨673319651191681503169541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 448879767461121002113027 673319651191681503169541)
                    ·
                      refine ⟨126247434598440281844289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 673319651191681503169541 126247434598440281844289)
                      ·
                        rfl

theorem cell23_245866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_245866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245866 prefixEnd_245866 := by exact prefixLift 245866
  have htrace : WordTrace (prefixWord ++ tailWord_245866) baseStart_245866 baseEnd_245866 := by
    simpa [prefixWord, tailWord_245866, baseEnd_245866] using wordTrace_append hprefix tailTrace_245866
  have hstable : (prefixWord ++ tailWord_245866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245866).length < 2 ^ (prefixWord ++ tailWord_245866).sum := by decide
  have hdescent : baseEnd_245866 < baseStart_245866 := by decide
  rcases family_descends (prefixWord ++ tailWord_245866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245872 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 8]
def baseStart_245872 : Nat := 118140960795 + 245872 * 2 ^ 59
def prefixEnd_245872 : Nat := 4983230072969 + 3 ^ 40 * 245872 * 2
def baseEnd_245872 : Nat := 14027835053596362041029

theorem tailTrace_245872 : CollatzResearch.WordTrace tailWord_245872 prefixEnd_245872 14027835053596362041029 := by
  unfold tailWord_245872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483844282627605219793935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5978459043503473626391913 4483844282627605219793935)
  ·
    refine ⟨6725766423941407829690903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483844282627605219793935 6725766423941407829690903)
    ·
      refine ⟨10088649635912111744536355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725766423941407829690903 10088649635912111744536355)
      ·
        refine ⟨15132974453868167616804533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10088649635912111744536355 15132974453868167616804533)
        ·
          refine ⟨1418716355050140714075425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15132974453868167616804533 1418716355050140714075425)
          ·
            refine ⟨1064037266287605535556569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418716355050140714075425 1064037266287605535556569)
            ·
              refine ⟨798027949715704151667427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064037266287605535556569 798027949715704151667427)
              ·
                refine ⟨1197041924573556227501141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798027949715704151667427 1197041924573556227501141)
                ·
                  refine ⟨14027835053596362041029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1197041924573556227501141 14027835053596362041029)
                  ·
                    rfl

theorem cell23_245872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_245872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245872 prefixEnd_245872 := by exact prefixLift 245872
  have htrace : WordTrace (prefixWord ++ tailWord_245872) baseStart_245872 baseEnd_245872 := by
    simpa [prefixWord, tailWord_245872, baseEnd_245872] using wordTrace_append hprefix tailTrace_245872
  have hstable : (prefixWord ++ tailWord_245872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245872).length < 2 ^ (prefixWord ++ tailWord_245872).sum := by decide
  have hdescent : baseEnd_245872 < baseStart_245872 := by decide
  rcases family_descends (prefixWord ++ tailWord_245872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245927 : List Nat := [1, 1, 6, 2, 2, 2, 2, 2, 1, 4]
def baseStart_245927 : Nat := 118140960795 + 245927 * 2 ^ 59
def prefixEnd_245927 : Nat := 4983230072969 + 3 ^ 40 * 245927 * 2
def baseEnd_245927 : Nat := 42092918972788181060503

theorem tailTrace_245927 : CollatzResearch.WordTrace tailWord_245927 prefixEnd_245927 42092918972788181060503 := by
  unfold tailWord_245927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969694580055954832840035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5979796386703969888560023 8969694580055954832840035)
  ·
    refine ⟨13454541870083932249260053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8969694580055954832840035 13454541870083932249260053)
    ·
      refine ⟨630681650160184324184065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13454541870083932249260053 630681650160184324184065)
      ·
        refine ⟨473011237620138243138049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630681650160184324184065 473011237620138243138049)
        ·
          refine ⟨354758428215103682353537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473011237620138243138049 354758428215103682353537)
          ·
            refine ⟨266068821161327761765153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354758428215103682353537 266068821161327761765153)
            ·
              refine ⟨199551615870995821323865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266068821161327761765153 199551615870995821323865)
              ·
                refine ⟨149663711903246865992899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199551615870995821323865 149663711903246865992899)
                ·
                  refine ⟨224495567854870298989349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149663711903246865992899 224495567854870298989349)
                  ·
                    refine ⟨42092918972788181060503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224495567854870298989349 42092918972788181060503)
                    ·
                      rfl

theorem cell23_245927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_245927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245927 prefixEnd_245927 := by exact prefixLift 245927
  have htrace : WordTrace (prefixWord ++ tailWord_245927) baseStart_245927 baseEnd_245927 := by
    simpa [prefixWord, tailWord_245927, baseEnd_245927] using wordTrace_append hprefix tailTrace_245927
  have hstable : (prefixWord ++ tailWord_245927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245927).length < 2 ^ (prefixWord ++ tailWord_245927).sum := by decide
  have hdescent : baseEnd_245927 < baseStart_245927 := by decide
  rcases family_descends (prefixWord ++ tailWord_245927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245939 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 2, 6, 2]
def baseStart_245939 : Nat := 118140960795 + 245939 * 2 ^ 59
def prefixEnd_245939 : Nat := 4983230072969 + 3 ^ 40 * 245939 * 2
def baseEnd_245939 : Nat := 126284918686218496231453

theorem tailTrace_245939 : CollatzResearch.WordTrace tailWord_245939 prefixEnd_245939 126284918686218496231453 := by
  unfold tailWord_245939
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970132256012480882276871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5980088170674987254851247 8970132256012480882276871)
  ·
    refine ⟨13455198384018721323415307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8970132256012480882276871 13455198384018721323415307)
    ·
      refine ⟨20182797576028081985122961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455198384018721323415307 20182797576028081985122961)
      ·
        refine ⟨15137098182021061488842221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20182797576028081985122961 15137098182021061488842221)
        ·
          refine ⟨5676411818257898058315833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15137098182021061488842221 5676411818257898058315833)
          ·
            refine ⟨4257308863693423543736875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5676411818257898058315833 4257308863693423543736875)
            ·
              refine ⟨6385963295540135315605313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257308863693423543736875 6385963295540135315605313)
              ·
                refine ⟨4789472471655101486703985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6385963295540135315605313 4789472471655101486703985)
                ·
                  refine ⟨3592104353741326115027989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4789472471655101486703985 3592104353741326115027989)
                  ·
                    refine ⟨168379891581624661641937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3592104353741326115027989 168379891581624661641937)
                    ·
                      refine ⟨126284918686218496231453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 168379891581624661641937 126284918686218496231453)
                      ·
                        rfl

theorem cell23_245939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6, 2].length) (baseStart_245939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245939 prefixEnd_245939 := by exact prefixLift 245939
  have htrace : WordTrace (prefixWord ++ tailWord_245939) baseStart_245939 baseEnd_245939 := by
    simpa [prefixWord, tailWord_245939, baseEnd_245939] using wordTrace_append hprefix tailTrace_245939
  have hstable : (prefixWord ++ tailWord_245939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245939).length < 2 ^ (prefixWord ++ tailWord_245939).sum := by decide
  have hdescent : baseEnd_245939 < baseStart_245939 := by decide
  rcases family_descends (prefixWord ++ tailWord_245939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245949 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_245949 : Nat := 118140960795 + 245949 * 2 ^ 59
def prefixEnd_245949 : Nat := 4983230072969 + 3 ^ 40 * 245949 * 2
def baseEnd_245949 : Nat := 42096684497587819035469

theorem tailTrace_245949 : CollatzResearch.WordTrace tailWord_245949 prefixEnd_245949 42096684497587819035469 := by
  unfold tailWord_245949
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970496985976252590140901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5980331323984168393427267 8970496985976252590140901)
  ·
    refine ⟨1681968184870547360651419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8970496985976252590140901 1681968184870547360651419)
    ·
      refine ⟨2522952277305821040977129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681968184870547360651419 2522952277305821040977129)
      ·
        refine ⟨1892214207979365780732847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2522952277305821040977129 1892214207979365780732847)
        ·
          refine ⟨2838321311969048671099271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892214207979365780732847 2838321311969048671099271)
          ·
            refine ⟨4257481967953573006648907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838321311969048671099271 4257481967953573006648907)
            ·
              refine ⟨6386222951930359509973361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257481967953573006648907 6386222951930359509973361)
              ·
                refine ⟨4789667213947769632480021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386222951930359509973361 4789667213947769632480021)
                ·
                  refine ⟨224515650653801701522501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4789667213947769632480021 224515650653801701522501)
                  ·
                    refine ⟨42096684497587819035469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224515650653801701522501 42096684497587819035469)
                    ·
                      rfl

theorem cell23_245949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_245949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245949 prefixEnd_245949 := by exact prefixLift 245949
  have htrace : WordTrace (prefixWord ++ tailWord_245949) baseStart_245949 baseEnd_245949 := by
    simpa [prefixWord, tailWord_245949, baseEnd_245949] using wordTrace_append hprefix tailTrace_245949
  have hstable : (prefixWord ++ tailWord_245949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245949).length < 2 ^ (prefixWord ++ tailWord_245949).sum := by decide
  have hdescent : baseEnd_245949 < baseStart_245949 := by decide
  rcases family_descends (prefixWord ++ tailWord_245949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245956 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_245956 : Nat := 118140960795 + 245956 * 2 ^ 59
def prefixEnd_245956 : Nat := 4983230072969 + 3 ^ 40 * 245956 * 2
def baseEnd_245956 : Nat := 126293647857344929718875

theorem tailTrace_245956 : CollatzResearch.WordTrace tailWord_245956 prefixEnd_245956 126293647857344929718875 := by
  unfold tailWord_245956
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485376148475446392822861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5980501531300595190430481 4485376148475446392822861)
  ·
    refine ⟨1682016055678292397308573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4485376148475446392822861 1682016055678292397308573)
    ·
      refine ⟨630756020879359648990715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1682016055678292397308573 630756020879359648990715)
      ·
        refine ⟨946134031319039473486073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630756020879359648990715 946134031319039473486073)
        ·
          refine ⟨709600523489279605114555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946134031319039473486073 709600523489279605114555)
          ·
            refine ⟨1064400785233919407671833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709600523489279605114555 1064400785233919407671833)
            ·
              refine ⟨798300588925439555753875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064400785233919407671833 798300588925439555753875)
              ·
                refine ⟨1197450883388159333630813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798300588925439555753875 1197450883388159333630813)
                ·
                  refine ⟨449044081270559750111555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197450883388159333630813 449044081270559750111555)
                  ·
                    refine ⟨673566121905839625167333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 449044081270559750111555 673566121905839625167333)
                    ·
                      refine ⟨126293647857344929718875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 673566121905839625167333 126293647857344929718875)
                      ·
                        rfl

theorem cell23_245956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_245956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245956 prefixEnd_245956 := by exact prefixLift 245956
  have htrace : WordTrace (prefixWord ++ tailWord_245956) baseStart_245956 baseEnd_245956 := by
    simpa [prefixWord, tailWord_245956, baseEnd_245956] using wordTrace_append hprefix tailTrace_245956
  have hstable : (prefixWord ++ tailWord_245956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245956).length < 2 ^ (prefixWord ++ tailWord_245956).sum := by decide
  have hdescent : baseEnd_245956 < baseStart_245956 := by decide
  rcases family_descends (prefixWord ++ tailWord_245956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245969 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_245969 : Nat := 118140960795 + 245969 * 2 ^ 59
def prefixEnd_245969 : Nat := 4983230072969 + 3 ^ 40 * 245969 * 2
def baseEnd_245969 : Nat := 126300323105853378856315

theorem tailTrace_245969 : CollatzResearch.WordTrace tailWord_245969 prefixEnd_245969 126300323105853378856315 := by
  unfold tailWord_245969
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971226445903796005868961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5980817630602530670579307 8971226445903796005868961)
  ·
    refine ⟨6728419834427847004401721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8971226445903796005868961 6728419834427847004401721)
    ·
      refine ⟨5046314875820885253301291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6728419834427847004401721 5046314875820885253301291)
      ·
        refine ⟨7569472313731327879951937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5046314875820885253301291 7569472313731327879951937)
        ·
          refine ⟨5677104235298495909963953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7569472313731327879951937 5677104235298495909963953)
          ·
            refine ⟨4257828176473871932472965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5677104235298495909963953 4257828176473871932472965)
            ·
              refine ⟨798342783088850987338681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4257828176473871932472965 798342783088850987338681)
              ·
                refine ⟨598757087316638240504011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798342783088850987338681 598757087316638240504011)
                ·
                  refine ⟨898135630974957360756017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598757087316638240504011 898135630974957360756017)
                  ·
                    refine ⟨673601723231218020567013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 898135630974957360756017 673601723231218020567013)
                    ·
                      refine ⟨126300323105853378856315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 673601723231218020567013 126300323105853378856315)
                      ·
                        rfl

theorem cell23_245969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_245969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245969 prefixEnd_245969 := by exact prefixLift 245969
  have htrace : WordTrace (prefixWord ++ tailWord_245969) baseStart_245969 baseEnd_245969 := by
    simpa [prefixWord, tailWord_245969, baseEnd_245969] using wordTrace_append hprefix tailTrace_245969
  have hstable : (prefixWord ++ tailWord_245969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245969).length < 2 ^ (prefixWord ++ tailWord_245969).sum := by decide
  have hdescent : baseEnd_245969 < baseStart_245969 := by decide
  rcases family_descends (prefixWord ++ tailWord_245969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245973 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_245973 : Nat := 118140960795 + 245973 * 2 ^ 59
def prefixEnd_245973 : Nat := 4983230072969 + 3 ^ 40 * 245973 * 2
def baseEnd_245973 : Nat := 126302377028471363206297

theorem tailTrace_245973 : CollatzResearch.WordTrace tailWord_245973 prefixEnd_245973 126302377028471363206297 := by
  unfold tailWord_245973
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971372337889304689014573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5980914891926203126009715 8971372337889304689014573)
  ·
    refine ⟨3364264626708489258380465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8971372337889304689014573 3364264626708489258380465)
    ·
      refine ⟨2523198470031366943785349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3364264626708489258380465 2523198470031366943785349)
      ·
        refine ⟨473099713130881301959753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2523198470031366943785349 473099713130881301959753)
        ·
          refine ⟨354824784848160976469815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473099713130881301959753 354824784848160976469815)
          ·
            refine ⟨532237177272241464704723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354824784848160976469815 532237177272241464704723)
            ·
              refine ⟨798355765908362197057085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532237177272241464704723 798355765908362197057085)
              ·
                refine ⟨299383412215635823896407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 798355765908362197057085 299383412215635823896407)
                ·
                  refine ⟨449075118323453735844611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299383412215635823896407 449075118323453735844611)
                  ·
                    refine ⟨673612677485180603766917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 449075118323453735844611 673612677485180603766917)
                    ·
                      refine ⟨126302377028471363206297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 673612677485180603766917 126302377028471363206297)
                      ·
                        rfl

theorem cell23_245973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_245973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_245973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_245973 prefixEnd_245973 := by exact prefixLift 245973
  have htrace : WordTrace (prefixWord ++ tailWord_245973) baseStart_245973 baseEnd_245973 := by
    simpa [prefixWord, tailWord_245973, baseEnd_245973] using wordTrace_append hprefix tailTrace_245973
  have hstable : (prefixWord ++ tailWord_245973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245973).length < 2 ^ (prefixWord ++ tailWord_245973).sum := by decide
  have hdescent : baseEnd_245973 < baseStart_245973 := by decide
  rcases family_descends (prefixWord ++ tailWord_245973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246016 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 3, 3, 2]
def baseStart_246016 : Nat := 118140960795 + 246016 * 2 ^ 59
def prefixEnd_246016 : Nat := 4983230072969 + 3 ^ 40 * 246016 * 2
def baseEnd_246016 : Nat := 126324456696614694968599

theorem tailTrace_246016 : CollatzResearch.WordTrace tailWord_246016 prefixEnd_246016 126324456696614694968599 := by
  unfold tailWord_246016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486470338366761516414951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5981960451155682021886601 4486470338366761516414951)
  ·
    refine ⟨6729705507550142274622427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4486470338366761516414951 6729705507550142274622427)
    ·
      refine ⟨10094558261325213411933641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729705507550142274622427 10094558261325213411933641)
      ·
        refine ⟨7570918695993910058950231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10094558261325213411933641 7570918695993910058950231)
        ·
          refine ⟨11356378043990865088425347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7570918695993910058950231 11356378043990865088425347)
          ·
            refine ⟨17034567065986297632638021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11356378043990865088425347 17034567065986297632638021)
            ·
              refine ⟨3193981324872430806119629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17034567065986297632638021 3193981324872430806119629)
              ·
                refine ⟨1197742996827161552294861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3193981324872430806119629 1197742996827161552294861)
                ·
                  refine ⟨449153623810185582110573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197742996827161552294861 449153623810185582110573)
                  ·
                    refine ⟨168432608928819593291465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449153623810185582110573 168432608928819593291465)
                    ·
                      refine ⟨126324456696614694968599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 168432608928819593291465 126324456696614694968599)
                      ·
                        rfl

theorem cell23_246016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_246016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246016 prefixEnd_246016 := by exact prefixLift 246016
  have htrace : WordTrace (prefixWord ++ tailWord_246016) baseStart_246016 baseEnd_246016 := by
    simpa [prefixWord, tailWord_246016, baseEnd_246016] using wordTrace_append hprefix tailTrace_246016
  have hstable : (prefixWord ++ tailWord_246016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246016).length < 2 ^ (prefixWord ++ tailWord_246016).sum := by decide
  have hdescent : baseEnd_246016 < baseStart_246016 := by decide
  rcases family_descends (prefixWord ++ tailWord_246016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246033 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 1, 3, 2]
def baseStart_246033 : Nat := 118140960795 + 246033 * 2 ^ 59
def prefixEnd_246033 : Nat := 4983230072969 + 3 ^ 40 * 246033 * 2
def baseEnd_246033 : Nat := 126333185867741128456021

theorem tailTrace_246033 : CollatzResearch.WordTrace tailWord_246033 prefixEnd_246033 126333185867741128456021 := by
  unfold tailWord_246033
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973560717671934936198753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5982373811781289957465835 8973560717671934936198753)
  ·
    refine ⟨6730170538253951202149065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8973560717671934936198753 6730170538253951202149065)
    ·
      refine ⟨5047627903690463401611799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6730170538253951202149065 5047627903690463401611799)
      ·
        refine ⟨7571441855535695102417699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5047627903690463401611799 7571441855535695102417699)
        ·
          refine ⟨11357162783303542653626549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7571441855535695102417699 11357162783303542653626549)
          ·
            refine ⟨1064734010934707123777489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11357162783303542653626549 1064734010934707123777489)
            ·
              refine ⟨798550508201030342833117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064734010934707123777489 798550508201030342833117)
              ·
                refine ⟨299456440575386378562419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 798550508201030342833117 299456440575386378562419)
                ·
                  refine ⟨449184660863079567843629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299456440575386378562419 449184660863079567843629)
                  ·
                    refine ⟨168444247823654837941361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449184660863079567843629 168444247823654837941361)
                    ·
                      refine ⟨126333185867741128456021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 168444247823654837941361 126333185867741128456021)
                      ·
                        rfl

theorem cell23_246033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_246033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246033 prefixEnd_246033 := by exact prefixLift 246033
  have htrace : WordTrace (prefixWord ++ tailWord_246033) baseStart_246033 baseEnd_246033 := by
    simpa [prefixWord, tailWord_246033, baseEnd_246033] using wordTrace_append hprefix tailTrace_246033
  have hstable : (prefixWord ++ tailWord_246033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246033).length < 2 ^ (prefixWord ++ tailWord_246033).sum := by decide
  have hdescent : baseEnd_246033 < baseStart_246033 := by decide
  rcases family_descends (prefixWord ++ tailWord_246033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246069 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 9]
def baseStart_246069 : Nat := 118140960795 + 246069 * 2 ^ 59
def prefixEnd_246069 : Nat := 4983230072969 + 3 ^ 40 * 246069 * 2
def baseEnd_246069 : Nat := 14039074574589220845095

theorem tailTrace_246069 : CollatzResearch.WordTrace tailWord_246069 prefixEnd_246069 14039074574589220845095 := by
  unfold tailWord_246069
  simp only [CollatzResearch.WordTrace]
  refine ⟨8974873745541513084509261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5983249163694342056339507 8974873745541513084509261)
  ·
    refine ⟨3365577654578067406690973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8974873745541513084509261 3365577654578067406690973)
    ·
      refine ⟨1262091620466775277509115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3365577654578067406690973 1262091620466775277509115)
      ·
        refine ⟨1893137430700162916263673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262091620466775277509115 1893137430700162916263673)
        ·
          refine ⟨1419853073025122187197755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1893137430700162916263673 1419853073025122187197755)
          ·
            refine ⟨2129779609537683280796633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419853073025122187197755 2129779609537683280796633)
            ·
              refine ⟨1597334707153262460597475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2129779609537683280796633 1597334707153262460597475)
              ·
                refine ⟨2396002060729893690896213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597334707153262460597475 2396002060729893690896213)
                ·
                  refine ⟨14039074574589220845095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2396002060729893690896213 14039074574589220845095)
                  ·
                    rfl

theorem cell23_246069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_246069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246069 prefixEnd_246069 := by exact prefixLift 246069
  have htrace : WordTrace (prefixWord ++ tailWord_246069) baseStart_246069 baseEnd_246069 := by
    simpa [prefixWord, tailWord_246069, baseEnd_246069] using wordTrace_append hprefix tailTrace_246069
  have hstable : (prefixWord ++ tailWord_246069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246069).length < 2 ^ (prefixWord ++ tailWord_246069).sum := by decide
  have hdescent : baseEnd_246069 < baseStart_246069 := by decide
  rcases family_descends (prefixWord ++ tailWord_246069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246084 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_246084 : Nat := 118140960795 + 246084 * 2 ^ 59
def prefixEnd_246084 : Nat := 4983230072969 + 3 ^ 40 * 246084 * 2
def baseEnd_246084 : Nat := 126359373381120428918287

theorem tailTrace_246084 : CollatzResearch.WordTrace tailWord_246084 prefixEnd_246084 126359373381120428918287 := by
  unfold tailWord_246084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487710420243585323152653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5983613893658113764203537 4487710420243585323152653)
  ·
    refine ⟨1682891407591344496182245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4487710420243585323152653 1682891407591344496182245)
    ·
      refine ⟨315542138923377093034171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1682891407591344496182245 315542138923377093034171)
      ·
        refine ⟨473313208385065639551257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315542138923377093034171 473313208385065639551257)
        ·
          refine ⟨354984906288799229663443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473313208385065639551257 354984906288799229663443)
          ·
            refine ⟨532477359433198844495165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354984906288799229663443 532477359433198844495165)
            ·
              refine ⟨199679009787449566685687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532477359433198844495165 199679009787449566685687)
              ·
                refine ⟨299518514681174350028531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199679009787449566685687 299518514681174350028531)
                ·
                  refine ⟨449277772021761525042797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299518514681174350028531 449277772021761525042797)
                  ·
                    refine ⟨168479164508160571891049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449277772021761525042797 168479164508160571891049)
                    ·
                      refine ⟨126359373381120428918287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 168479164508160571891049 126359373381120428918287)
                      ·
                        rfl

theorem cell23_246084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_246084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246084 prefixEnd_246084 := by exact prefixLift 246084
  have htrace : WordTrace (prefixWord ++ tailWord_246084) baseStart_246084 baseEnd_246084 := by
    simpa [prefixWord, tailWord_246084, baseEnd_246084] using wordTrace_append hprefix tailTrace_246084
  have hstable : (prefixWord ++ tailWord_246084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246084).length < 2 ^ (prefixWord ++ tailWord_246084).sum := by decide
  have hdescent : baseEnd_246084 < baseStart_246084 := by decide
  rcases family_descends (prefixWord ++ tailWord_246084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246099 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 4, 5]
def baseStart_246099 : Nat := 118140960795 + 246099 * 2 ^ 59
def prefixEnd_246099 : Nat := 4983230072969 + 3 ^ 40 * 246099 * 2
def baseEnd_246099 : Nat := 42122358530312623410239

theorem tailTrace_246099 : CollatzResearch.WordTrace tailWord_246099 prefixEnd_246099 42122358530312623410239 := by
  unfold tailWord_246099
  simp only [CollatzResearch.WordTrace]
  refine ⟨8975967935432828208101351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5983978623621885472067567 8975967935432828208101351)
  ·
    refine ⟨13463951903149242312152027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8975967935432828208101351 13463951903149242312152027)
    ·
      refine ⟨20195927854723863468228041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463951903149242312152027 20195927854723863468228041)
      ·
        refine ⟨15146945891042897601171031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20195927854723863468228041 15146945891042897601171031)
        ·
          refine ⟨22720418836564346401756547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15146945891042897601171031 22720418836564346401756547)
          ·
            refine ⟨34080628254846519602634821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22720418836564346401756547 34080628254846519602634821)
            ·
              refine ⟨6390117797783722425494029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34080628254846519602634821 6390117797783722425494029)
              ·
                refine ⟨2396294174168895909560261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6390117797783722425494029 2396294174168895909560261)
                ·
                  refine ⟨449305157656667983042549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396294174168895909560261 449305157656667983042549)
                  ·
                    refine ⟨42122358530312623410239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 449305157656667983042549 42122358530312623410239)
                    ·
                      rfl

theorem cell23_246099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 5].length) (baseStart_246099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246099 prefixEnd_246099 := by exact prefixLift 246099
  have htrace : WordTrace (prefixWord ++ tailWord_246099) baseStart_246099 baseEnd_246099 := by
    simpa [prefixWord, tailWord_246099, baseEnd_246099] using wordTrace_append hprefix tailTrace_246099
  have hstable : (prefixWord ++ tailWord_246099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246099).length < 2 ^ (prefixWord ++ tailWord_246099).sum := by decide
  have hdescent : baseEnd_246099 < baseStart_246099 := by decide
  rcases family_descends (prefixWord ++ tailWord_246099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246133 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_246133 : Nat := 118140960795 + 246133 * 2 ^ 59
def prefixEnd_246133 : Nat := 4983230072969 + 3 ^ 40 * 246133 * 2
def baseEnd_246133 : Nat := 42128177977730245735187

theorem tailTrace_246133 : CollatzResearch.WordTrace tailWord_246133 prefixEnd_246133 42128177977730245735187 := by
  unfold tailWord_246133
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977208017309652014839053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5984805344873101343226035 8977208017309652014839053)
  ·
    refine ⟨3366453006491119505564645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8977208017309652014839053 3366453006491119505564645)
    ·
      refine ⟨631209938717084907293371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3366453006491119505564645 631209938717084907293371)
      ·
        refine ⟨946814908075627360940057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631209938717084907293371 946814908075627360940057)
        ·
          refine ⟨710111181056720520705043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946814908075627360940057 710111181056720520705043)
          ·
            refine ⟨1065166771585080781057565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710111181056720520705043 1065166771585080781057565)
            ·
              refine ⟨399437539344405292896587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1065166771585080781057565 399437539344405292896587)
              ·
                refine ⟨599156309016607939344881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399437539344405292896587 599156309016607939344881)
                ·
                  refine ⟨449367231762455954508661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599156309016607939344881 449367231762455954508661)
                  ·
                    refine ⟨42128177977730245735187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 449367231762455954508661 42128177977730245735187)
                    ·
                      rfl

theorem cell23_246133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_246133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246133 prefixEnd_246133 := by exact prefixLift 246133
  have htrace : WordTrace (prefixWord ++ tailWord_246133) baseStart_246133 baseEnd_246133 := by
    simpa [prefixWord, tailWord_246133, baseEnd_246133] using wordTrace_append hprefix tailTrace_246133
  have hstable : (prefixWord ++ tailWord_246133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246133).length < 2 ^ (prefixWord ++ tailWord_246133).sum := by decide
  have hdescent : baseEnd_246133 < baseStart_246133 := by decide
  rcases family_descends (prefixWord ++ tailWord_246133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246153 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 2, 4, 2]
def baseStart_246153 : Nat := 118140960795 + 246153 * 2 ^ 59
def prefixEnd_246153 : Nat := 4983230072969 + 3 ^ 40 * 246153 * 2
def baseEnd_246153 : Nat := 126394803546280658955469

theorem tailTrace_246153 : CollatzResearch.WordTrace tailWord_246153 prefixEnd_246153 126394803546280658955469 := by
  unfold tailWord_246153
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977937477237195430567113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5985291651491463620378075 8977937477237195430567113)
  ·
    refine ⟨6733453107927896572925335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8977937477237195430567113 6733453107927896572925335)
    ·
      refine ⟨10100179661891844859388003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6733453107927896572925335 10100179661891844859388003)
      ·
        refine ⟨15150269492837767289082005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10100179661891844859388003 15150269492837767289082005)
        ·
          refine ⟨710168882476770341675719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15150269492837767289082005 710168882476770341675719)
          ·
            refine ⟨1065253323715155512513579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710168882476770341675719 1065253323715155512513579)
            ·
              refine ⟨1597879985572733268770369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065253323715155512513579 1597879985572733268770369)
              ·
                refine ⟨1198409989179549951577777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597879985572733268770369 1198409989179549951577777)
                ·
                  refine ⟨898807491884662463683333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198409989179549951577777 898807491884662463683333)
                  ·
                    refine ⟨168526404728374211940625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898807491884662463683333 168526404728374211940625)
                    ·
                      refine ⟨126394803546280658955469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 168526404728374211940625 126394803546280658955469)
                      ·
                        rfl

theorem cell23_246153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 4, 2].length) (baseStart_246153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246153 prefixEnd_246153 := by exact prefixLift 246153
  have htrace : WordTrace (prefixWord ++ tailWord_246153) baseStart_246153 baseEnd_246153 := by
    simpa [prefixWord, tailWord_246153, baseEnd_246153] using wordTrace_append hprefix tailTrace_246153
  have hstable : (prefixWord ++ tailWord_246153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246153).length < 2 ^ (prefixWord ++ tailWord_246153).sum := by decide
  have hdescent : baseEnd_246153 < baseStart_246153 := by decide
  rcases family_descends (prefixWord ++ tailWord_246153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246253 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_246253 : Nat := 118140960795 + 246253 * 2 ^ 59
def prefixEnd_246253 : Nat := 4983230072969 + 3 ^ 40 * 246253 * 2
def baseEnd_246253 : Nat := 42148717203910089235003

theorem tailTrace_246253 : CollatzResearch.WordTrace tailWord_246253 prefixEnd_246253 42148717203910089235003 := by
  unfold tailWord_246253
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981584776874912509207413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5987723184583275006138275 8981584776874912509207413)
  ·
    refine ⟨842023572832023047738195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8981584776874912509207413 842023572832023047738195)
    ·
      refine ⟨1263035359248034571607293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842023572832023047738195 1263035359248034571607293)
      ·
        refine ⟨473638259718012964352735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1263035359248034571607293 473638259718012964352735)
        ·
          refine ⟨710457389577019446529103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473638259718012964352735 710457389577019446529103)
          ·
            refine ⟨1065686084365529169793655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710457389577019446529103 1065686084365529169793655)
            ·
              refine ⟨1598529126548293754690483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065686084365529169793655 1598529126548293754690483)
              ·
                refine ⟨2397793689822440632035725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598529126548293754690483 2397793689822440632035725)
                ·
                  refine ⟨899172633683415237013397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2397793689822440632035725 899172633683415237013397)
                  ·
                    refine ⟨42148717203910089235003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 899172633683415237013397 42148717203910089235003)
                    ·
                      rfl

theorem cell23_246253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_246253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246253 prefixEnd_246253 := by exact prefixLift 246253
  have htrace : WordTrace (prefixWord ++ tailWord_246253) baseStart_246253 baseEnd_246253 := by
    simpa [prefixWord, tailWord_246253, baseEnd_246253] using wordTrace_append hprefix tailTrace_246253
  have hstable : (prefixWord ++ tailWord_246253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246253).length < 2 ^ (prefixWord ++ tailWord_246253).sum := by decide
  have hdescent : baseEnd_246253 < baseStart_246253 := by decide
  rcases family_descends (prefixWord ++ tailWord_246253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246283 : List Nat := [1, 1, 1, 1, 7, 3, 1, 8]
def baseStart_246283 : Nat := 118140960795 + 246283 * 2 ^ 59
def prefixEnd_246283 : Nat := 4983230072969 + 3 ^ 40 * 246283 * 2
def baseEnd_246283 : Nat := 4683761334495005567773

theorem tailTrace_246283 : CollatzResearch.WordTrace tailWord_246283 prefixEnd_246283 4683761334495005567773 := by
  unfold tailWord_246283
  simp only [CollatzResearch.WordTrace]
  refine ⟨8982678966766227632799503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5988452644510818421866335 8982678966766227632799503)
  ·
    refine ⟨13474018450149341449199255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8982678966766227632799503 13474018450149341449199255)
    ·
      refine ⟨20211027675224012173798883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13474018450149341449199255 20211027675224012173798883)
      ·
        refine ⟨30316541512836018260698325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20211027675224012173798883 30316541512836018260698325)
        ·
          refine ⟨710543941707094177985117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30316541512836018260698325 710543941707094177985117)
          ·
            refine ⟨266453978140160316744419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710543941707094177985117 266453978140160316744419)
            ·
              refine ⟨399680967210240475116629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266453978140160316744419 399680967210240475116629)
              ·
                refine ⟨4683761334495005567773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 399680967210240475116629 4683761334495005567773)
                ·
                  rfl

theorem cell23_246283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 8].length) (baseStart_246283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246283 prefixEnd_246283 := by exact prefixLift 246283
  have htrace : WordTrace (prefixWord ++ tailWord_246283) baseStart_246283 baseEnd_246283 := by
    simpa [prefixWord, tailWord_246283, baseEnd_246283] using wordTrace_append hprefix tailTrace_246283
  have hstable : (prefixWord ++ tailWord_246283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246283).length < 2 ^ (prefixWord ++ tailWord_246283).sum := by decide
  have hdescent : baseEnd_246283 < baseStart_246283 := by decide
  rcases family_descends (prefixWord ++ tailWord_246283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246311 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_246311 : Nat := 118140960795 + 246311 * 2 ^ 59
def prefixEnd_246311 : Nat := 4983230072969 + 3 ^ 40 * 246311 * 2
def baseEnd_246311 : Nat := 126475933489691040779743

theorem tailTrace_246311 : CollatzResearch.WordTrace tailWord_246311 prefixEnd_246311 126475933489691040779743 := by
  unfold tailWord_246311
  simp only [CollatzResearch.WordTrace]
  refine ⟨8983700210664788414818787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5989133473776525609879191 8983700210664788414818787)
  ·
    refine ⟨13475550315997182622228181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8983700210664788414818787 13475550315997182622228181)
    ·
      refine ⟨315833210531183967708473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13475550315997182622228181 315833210531183967708473)
      ·
        refine ⟨236874907898387975781355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315833210531183967708473 236874907898387975781355)
        ·
          refine ⟨355312361847581963672033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236874907898387975781355 355312361847581963672033)
          ·
            refine ⟨266484271385686472754025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355312361847581963672033 266484271385686472754025)
            ·
              refine ⟨199863203539264854565519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266484271385686472754025 199863203539264854565519)
              ·
                refine ⟨299794805308897281848279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199863203539264854565519 299794805308897281848279)
                ·
                  refine ⟨449692207963345922772419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299794805308897281848279 449692207963345922772419)
                  ·
                    refine ⟨674538311945018884158629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 449692207963345922772419 674538311945018884158629)
                    ·
                      refine ⟨126475933489691040779743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 674538311945018884158629 126475933489691040779743)
                      ·
                        rfl

theorem cell23_246311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_246311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246311 prefixEnd_246311 := by exact prefixLift 246311
  have htrace : WordTrace (prefixWord ++ tailWord_246311) baseStart_246311 baseEnd_246311 := by
    simpa [prefixWord, tailWord_246311, baseEnd_246311] using wordTrace_append hprefix tailTrace_246311
  have hstable : (prefixWord ++ tailWord_246311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246311).length < 2 ^ (prefixWord ++ tailWord_246311).sum := by decide
  have hdescent : baseEnd_246311 < baseStart_246311 := by decide
  rcases family_descends (prefixWord ++ tailWord_246311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246314 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_246314 : Nat := 118140960795 + 246314 * 2 ^ 59
def prefixEnd_246314 : Nat := 4983230072969 + 3 ^ 40 * 246314 * 2
def baseEnd_246314 : Nat := 126477473931654529042229

theorem tailTrace_246314 : CollatzResearch.WordTrace tailWord_246314 prefixEnd_246314 126477473931654529042229 := by
  unfold tailWord_246314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245952407413479981794499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5989206419769279951451997 2245952407413479981794499)
  ·
    refine ⟨3368928611120219972691749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2245952407413479981794499 3368928611120219972691749)
    ·
      refine ⟨631674114585041244879703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3368928611120219972691749 631674114585041244879703)
      ·
        refine ⟨947511171877561867319555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631674114585041244879703 947511171877561867319555)
        ·
          refine ⟨1421266757816342800979333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947511171877561867319555 1421266757816342800979333)
          ·
            refine ⟨266487517090564275183625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1421266757816342800979333 266487517090564275183625)
            ·
              refine ⟨199865637817923206387719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266487517090564275183625 199865637817923206387719)
              ·
                refine ⟨299798456726884809581579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199865637817923206387719 299798456726884809581579)
                ·
                  refine ⟨449697685090327214372369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299798456726884809581579 449697685090327214372369)
                  ·
                    refine ⟨337273263817745410779277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 449697685090327214372369 337273263817745410779277)
                    ·
                      refine ⟨126477473931654529042229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 337273263817745410779277 126477473931654529042229)
                      ·
                        rfl

theorem cell23_246314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_246314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246314 prefixEnd_246314 := by exact prefixLift 246314
  have htrace : WordTrace (prefixWord ++ tailWord_246314) baseStart_246314 baseEnd_246314 := by
    simpa [prefixWord, tailWord_246314, baseEnd_246314] using wordTrace_append hprefix tailTrace_246314
  have hstable : (prefixWord ++ tailWord_246314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246314).length < 2 ^ (prefixWord ++ tailWord_246314).sum := by decide
  have hdescent : baseEnd_246314 < baseStart_246314 := by decide
  rcases family_descends (prefixWord ++ tailWord_246314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246317 : List Nat := [1, 5, 4, 1, 1, 1, 10]
def baseStart_246317 : Nat := 118140960795 + 246317 * 2 ^ 59
def prefixEnd_246317 : Nat := 4983230072969 + 3 ^ 40 * 246317 * 2
def baseEnd_246317 : Nat := 1561469313254543423515

theorem tailTrace_246317 : CollatzResearch.WordTrace tailWord_246317 prefixEnd_246317 1561469313254543423515 := by
  unfold tailWord_246317
  simp only [CollatzResearch.WordTrace]
  refine ⟨8983919048643051439537205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5989279365762034293024803 8983919048643051439537205)
  ·
    refine ⟨842242410810286072456613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8983919048643051439537205 842242410810286072456613)
    ·
      refine ⟨157920452026928638585615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 842242410810286072456613 157920452026928638585615)
      ·
        refine ⟨236880678040392957878423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157920452026928638585615 236880678040392957878423)
        ·
          refine ⟨355321017060589436817635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236880678040392957878423 355321017060589436817635)
          ·
            refine ⟨532981525590884155226453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355321017060589436817635 532981525590884155226453)
            ·
              refine ⟨1561469313254543423515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 532981525590884155226453 1561469313254543423515)
              ·
                rfl

theorem cell23_246317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 10].length) (baseStart_246317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246317 prefixEnd_246317 := by exact prefixLift 246317
  have htrace : WordTrace (prefixWord ++ tailWord_246317) baseStart_246317 baseEnd_246317 := by
    simpa [prefixWord, tailWord_246317, baseEnd_246317] using wordTrace_append hprefix tailTrace_246317
  have hstable : (prefixWord ++ tailWord_246317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246317).length < 2 ^ (prefixWord ++ tailWord_246317).sum := by decide
  have hdescent : baseEnd_246317 < baseStart_246317 := by decide
  rcases family_descends (prefixWord ++ tailWord_246317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246343 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 2, 6]
def baseStart_246343 : Nat := 118140960795 + 246343 * 2 ^ 59
def prefixEnd_246343 : Nat := 4983230072969 + 3 ^ 40 * 246343 * 2
def baseEnd_246343 : Nat := 42164121623544971859865

theorem tailTrace_246343 : CollatzResearch.WordTrace tailWord_246343 prefixEnd_246343 42164121623544971859865 := by
  unfold tailWord_246343
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984867346548857879983683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5989911564365905253322455 8984867346548857879983683)
  ·
    refine ⟨13477301019823286819975525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8984867346548857879983683 13477301019823286819975525)
    ·
      refine ⟨2526993941216866278745411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13477301019823286819975525 2526993941216866278745411)
      ·
        refine ⟨3790490911825299418118117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526993941216866278745411 3790490911825299418118117)
        ·
          refine ⟨710717045967243640897147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3790490911825299418118117 710717045967243640897147)
          ·
            refine ⟨1066075568950865461345721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710717045967243640897147 1066075568950865461345721)
            ·
              refine ⟨799556676713149096009291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066075568950865461345721 799556676713149096009291)
              ·
                refine ⟨1199335015069723644013937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799556676713149096009291 1199335015069723644013937)
                ·
                  refine ⟨899501261302292733010453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199335015069723644013937 899501261302292733010453)
                  ·
                    refine ⟨42164121623544971859865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 899501261302292733010453 42164121623544971859865)
                    ·
                      rfl

theorem cell23_246343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_246343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246343 prefixEnd_246343 := by exact prefixLift 246343
  have htrace : WordTrace (prefixWord ++ tailWord_246343) baseStart_246343 baseEnd_246343 := by
    simpa [prefixWord, tailWord_246343, baseEnd_246343] using wordTrace_append hprefix tailTrace_246343
  have hstable : (prefixWord ++ tailWord_246343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246343).length < 2 ^ (prefixWord ++ tailWord_246343).sum := by decide
  have hdescent : baseEnd_246343 < baseStart_246343 := by decide
  rcases family_descends (prefixWord ++ tailWord_246343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246383 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 3]
def baseStart_246383 : Nat := 118140960795 + 246383 * 2 ^ 59
def prefixEnd_246383 : Nat := 4983230072969 + 3 ^ 40 * 246383 * 2
def baseEnd_246383 : Nat := 126512904096814759079411

theorem tailTrace_246383 : CollatzResearch.WordTrace tailWord_246383 prefixEnd_246383 126512904096814759079411 := by
  unfold tailWord_246383
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986326266403944711439803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5990884177602629807626535 8986326266403944711439803)
  ·
    refine ⟨13479489399605917067159705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8986326266403944711439803 13479489399605917067159705)
    ·
      refine ⟨10109617049704437800369779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13479489399605917067159705 10109617049704437800369779)
      ·
        refine ⟨15164425574556656700554669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10109617049704437800369779 15164425574556656700554669)
        ·
          refine ⟨5686659590458746262708001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15164425574556656700554669 5686659590458746262708001)
          ·
            refine ⟨4264994692844059697031001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5686659590458746262708001 4264994692844059697031001)
            ·
              refine ⟨3198746019633044772773251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264994692844059697031001 3198746019633044772773251)
              ·
                refine ⟨4798119029449567159159877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198746019633044772773251 4798119029449567159159877)
                ·
                  refine ⟨899647318021793842342477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4798119029449567159159877 899647318021793842342477)
                  ·
                    refine ⟨337367744258172690878429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899647318021793842342477 337367744258172690878429)
                    ·
                      refine ⟨126512904096814759079411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 337367744258172690878429 126512904096814759079411)
                      ·
                        rfl

theorem cell23_246383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_246383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246383 prefixEnd_246383 := by exact prefixLift 246383
  have htrace : WordTrace (prefixWord ++ tailWord_246383) baseStart_246383 baseEnd_246383 := by
    simpa [prefixWord, tailWord_246383, baseEnd_246383] using wordTrace_append hprefix tailTrace_246383
  have hstable : (prefixWord ++ tailWord_246383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246383).length < 2 ^ (prefixWord ++ tailWord_246383).sum := by decide
  have hdescent : baseEnd_246383 < baseStart_246383 := by decide
  rcases family_descends (prefixWord ++ tailWord_246383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246430 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_246430 : Nat := 118140960795 + 246430 * 2 ^ 59
def prefixEnd_246430 : Nat := 4983230072969 + 3 ^ 40 * 246430 * 2
def baseEnd_246430 : Nat := 126537037687576075191695

theorem tailTrace_246430 : CollatzResearch.WordTrace tailWord_246430 prefixEnd_246430 126537037687576075191695 := by
  unfold tailWord_246430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123505062154208967300093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5992026998155781158933829 1123505062154208967300093)
  ·
    refine ⟨421314398307828362737535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1123505062154208967300093 421314398307828362737535)
    ·
      refine ⟨631971597461742544106303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421314398307828362737535 631971597461742544106303)
      ·
        refine ⟨947957396192613816159455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631971597461742544106303 947957396192613816159455)
        ·
          refine ⟨1421936094288920724239183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947957396192613816159455 1421936094288920724239183)
          ·
            refine ⟨2132904141433381086358775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421936094288920724239183 2132904141433381086358775)
            ·
              refine ⟨3199356212150071629538163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132904141433381086358775 3199356212150071629538163)
              ·
                refine ⟨4799034318225107444307245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199356212150071629538163 4799034318225107444307245)
                ·
                  refine ⟨1799637869334415291615217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4799034318225107444307245 1799637869334415291615217)
                  ·
                    refine ⟨1349728402000811468711413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799637869334415291615217 1349728402000811468711413)
                    ·
                      refine ⟨126537037687576075191695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1349728402000811468711413 126537037687576075191695)
                      ·
                        rfl

theorem cell23_246430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_246430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246430 prefixEnd_246430 := by exact prefixLift 246430
  have htrace : WordTrace (prefixWord ++ tailWord_246430) baseStart_246430 baseEnd_246430 := by
    simpa [prefixWord, tailWord_246430, baseEnd_246430] using wordTrace_append hprefix tailTrace_246430
  have hstable : (prefixWord ++ tailWord_246430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246430).length < 2 ^ (prefixWord ++ tailWord_246430).sum := by decide
  have hdescent : baseEnd_246430 < baseStart_246430 := by decide
  rcases family_descends (prefixWord ++ tailWord_246430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246450 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_246450 : Nat := 118140960795 + 246450 * 2 ^ 59
def prefixEnd_246450 : Nat := 4983230072969 + 3 ^ 40 * 246450 * 2
def baseEnd_246450 : Nat := 42182435766888665647201

theorem tailTrace_246450 : CollatzResearch.WordTrace tailWord_246450 prefixEnd_246450 42182435766888665647201 := by
  unfold tailWord_246450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247192489290303788532201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5992513304774143436085869 2247192489290303788532201)
  ·
    refine ⟨1685394366967727841399151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2247192489290303788532201 1685394366967727841399151)
    ·
      refine ⟨2528091550451591762098727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685394366967727841399151 2528091550451591762098727)
      ·
        refine ⟨3792137325677387643148091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528091550451591762098727 3792137325677387643148091)
        ·
          refine ⟨5688205988516081464722137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792137325677387643148091 5688205988516081464722137)
          ·
            refine ⟨4266154491387061098541603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5688205988516081464722137 4266154491387061098541603)
            ·
              refine ⟨6399231737080591647812405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266154491387061098541603 6399231737080591647812405)
              ·
                refine ⟨599927975351305466982413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6399231737080591647812405 599927975351305466982413)
                ·
                  refine ⟨224972990756739550118405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599927975351305466982413 224972990756739550118405)
                  ·
                    refine ⟨42182435766888665647201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224972990756739550118405 42182435766888665647201)
                    ·
                      rfl

theorem cell23_246450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_246450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246450 prefixEnd_246450 := by exact prefixLift 246450
  have htrace : WordTrace (prefixWord ++ tailWord_246450) baseStart_246450 baseEnd_246450 := by
    simpa [prefixWord, tailWord_246450, baseEnd_246450] using wordTrace_append hprefix tailTrace_246450
  have hstable : (prefixWord ++ tailWord_246450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246450).length < 2 ^ (prefixWord ++ tailWord_246450).sum := by decide
  have hdescent : baseEnd_246450 < baseStart_246450 := by decide
  rcases family_descends (prefixWord ++ tailWord_246450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246460 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_246460 : Nat := 118140960795 + 246460 * 2 ^ 59
def prefixEnd_246460 : Nat := 4983230072969 + 3 ^ 40 * 246460 * 2
def baseEnd_246460 : Nat := 126552442107210957816557

theorem tailTrace_246460 : CollatzResearch.WordTrace tailWord_246460 prefixEnd_246460 126552442107210957816557 := by
  unfold tailWord_246460
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494567343562493430996417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5992756458083324574661889 4494567343562493430996417)
  ·
    refine ⟨3370925507671870073247313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4494567343562493430996417 3370925507671870073247313)
    ·
      refine ⟨2528194130753902554935485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3370925507671870073247313 2528194130753902554935485)
      ·
        refine ⟨948072799032713458100807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2528194130753902554935485 948072799032713458100807)
        ·
          refine ⟨1422109198549070187151211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948072799032713458100807 1422109198549070187151211)
          ·
            refine ⟨2133163797823605280726817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422109198549070187151211 2133163797823605280726817)
            ·
              refine ⟨1599872848367703960545113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133163797823605280726817 1599872848367703960545113)
              ·
                refine ⟨1199904636275777970408835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599872848367703960545113 1199904636275777970408835)
                ·
                  refine ⟨1799856954413666955613253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199904636275777970408835 1799856954413666955613253)
                  ·
                    refine ⟨337473178952562554177485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799856954413666955613253 337473178952562554177485)
                    ·
                      refine ⟨126552442107210957816557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 337473178952562554177485 126552442107210957816557)
                      ·
                        rfl

theorem cell23_246460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_246460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246460 prefixEnd_246460 := by exact prefixLift 246460
  have htrace : WordTrace (prefixWord ++ tailWord_246460) baseStart_246460 baseEnd_246460 := by
    simpa [prefixWord, tailWord_246460, baseEnd_246460] using wordTrace_append hprefix tailTrace_246460
  have hstable : (prefixWord ++ tailWord_246460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246460).length < 2 ^ (prefixWord ++ tailWord_246460).sum := by decide
  have hdescent : baseEnd_246460 < baseStart_246460 := by decide
  rcases family_descends (prefixWord ++ tailWord_246460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246497 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 6]
def baseStart_246497 : Nat := 118140960795 + 246497 * 2 ^ 59
def prefixEnd_246497 : Nat := 4983230072969 + 3 ^ 40 * 246497 * 2
def baseEnd_246497 : Nat := 14063493432380812561543

theorem tailTrace_246497 : CollatzResearch.WordTrace tailWord_246497 prefixEnd_246497 14063493432380812561543 := by
  unfold tailWord_246497
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990484187990942181089745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5993656125327294787393163 8990484187990942181089745)
  ·
    refine ⟨6742863140993206635817309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8990484187990942181089745 6742863140993206635817309)
    ·
      refine ⟨2528573677872452488431491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6742863140993206635817309 2528573677872452488431491)
      ·
        refine ⟨3792860516808678732647237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528573677872452488431491 3792860516808678732647237)
        ·
          refine ⟨711161346901627262371357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3792860516808678732647237 711161346901627262371357)
          ·
            refine ⟨266685505088110223389259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 711161346901627262371357 266685505088110223389259)
            ·
              refine ⟨400028257632165335083889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266685505088110223389259 400028257632165335083889)
              ·
                refine ⟨300021193224124001312917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400028257632165335083889 300021193224124001312917)
                ·
                  refine ⟨14063493432380812561543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 300021193224124001312917 14063493432380812561543)
                  ·
                    rfl

theorem cell23_246497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 6].length) (baseStart_246497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246497 prefixEnd_246497 := by exact prefixLift 246497
  have htrace : WordTrace (prefixWord ++ tailWord_246497) baseStart_246497 baseEnd_246497 := by
    simpa [prefixWord, tailWord_246497, baseEnd_246497] using wordTrace_append hprefix tailTrace_246497
  have hstable : (prefixWord ++ tailWord_246497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246497).length < 2 ^ (prefixWord ++ tailWord_246497).sum := by decide
  have hdescent : baseEnd_246497 < baseStart_246497 := by decide
  rcases family_descends (prefixWord ++ tailWord_246497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246560 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_246560 : Nat := 118140960795 + 246560 * 2 ^ 59
def prefixEnd_246560 : Nat := 4983230072969 + 3 ^ 40 * 246560 * 2
def baseEnd_246560 : Nat := 126603790172660566566097

theorem tailTrace_246560 : CollatzResearch.WordTrace tailWord_246560 prefixEnd_246560 126603790172660566566097 := by
  unfold tailWord_246560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4496390993381351970316567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5995187991175135960422089 4496390993381351970316567)
  ·
    refine ⟨6744586490072027955474851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4496390993381351970316567 6744586490072027955474851)
    ·
      refine ⟨10116879735108041933212277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6744586490072027955474851 10116879735108041933212277)
      ·
        refine ⟨948457475166378931238651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10116879735108041933212277 948457475166378931238651)
        ·
          refine ⟨1422686212749568396857977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948457475166378931238651 1422686212749568396857977)
          ·
            refine ⟨1067014659562176297643483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422686212749568396857977 1067014659562176297643483)
            ·
              refine ⟨1600521989343264446465225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067014659562176297643483 1600521989343264446465225)
              ·
                refine ⟨1200391492007448334848919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600521989343264446465225 1200391492007448334848919)
                ·
                  refine ⟨1800587238011172502273379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200391492007448334848919 1800587238011172502273379)
                  ·
                    refine ⟨2700880857016758753410069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1800587238011172502273379 2700880857016758753410069)
                    ·
                      refine ⟨126603790172660566566097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2700880857016758753410069 126603790172660566566097)
                      ·
                        rfl

theorem cell23_246560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_246560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246560 prefixEnd_246560 := by exact prefixLift 246560
  have htrace : WordTrace (prefixWord ++ tailWord_246560) baseStart_246560 baseEnd_246560 := by
    simpa [prefixWord, tailWord_246560, baseEnd_246560] using wordTrace_append hprefix tailTrace_246560
  have hstable : (prefixWord ++ tailWord_246560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246560).length < 2 ^ (prefixWord ++ tailWord_246560).sum := by decide
  have hdescent : baseEnd_246560 < baseStart_246560 := by decide
  rcases family_descends (prefixWord ++ tailWord_246560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246597 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_246597 : Nat := 118140960795 + 246597 * 2 ^ 59
def prefixEnd_246597 : Nat := 4983230072969 + 3 ^ 40 * 246597 * 2
def baseEnd_246597 : Nat := 126622788956876921803427

theorem tailTrace_246597 : CollatzResearch.WordTrace tailWord_246597 prefixEnd_246597 126622788956876921803427 := by
  unfold tailWord_246597
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994131487628659259730045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5996087658419106173153363 8994131487628659259730045)
  ·
    refine ⟨3372799307860747222398767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8994131487628659259730045 3372799307860747222398767)
    ·
      refine ⟨5059198961791120833598151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372799307860747222398767 5059198961791120833598151)
      ·
        refine ⟨7588798442686681250397227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059198961791120833598151 7588798442686681250397227)
        ·
          refine ⟨11383197664030021875595841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588798442686681250397227 11383197664030021875595841)
          ·
            refine ⟨8537398248022516406696881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11383197664030021875595841 8537398248022516406696881)
            ·
              refine ⟨6403048686016887305022661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8537398248022516406696881 6403048686016887305022661)
              ·
                refine ⟨1200571628628166369691749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6403048686016887305022661 1200571628628166369691749)
                ·
                  refine ⟨225107180367781194317203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200571628628166369691749 225107180367781194317203)
                  ·
                    refine ⟨337660770551671791475805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225107180367781194317203 337660770551671791475805)
                    ·
                      refine ⟨126622788956876921803427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 337660770551671791475805 126622788956876921803427)
                      ·
                        rfl

theorem cell23_246597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_246597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246597 prefixEnd_246597 := by exact prefixLift 246597
  have htrace : WordTrace (prefixWord ++ tailWord_246597) baseStart_246597 baseEnd_246597 := by
    simpa [prefixWord, tailWord_246597, baseEnd_246597] using wordTrace_append hprefix tailTrace_246597
  have hstable : (prefixWord ++ tailWord_246597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246597).length < 2 ^ (prefixWord ++ tailWord_246597).sum := by decide
  have hdescent : baseEnd_246597 < baseStart_246597 := by decide
  rcases family_descends (prefixWord ++ tailWord_246597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246615 : List Nat := [1, 1, 3, 2, 4, 3, 2, 2, 1, 2, 2]
def baseStart_246615 : Nat := 118140960795 + 246615 * 2 ^ 59
def prefixEnd_246615 : Nat := 4983230072969 + 3 ^ 40 * 246615 * 2
def baseEnd_246615 : Nat := 126632031608657851378345

theorem tailTrace_246615 : CollatzResearch.WordTrace tailWord_246615 prefixEnd_246615 126632031608657851378345 := by
  unfold tailWord_246615
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994788001563448333885299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5996525334375632222590199 8994788001563448333885299)
  ·
    refine ⟨13492182002345172500827949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8994788001563448333885299 13492182002345172500827949)
    ·
      refine ⟨5059568250879439687810481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13492182002345172500827949 5059568250879439687810481)
      ·
        refine ⟨3794676188159579765857861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5059568250879439687810481 3794676188159579765857861)
        ·
          refine ⟨711501785279921206098349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3794676188159579765857861 711501785279921206098349)
          ·
            refine ⟨266813169479970452286881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 711501785279921206098349 266813169479970452286881)
            ·
              refine ⟨200109877109977839215161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266813169479970452286881 200109877109977839215161)
              ·
                refine ⟨150082407832483379411371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200109877109977839215161 150082407832483379411371)
                ·
                  refine ⟨225123611748725069117057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150082407832483379411371 225123611748725069117057)
                  ·
                    refine ⟨168842708811543801837793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225123611748725069117057 168842708811543801837793)
                    ·
                      refine ⟨126632031608657851378345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 168842708811543801837793 126632031608657851378345)
                      ·
                        rfl

theorem cell23_246615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_246615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246615 prefixEnd_246615 := by exact prefixLift 246615
  have htrace : WordTrace (prefixWord ++ tailWord_246615) baseStart_246615 baseEnd_246615 := by
    simpa [prefixWord, tailWord_246615, baseEnd_246615] using wordTrace_append hprefix tailTrace_246615
  have hstable : (prefixWord ++ tailWord_246615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246615).length < 2 ^ (prefixWord ++ tailWord_246615).sum := by decide
  have hdescent : baseEnd_246615 < baseStart_246615 := by decide
  rcases family_descends (prefixWord ++ tailWord_246615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246640 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_246640 : Nat := 118140960795 + 246640 * 2 ^ 59
def prefixEnd_246640 : Nat := 4983230072969 + 3 ^ 40 * 246640 * 2
def baseEnd_246640 : Nat := 126644868625020253565729

theorem tailTrace_246640 : CollatzResearch.WordTrace tailWord_246640 prefixEnd_246640 126644868625020253565729 := by
  unfold tailWord_246640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497849913236438801772687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5997133217648585069030249 4497849913236438801772687)
  ·
    refine ⟨6746774869854658202659031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4497849913236438801772687 6746774869854658202659031)
    ·
      refine ⟨10120162304781987303988547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6746774869854658202659031 10120162304781987303988547)
      ·
        refine ⟨15180243457172980955982821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120162304781987303988547 15180243457172980955982821)
        ·
          refine ⟨2846295648219933929246779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15180243457172980955982821 2846295648219933929246779)
          ·
            refine ⟨4269443472329900893870169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846295648219933929246779 4269443472329900893870169)
            ·
              refine ⟨3202082604247425670402627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269443472329900893870169 3202082604247425670402627)
              ·
                refine ⟨4803123906371138505603941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202082604247425670402627 4803123906371138505603941)
                ·
                  refine ⟨900585732444588469800739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4803123906371138505603941 900585732444588469800739)
                  ·
                    refine ⟨1350878598666882704701109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 900585732444588469800739 1350878598666882704701109)
                    ·
                      refine ⟨126644868625020253565729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1350878598666882704701109 126644868625020253565729)
                      ·
                        rfl

theorem cell23_246640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_246640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246640 prefixEnd_246640 := by exact prefixLift 246640
  have htrace : WordTrace (prefixWord ++ tailWord_246640) baseStart_246640 baseEnd_246640 := by
    simpa [prefixWord, tailWord_246640, baseEnd_246640] using wordTrace_append hprefix tailTrace_246640
  have hstable : (prefixWord ++ tailWord_246640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246640).length < 2 ^ (prefixWord ++ tailWord_246640).sum := by decide
  have hdescent : baseEnd_246640 < baseStart_246640 := by decide
  rcases family_descends (prefixWord ++ tailWord_246640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246650 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_246650 : Nat := 118140960795 + 246650 * 2 ^ 59
def prefixEnd_246650 : Nat := 4983230072969 + 3 ^ 40 * 246650 * 2
def baseEnd_246650 : Nat := 126650003431565214440683

theorem tailTrace_246650 : CollatzResearch.WordTrace tailWord_246650 prefixEnd_246650 126650003431565214440683 := by
  unfold tailWord_246650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249016139109162327852351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5997376370957766207606269 2249016139109162327852351)
  ·
    refine ⟨3373524208663743491778527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2249016139109162327852351 3373524208663743491778527)
    ·
      refine ⟨5060286312995615237667791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3373524208663743491778527 5060286312995615237667791)
      ·
        refine ⟨7590429469493422856501687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5060286312995615237667791 7590429469493422856501687)
        ·
          refine ⟨11385644204240134284752531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7590429469493422856501687 11385644204240134284752531)
          ·
            refine ⟨17078466306360201427128797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11385644204240134284752531 17078466306360201427128797)
            ·
              refine ⟨6404424864885075535173299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17078466306360201427128797 6404424864885075535173299)
              ·
                refine ⟨9606637297327613302759949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404424864885075535173299 9606637297327613302759949)
                ·
                  refine ⟨3602488986497854988534981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9606637297327613302759949 3602488986497854988534981)
                  ·
                    refine ⟨675466684968347810350309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602488986497854988534981 675466684968347810350309)
                    ·
                      refine ⟨126650003431565214440683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 675466684968347810350309 126650003431565214440683)
                      ·
                        rfl

theorem cell23_246650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_246650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246650 prefixEnd_246650 := by exact prefixLift 246650
  have htrace : WordTrace (prefixWord ++ tailWord_246650) baseStart_246650 baseEnd_246650 := by
    simpa [prefixWord, tailWord_246650, baseEnd_246650] using wordTrace_append hprefix tailTrace_246650
  have hstable : (prefixWord ++ tailWord_246650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246650).length < 2 ^ (prefixWord ++ tailWord_246650).sum := by decide
  have hdescent : baseEnd_246650 < baseStart_246650 := by decide
  rcases family_descends (prefixWord ++ tailWord_246650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246660 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 11]
def baseStart_246660 : Nat := 118140960795 + 246660 * 2 ^ 59
def prefixEnd_246660 : Nat := 4983230072969 + 3 ^ 40 * 246660 * 2
def baseEnd_246660 : Nat := 14072793137567797257293

theorem tailTrace_246660 : CollatzResearch.WordTrace tailWord_246660 prefixEnd_246660 14072793137567797257293 := by
  unfold tailWord_246660
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498214643200210509636717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5997619524266947346182289 4498214643200210509636717)
  ·
    refine ⟨1686830491200078941113769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4498214643200210509636717 1686830491200078941113769)
    ·
      refine ⟨1265122868400059205835327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1686830491200078941113769 1265122868400059205835327)
      ·
        refine ⟨1897684302600088808752991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265122868400059205835327 1897684302600088808752991)
        ·
          refine ⟨2846526453900133213129487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897684302600088808752991 2846526453900133213129487)
          ·
            refine ⟨4269789680850199819694231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846526453900133213129487 4269789680850199819694231)
            ·
              refine ⟨6404684521275299729541347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269789680850199819694231 6404684521275299729541347)
              ·
                refine ⟨9607026781912949594312021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404684521275299729541347 9607026781912949594312021)
                ·
                  refine ⟨14072793137567797257293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 9607026781912949594312021 14072793137567797257293)
                  ·
                    rfl

theorem cell23_246660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_246660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246660 prefixEnd_246660 := by exact prefixLift 246660
  have htrace : WordTrace (prefixWord ++ tailWord_246660) baseStart_246660 baseEnd_246660 := by
    simpa [prefixWord, tailWord_246660, baseEnd_246660] using wordTrace_append hprefix tailTrace_246660
  have hstable : (prefixWord ++ tailWord_246660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246660).length < 2 ^ (prefixWord ++ tailWord_246660).sum := by decide
  have hdescent : baseEnd_246660 < baseStart_246660 := by decide
  rcases family_descends (prefixWord ++ tailWord_246660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246677 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 7]
def baseStart_246677 : Nat := 118140960795 + 246677 * 2 ^ 59
def prefixEnd_246677 : Nat := 4983230072969 + 3 ^ 40 * 246677 * 2
def baseEnd_246677 : Nat := 14073763045470734311451

theorem tailTrace_246677 : CollatzResearch.WordTrace tailWord_246677 prefixEnd_246677 14073763045470734311451 := by
  unfold tailWord_246677
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997049327338832922642285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5998032884892555281761523 8997049327338832922642285)
  ·
    refine ⟨3373893497752062345990857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8997049327338832922642285 3373893497752062345990857)
    ·
      refine ⟨2530420123314046759493143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3373893497752062345990857 2530420123314046759493143)
      ·
        refine ⟨3795630184971070139239715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530420123314046759493143 3795630184971070139239715)
        ·
          refine ⟨5693445277456605208859573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795630184971070139239715 5693445277456605208859573)
          ·
            refine ⟨533760494761556738330585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5693445277456605208859573 533760494761556738330585)
            ·
              refine ⟨400320371071167553747939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533760494761556738330585 400320371071167553747939)
              ·
                refine ⟨600480556606751330621909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400320371071167553747939 600480556606751330621909)
                ·
                  refine ⟨14073763045470734311451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 600480556606751330621909 14073763045470734311451)
                  ·
                    rfl

theorem cell23_246677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_246677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246677 prefixEnd_246677 := by exact prefixLift 246677
  have htrace : WordTrace (prefixWord ++ tailWord_246677) baseStart_246677 baseEnd_246677 := by
    simpa [prefixWord, tailWord_246677, baseEnd_246677] using wordTrace_append hprefix tailTrace_246677
  have hstable : (prefixWord ++ tailWord_246677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246677).length < 2 ^ (prefixWord ++ tailWord_246677).sum := by decide
  have hdescent : baseEnd_246677 < baseStart_246677 := by decide
  rcases family_descends (prefixWord ++ tailWord_246677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246700 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_246700 : Nat := 118140960795 + 246700 * 2 ^ 59
def prefixEnd_246700 : Nat := 4983230072969 + 3 ^ 40 * 246700 * 2
def baseEnd_246700 : Nat := 126675677464290018815453

theorem tailTrace_246700 : CollatzResearch.WordTrace tailWord_246700 prefixEnd_246700 126675677464290018815453 := by
  unfold tailWord_246700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498944103127753925364777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5998592137503671900486369 4498944103127753925364777)
  ·
    refine ⟨3374208077345815444023583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4498944103127753925364777 3374208077345815444023583)
    ·
      refine ⟨5061312116018723166035375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3374208077345815444023583 5061312116018723166035375)
      ·
        refine ⟨7591968174028084749053063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061312116018723166035375 7591968174028084749053063)
        ·
          refine ⟨11387952261042127123579595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591968174028084749053063 11387952261042127123579595)
          ·
            refine ⟨17081928391563190685369393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11387952261042127123579595 17081928391563190685369393)
            ·
              refine ⟨12811446293672393014027045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17081928391563190685369393 12811446293672393014027045)
              ·
                refine ⟨2402146180063573690130071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12811446293672393014027045 2402146180063573690130071)
                ·
                  refine ⟨3603219270095360535195107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402146180063573690130071 3603219270095360535195107)
                  ·
                    refine ⟨5404828905143040802792661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3603219270095360535195107 5404828905143040802792661)
                    ·
                      refine ⟨126675677464290018815453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5404828905143040802792661 126675677464290018815453)
                      ·
                        rfl

theorem cell23_246700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_246700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246700 prefixEnd_246700 := by exact prefixLift 246700
  have htrace : WordTrace (prefixWord ++ tailWord_246700) baseStart_246700 baseEnd_246700 := by
    simpa [prefixWord, tailWord_246700, baseEnd_246700] using wordTrace_append hprefix tailTrace_246700
  have hstable : (prefixWord ++ tailWord_246700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246700).length < 2 ^ (prefixWord ++ tailWord_246700).sum := by decide
  have hdescent : baseEnd_246700 < baseStart_246700 := by decide
  rcases family_descends (prefixWord ++ tailWord_246700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246727 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_246727 : Nat := 118140960795 + 246727 * 2 ^ 59
def prefixEnd_246727 : Nat := 4983230072969 + 3 ^ 40 * 246727 * 2
def baseEnd_246727 : Nat := 126689541441961413177829

theorem tailTrace_246727 : CollatzResearch.WordTrace tailWord_246727 prefixEnd_246727 126689541441961413177829 := by
  unfold tailWord_246727
  simp only [CollatzResearch.WordTrace]
  refine ⟨8998872977157691461962435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5999248651438460974641623 8998872977157691461962435)
  ·
    refine ⟨13498309465736537192943653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8998872977157691461962435 13498309465736537192943653)
    ·
      refine ⟨2530933024825600723676935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13498309465736537192943653 2530933024825600723676935)
      ·
        refine ⟨3796399537238401085515403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530933024825600723676935 3796399537238401085515403)
        ·
          refine ⟨5694599305857601628273105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796399537238401085515403 5694599305857601628273105)
          ·
            refine ⟨4270949479393201221204829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5694599305857601628273105 4270949479393201221204829)
            ·
              refine ⟨1601606054772450457951811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4270949479393201221204829 1601606054772450457951811)
              ·
                refine ⟨2402409082158675686927717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601606054772450457951811 2402409082158675686927717)
                ·
                  refine ⟨450451702904751691298947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402409082158675686927717 450451702904751691298947)
                  ·
                    refine ⟨675677554357127536948421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 450451702904751691298947 675677554357127536948421)
                    ·
                      refine ⟨126689541441961413177829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 675677554357127536948421 126689541441961413177829)
                      ·
                        rfl

theorem cell23_246727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_246727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246727 prefixEnd_246727 := by exact prefixLift 246727
  have htrace : WordTrace (prefixWord ++ tailWord_246727) baseStart_246727 baseEnd_246727 := by
    simpa [prefixWord, tailWord_246727, baseEnd_246727] using wordTrace_append hprefix tailTrace_246727
  have hstable : (prefixWord ++ tailWord_246727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246727).length < 2 ^ (prefixWord ++ tailWord_246727).sum := by decide
  have hdescent : baseEnd_246727 < baseStart_246727 := by decide
  rcases family_descends (prefixWord ++ tailWord_246727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246827 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 1, 6]
def baseStart_246827 : Nat := 118140960795 + 246827 * 2 ^ 59
def prefixEnd_246827 : Nat := 4983230072969 + 3 ^ 40 * 246827 * 2
def baseEnd_246827 : Nat := 42246963169137007309123

theorem tailTrace_246827 : CollatzResearch.WordTrace tailWord_246827 prefixEnd_246827 42246963169137007309123 := by
  unfold tailWord_246827
  simp only [CollatzResearch.WordTrace]
  refine ⟨9002520276795408540602735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6001680184530272360401823 9002520276795408540602735)
  ·
    refine ⟨13503780415193112810904103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9002520276795408540602735 13503780415193112810904103)
    ·
      refine ⟨20255670622789669216356155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13503780415193112810904103 20255670622789669216356155)
      ·
        refine ⟨30383505934184503824534233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20255670622789669216356155 30383505934184503824534233)
        ·
          refine ⟨22787629450638377868400675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30383505934184503824534233 22787629450638377868400675)
          ·
            refine ⟨34181444175957566802601013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22787629450638377868400675 34181444175957566802601013)
            ·
              refine ⟨3204510391496021887743845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34181444175957566802601013 3204510391496021887743845)
              ·
                refine ⟨600845698405504103951971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3204510391496021887743845 600845698405504103951971)
                ·
                  refine ⟨901268547608256155927957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600845698405504103951971 901268547608256155927957)
                  ·
                    refine ⟨42246963169137007309123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 901268547608256155927957 42246963169137007309123)
                    ·
                      rfl

theorem cell23_246827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 6].length) (baseStart_246827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246827 prefixEnd_246827 := by exact prefixLift 246827
  have htrace : WordTrace (prefixWord ++ tailWord_246827) baseStart_246827 baseEnd_246827 := by
    simpa [prefixWord, tailWord_246827, baseEnd_246827] using wordTrace_append hprefix tailTrace_246827
  have hstable : (prefixWord ++ tailWord_246827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246827).length < 2 ^ (prefixWord ++ tailWord_246827).sum := by decide
  have hdescent : baseEnd_246827 < baseStart_246827 := by decide
  rcases family_descends (prefixWord ++ tailWord_246827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246828 : List Nat := [2, 2, 1, 1, 1, 2, 6, 3, 1, 1, 3]
def baseStart_246828 : Nat := 118140960795 + 246828 * 2 ^ 59
def prefixEnd_246828 : Nat := 4983230072969 + 3 ^ 40 * 246828 * 2
def baseEnd_246828 : Nat := 126741402988065518014865

theorem tailTrace_246828 : CollatzResearch.WordTrace tailWord_246828 prefixEnd_246828 126741402988065518014865 := by
  unfold tailWord_246828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501278374895892855694569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6001704499861190474259425 4501278374895892855694569)
  ·
    refine ⟨3375958781171919641770927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4501278374895892855694569 3375958781171919641770927)
    ·
      refine ⟨5063938171757879462656391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375958781171919641770927 5063938171757879462656391)
      ·
        refine ⟨7595907257636819193984587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063938171757879462656391 7595907257636819193984587)
        ·
          refine ⟨11393860886455228790976881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595907257636819193984587 11393860886455228790976881)
          ·
            refine ⟨8545395664841421593232661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11393860886455228790976881 8545395664841421593232661)
            ·
              refine ⟨400565421789441637182781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8545395664841421593232661 400565421789441637182781)
              ·
                refine ⟨150212033171040613943543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400565421789441637182781 150212033171040613943543)
                ·
                  refine ⟨225318049756560920915315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150212033171040613943543 225318049756560920915315)
                  ·
                    refine ⟨337977074634841381372973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225318049756560920915315 337977074634841381372973)
                    ·
                      refine ⟨126741402988065518014865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 337977074634841381372973 126741402988065518014865)
                      ·
                        rfl

theorem cell23_246828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_246828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246828 prefixEnd_246828 := by exact prefixLift 246828
  have htrace : WordTrace (prefixWord ++ tailWord_246828) baseStart_246828 baseEnd_246828 := by
    simpa [prefixWord, tailWord_246828, baseEnd_246828] using wordTrace_append hprefix tailTrace_246828
  have hstable : (prefixWord ++ tailWord_246828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246828).length < 2 ^ (prefixWord ++ tailWord_246828).sum := by decide
  have hdescent : baseEnd_246828 < baseStart_246828 := by decide
  rcases family_descends (prefixWord ++ tailWord_246828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246847 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_246847 : Nat := 118140960795 + 246847 * 2 ^ 59
def prefixEnd_246847 : Nat := 4983230072969 + 3 ^ 40 * 246847 * 2
def baseEnd_246847 : Nat := 126751159120500943677277

theorem tailTrace_246847 : CollatzResearch.WordTrace tailWord_246847 prefixEnd_246847 126751159120500943677277 := by
  unfold tailWord_246847
  simp only [CollatzResearch.WordTrace]
  refine ⟨9003249736722951956330795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6002166491148634637553863 9003249736722951956330795)
  ·
    refine ⟨13504874605084427934496193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9003249736722951956330795 13504874605084427934496193)
    ·
      refine ⟨10128655953813320950872145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13504874605084427934496193 10128655953813320950872145)
      ·
        refine ⟨7596491965359990713154109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10128655953813320950872145 7596491965359990713154109)
        ·
          refine ⟨2848684487009996517432791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7596491965359990713154109 2848684487009996517432791)
          ·
            refine ⟨4273026730514994776149187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848684487009996517432791 4273026730514994776149187)
            ·
              refine ⟨6409540095772492164223781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273026730514994776149187 6409540095772492164223781)
              ·
                refine ⟨1201788767957342280791959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6409540095772492164223781 1201788767957342280791959)
                ·
                  refine ⟨1802683151936013421187939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201788767957342280791959 1802683151936013421187939)
                  ·
                    refine ⟨2704024727904020131781909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1802683151936013421187939 2704024727904020131781909)
                    ·
                      refine ⟨126751159120500943677277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2704024727904020131781909 126751159120500943677277)
                      ·
                        rfl

theorem cell23_246847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_246847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246847 prefixEnd_246847 := by exact prefixLift 246847
  have htrace : WordTrace (prefixWord ++ tailWord_246847) baseStart_246847 baseEnd_246847 := by
    simpa [prefixWord, tailWord_246847, baseEnd_246847] using wordTrace_append hprefix tailTrace_246847
  have hstable : (prefixWord ++ tailWord_246847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246847).length < 2 ^ (prefixWord ++ tailWord_246847).sum := by decide
  have hdescent : baseEnd_246847 < baseStart_246847 := by decide
  rcases family_descends (prefixWord ++ tailWord_246847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246861 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_246861 : Nat := 118140960795 + 246861 * 2 ^ 59
def prefixEnd_246861 : Nat := 4983230072969 + 3 ^ 40 * 246861 * 2
def baseEnd_246861 : Nat := 42252782616554629634071

theorem tailTrace_246861 : CollatzResearch.WordTrace tailWord_246861 prefixEnd_246861 42252782616554629634071 := by
  unfold tailWord_246861
  simp only [CollatzResearch.WordTrace]
  refine ⟨9003760358672232347340437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6002506905781488231560291 9003760358672232347340437)
  ·
    refine ⟨422051266812760891281583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9003760358672232347340437 422051266812760891281583)
    ·
      refine ⟨633076900219141336922375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422051266812760891281583 633076900219141336922375)
      ·
        refine ⟨949615350328712005383563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633076900219141336922375 949615350328712005383563)
        ·
          refine ⟨1424423025493068008075345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949615350328712005383563 1424423025493068008075345)
          ·
            refine ⟨1068317269119801006056509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424423025493068008075345 1068317269119801006056509)
            ·
              refine ⟨400618975919925377271191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068317269119801006056509 400618975919925377271191)
              ·
                refine ⟨600928463879888065906787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400618975919925377271191 600928463879888065906787)
                ·
                  refine ⟨901392695819832098860181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600928463879888065906787 901392695819832098860181)
                  ·
                    refine ⟨42252782616554629634071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 901392695819832098860181 42252782616554629634071)
                    ·
                      rfl

theorem cell23_246861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_246861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246861 prefixEnd_246861 := by exact prefixLift 246861
  have htrace : WordTrace (prefixWord ++ tailWord_246861) baseStart_246861 baseEnd_246861 := by
    simpa [prefixWord, tailWord_246861, baseEnd_246861] using wordTrace_append hprefix tailTrace_246861
  have hstable : (prefixWord ++ tailWord_246861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246861).length < 2 ^ (prefixWord ++ tailWord_246861).sum := by decide
  have hdescent : baseEnd_246861 < baseStart_246861 := by decide
  rcases family_descends (prefixWord ++ tailWord_246861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246868 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_246868 : Nat := 118140960795 + 246868 * 2 ^ 59
def prefixEnd_246868 : Nat := 4983230072969 + 3 ^ 40 * 246868 * 2
def baseEnd_246868 : Nat := 126761942214245361514681

theorem tailTrace_246868 : CollatzResearch.WordTrace tailWord_246868 prefixEnd_246868 126761942214245361514681 := by
  unfold tailWord_246868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502007834823436271422629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6002677113097915028563505 4502007834823436271422629)
  ·
    refine ⟨844126469029394300891743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4502007834823436271422629 844126469029394300891743)
    ·
      refine ⟨1266189703544091451337615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 844126469029394300891743 1266189703544091451337615)
      ·
        refine ⟨1899284555316137177006423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266189703544091451337615 1899284555316137177006423)
        ·
          refine ⟨2848926832974205765509635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899284555316137177006423 2848926832974205765509635)
          ·
            refine ⟨4273390249461308648264453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848926832974205765509635 4273390249461308648264453)
            ·
              refine ⟨801260671773995371549585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4273390249461308648264453 801260671773995371549585)
              ·
                refine ⟨600945503830496528662189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801260671773995371549585 600945503830496528662189)
                ·
                  refine ⟨225354563936436198248321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600945503830496528662189 225354563936436198248321)
                  ·
                    refine ⟨169015922952327148686241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225354563936436198248321 169015922952327148686241)
                    ·
                      refine ⟨126761942214245361514681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 169015922952327148686241 126761942214245361514681)
                      ·
                        rfl

theorem cell23_246868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_246868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246868 prefixEnd_246868 := by exact prefixLift 246868
  have htrace : WordTrace (prefixWord ++ tailWord_246868) baseStart_246868 baseEnd_246868 := by
    simpa [prefixWord, tailWord_246868, baseEnd_246868] using wordTrace_append hprefix tailTrace_246868
  have hstable : (prefixWord ++ tailWord_246868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246868).length < 2 ^ (prefixWord ++ tailWord_246868).sum := by decide
  have hdescent : baseEnd_246868 < baseStart_246868 := by decide
  rcases family_descends (prefixWord ++ tailWord_246868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246884 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_246884 : Nat := 118140960795 + 246884 * 2 ^ 59
def prefixEnd_246884 : Nat := 4983230072969 + 3 ^ 40 * 246884 * 2
def baseEnd_246884 : Nat := 126770157904717298914607

theorem tailTrace_246884 : CollatzResearch.WordTrace tailWord_246884 prefixEnd_246884 126770157904717298914607 := by
  unfold tailWord_246884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502299618794453637713853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6003066158392604850285137 4502299618794453637713853)
  ·
    refine ⟨1688362357047920114142695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4502299618794453637713853 1688362357047920114142695)
    ·
      refine ⟨2532543535571880171214043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688362357047920114142695 2532543535571880171214043)
      ·
        refine ⟨3798815303357820256821065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532543535571880171214043 3798815303357820256821065)
        ·
          refine ⟨2849111477518365192615799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798815303357820256821065 2849111477518365192615799)
          ·
            refine ⟨4273667216277547788923699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849111477518365192615799 4273667216277547788923699)
            ·
              refine ⟨6410500824416321683385549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273667216277547788923699 6410500824416321683385549)
              ·
                refine ⟨2403937809156120631269581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6410500824416321683385549 2403937809156120631269581)
                ·
                  refine ⟨901476678433545236726093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2403937809156120631269581 901476678433545236726093)
                  ·
                    refine ⟨338053754412579463772285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901476678433545236726093 338053754412579463772285)
                    ·
                      refine ⟨126770157904717298914607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 338053754412579463772285 126770157904717298914607)
                      ·
                        rfl

theorem cell23_246884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_246884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246884 prefixEnd_246884 := by exact prefixLift 246884
  have htrace : WordTrace (prefixWord ++ tailWord_246884) baseStart_246884 baseEnd_246884 := by
    simpa [prefixWord, tailWord_246884, baseEnd_246884] using wordTrace_append hprefix tailTrace_246884
  have hstable : (prefixWord ++ tailWord_246884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246884).length < 2 ^ (prefixWord ++ tailWord_246884).sum := by decide
  have hdescent : baseEnd_246884 < baseStart_246884 := by decide
  rcases family_descends (prefixWord ++ tailWord_246884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246888 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_246888 : Nat := 118140960795 + 246888 * 2 ^ 59
def prefixEnd_246888 : Nat := 4983230072969 + 3 ^ 40 * 246888 * 2
def baseEnd_246888 : Nat := 126772211827335283264589

theorem tailTrace_246888 : CollatzResearch.WordTrace tailWord_246888 prefixEnd_246888 126772211827335283264589 := by
  unfold tailWord_246888
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502372564787207979286659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6003163419716277305715545 4502372564787207979286659)
  ·
    refine ⟨6753558847180811968929989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4502372564787207979286659 6753558847180811968929989)
    ·
      refine ⟨1266292283846402244174373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6753558847180811968929989 1266292283846402244174373)
      ·
        refine ⟨237429803221200420782695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1266292283846402244174373 237429803221200420782695)
        ·
          refine ⟨356144704831800631174043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237429803221200420782695 356144704831800631174043)
          ·
            refine ⟨534217057247700946761065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356144704831800631174043 534217057247700946761065)
            ·
              refine ⟨400662792935775710070799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534217057247700946761065 400662792935775710070799)
              ·
                refine ⟨600994189403663565106199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400662792935775710070799 600994189403663565106199)
                ·
                  refine ⟨901491284105495347659299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600994189403663565106199 901491284105495347659299)
                  ·
                    refine ⟨1352236926158243021488949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 901491284105495347659299 1352236926158243021488949)
                    ·
                      refine ⟨126772211827335283264589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1352236926158243021488949 126772211827335283264589)
                      ·
                        rfl

theorem cell23_246888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_246888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246888 prefixEnd_246888 := by exact prefixLift 246888
  have htrace : WordTrace (prefixWord ++ tailWord_246888) baseStart_246888 baseEnd_246888 := by
    simpa [prefixWord, tailWord_246888, baseEnd_246888] using wordTrace_append hprefix tailTrace_246888
  have hstable : (prefixWord ++ tailWord_246888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246888).length < 2 ^ (prefixWord ++ tailWord_246888).sum := by decide
  have hdescent : baseEnd_246888 < baseStart_246888 := by decide
  rcases family_descends (prefixWord ++ tailWord_246888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246944 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_246944 : Nat := 118140960795 + 246944 * 2 ^ 59
def prefixEnd_246944 : Nat := 4983230072969 + 3 ^ 40 * 246944 * 2
def baseEnd_246944 : Nat := 126800966743987064164331

theorem tailTrace_246944 : CollatzResearch.WordTrace tailWord_246944 prefixEnd_246944 126800966743987064164331 := by
  unfold tailWord_246944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503393808685768761305943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6004525078247691681741257 4503393808685768761305943)
  ·
    refine ⟨6755090713028653141958915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4503393808685768761305943 6755090713028653141958915)
    ·
      refine ⟨10132636069542979712938373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6755090713028653141958915 10132636069542979712938373)
      ·
        refine ⟨1899869263039308696175945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10132636069542979712938373 1899869263039308696175945)
        ·
          refine ⟨1424901947279481522131959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899869263039308696175945 1424901947279481522131959)
          ·
            refine ⟨2137352920919222283197939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424901947279481522131959 2137352920919222283197939)
            ·
              refine ⟨3206029381378833424796909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137352920919222283197939 3206029381378833424796909)
              ·
                refine ⟨1202261018017062534298841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3206029381378833424796909 1202261018017062534298841)
                ·
                  refine ⟨901695763512796900724131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1202261018017062534298841 901695763512796900724131)
                  ·
                    refine ⟨1352543645269195351086197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 901695763512796900724131 1352543645269195351086197)
                    ·
                      refine ⟨126800966743987064164331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1352543645269195351086197 126800966743987064164331)
                      ·
                        rfl

theorem cell23_246944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_246944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246944 prefixEnd_246944 := by exact prefixLift 246944
  have htrace : WordTrace (prefixWord ++ tailWord_246944) baseStart_246944 baseEnd_246944 := by
    simpa [prefixWord, tailWord_246944, baseEnd_246944] using wordTrace_append hprefix tailTrace_246944
  have hstable : (prefixWord ++ tailWord_246944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246944).length < 2 ^ (prefixWord ++ tailWord_246944).sum := by decide
  have hdescent : baseEnd_246944 < baseStart_246944 := by decide
  rcases family_descends (prefixWord ++ tailWord_246944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246945 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_246945 : Nat := 118140960795 + 246945 * 2 ^ 59
def prefixEnd_246945 : Nat := 4983230072969 + 3 ^ 40 * 246945 * 2
def baseEnd_246945 : Nat := 126801480224641560251827

theorem tailTrace_246945 : CollatzResearch.WordTrace tailWord_246945 prefixEnd_246945 126801480224641560251827 := by
  unfold tailWord_246945
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006824090367914693398289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6004549393578609795598859 9006824090367914693398289)
  ·
    refine ⟨6755118067775936020048717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9006824090367914693398289 6755118067775936020048717)
    ·
      refine ⟨2533169275415976007518269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6755118067775936020048717 2533169275415976007518269)
      ·
        refine ⟨949938478280991002819351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2533169275415976007518269 949938478280991002819351)
        ·
          refine ⟨1424907717421486504229027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949938478280991002819351 1424907717421486504229027)
          ·
            refine ⟨2137361576132229756343541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424907717421486504229027 2137361576132229756343541)
            ·
              refine ⟨200377647762396539657207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2137361576132229756343541 200377647762396539657207)
              ·
                refine ⟨300566471643594809485811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200377647762396539657207 300566471643594809485811)
                ·
                  refine ⟨450849707465392214228717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300566471643594809485811 450849707465392214228717)
                  ·
                    refine ⟨169068640299522080335769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450849707465392214228717 169068640299522080335769)
                    ·
                      refine ⟨126801480224641560251827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 169068640299522080335769 126801480224641560251827)
                      ·
                        rfl

theorem cell23_246945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_246945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246945 prefixEnd_246945 := by exact prefixLift 246945
  have htrace : WordTrace (prefixWord ++ tailWord_246945) baseStart_246945 baseEnd_246945 := by
    simpa [prefixWord, tailWord_246945, baseEnd_246945] using wordTrace_append hprefix tailTrace_246945
  have hstable : (prefixWord ++ tailWord_246945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246945).length < 2 ^ (prefixWord ++ tailWord_246945).sum := by decide
  have hdescent : baseEnd_246945 < baseStart_246945 := by decide
  rcases family_descends (prefixWord ++ tailWord_246945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246961 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_246961 : Nat := 118140960795 + 246961 * 2 ^ 59
def prefixEnd_246961 : Nat := 4983230072969 + 3 ^ 40 * 246961 * 2
def baseEnd_246961 : Nat := 126809695915113497651753

theorem tailTrace_246961 : CollatzResearch.WordTrace tailWord_246961 prefixEnd_246961 126809695915113497651753 := by
  unfold tailWord_246961
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007407658309949425980737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6004938438873299617320491 9007407658309949425980737)
  ·
    refine ⟨6755555743732462069485553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9007407658309949425980737 6755555743732462069485553)
    ·
      refine ⟨5066666807799346552114165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6755555743732462069485553 5066666807799346552114165)
      ·
        refine ⟨475000013231188739260703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5066666807799346552114165 475000013231188739260703)
        ·
          refine ⟨712500019846783108891055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475000013231188739260703 712500019846783108891055)
          ·
            refine ⟨1068750029770174663336583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712500019846783108891055 1068750029770174663336583)
            ·
              refine ⟨1603125044655261995004875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068750029770174663336583 1603125044655261995004875)
              ·
                refine ⟨2404687566982892992507313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603125044655261995004875 2404687566982892992507313)
                ·
                  refine ⟨1803515675237169744380485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404687566982892992507313 1803515675237169744380485)
                  ·
                    refine ⟨338159189106969327071341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803515675237169744380485 338159189106969327071341)
                    ·
                      refine ⟨126809695915113497651753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 338159189106969327071341 126809695915113497651753)
                      ·
                        rfl

theorem cell23_246961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_246961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246961 prefixEnd_246961 := by exact prefixLift 246961
  have htrace : WordTrace (prefixWord ++ tailWord_246961) baseStart_246961 baseEnd_246961 := by
    simpa [prefixWord, tailWord_246961, baseEnd_246961] using wordTrace_append hprefix tailTrace_246961
  have hstable : (prefixWord ++ tailWord_246961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246961).length < 2 ^ (prefixWord ++ tailWord_246961).sum := by decide
  have hdescent : baseEnd_246961 < baseStart_246961 := by decide
  rcases family_descends (prefixWord ++ tailWord_246961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246996 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_246996 : Nat := 118140960795 + 246996 * 2 ^ 59
def prefixEnd_246996 : Nat := 4983230072969 + 3 ^ 40 * 246996 * 2
def baseEnd_246996 : Nat := 126827667738020860714093

theorem tailTrace_246996 : CollatzResearch.WordTrace tailWord_246996 prefixEnd_246996 126827667738020860714093 := by
  unfold tailWord_246996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504342106591575201752421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6005789475455433602336561 4504342106591575201752421)
  ·
    refine ⟨844564144985920350328579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4504342106591575201752421 844564144985920350328579)
    ·
      refine ⟨1266846217478880525492869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 844564144985920350328579 1266846217478880525492869)
      ·
        refine ⟨237533665777290098529913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1266846217478880525492869 237533665777290098529913)
        ·
          refine ⟨178150249332967573897435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237533665777290098529913 178150249332967573897435)
          ·
            refine ⟨267225373999451360846153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178150249332967573897435 267225373999451360846153)
            ·
              refine ⟨200419030499588520634615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267225373999451360846153 200419030499588520634615)
              ·
                refine ⟨300628545749382780951923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200419030499588520634615 300628545749382780951923)
                ·
                  refine ⟨450942818624074171427885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300628545749382780951923 450942818624074171427885)
                  ·
                    refine ⟨169103556984027814285457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450942818624074171427885 169103556984027814285457)
                    ·
                      refine ⟨126827667738020860714093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 169103556984027814285457 126827667738020860714093)
                      ·
                        rfl

theorem cell23_246996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_246996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_246996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_246996 prefixEnd_246996 := by exact prefixLift 246996
  have htrace : WordTrace (prefixWord ++ tailWord_246996) baseStart_246996 baseEnd_246996 := by
    simpa [prefixWord, tailWord_246996, baseEnd_246996] using wordTrace_append hprefix tailTrace_246996
  have hstable : (prefixWord ++ tailWord_246996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246996).length < 2 ^ (prefixWord ++ tailWord_246996).sum := by decide
  have hdescent : baseEnd_246996 < baseStart_246996 := by decide
  rcases family_descends (prefixWord ++ tailWord_246996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247051 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 3]
def baseStart_247051 : Nat := 118140960795 + 247051 * 2 ^ 59
def prefixEnd_247051 : Nat := 4983230072969 + 3 ^ 40 * 247051 * 2
def baseEnd_247051 : Nat := 126855909174018145526339

theorem tailTrace_247051 : CollatzResearch.WordTrace tailWord_247051 prefixEnd_247051 126855909174018145526339 := by
  unfold tailWord_247051
  simp only [CollatzResearch.WordTrace]
  refine ⟨9010690227983894796757007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6007126818655929864504671 9010690227983894796757007)
  ·
    refine ⟨13516035341975842195135511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9010690227983894796757007 13516035341975842195135511)
    ·
      refine ⟨20274053012963763292703267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13516035341975842195135511 20274053012963763292703267)
      ·
        refine ⟨30411079519445644939054901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20274053012963763292703267 30411079519445644939054901)
        ·
          refine ⟨2851038704948029213036397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30411079519445644939054901 2851038704948029213036397)
          ·
            refine ⟨1069139514355510954888649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2851038704948029213036397 1069139514355510954888649)
            ·
              refine ⟨801854635766633216166487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069139514355510954888649 801854635766633216166487)
              ·
                refine ⟨1202781953649949824249731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801854635766633216166487 1202781953649949824249731)
                ·
                  refine ⟨1804172930474924736374597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202781953649949824249731 1804172930474924736374597)
                  ·
                    refine ⟨338282424464048388070237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1804172930474924736374597 338282424464048388070237)
                    ·
                      refine ⟨126855909174018145526339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 338282424464048388070237 126855909174018145526339)
                      ·
                        rfl

theorem cell23_247051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 3].length) (baseStart_247051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247051 prefixEnd_247051 := by exact prefixLift 247051
  have htrace : WordTrace (prefixWord ++ tailWord_247051) baseStart_247051 baseEnd_247051 := by
    simpa [prefixWord, tailWord_247051, baseEnd_247051] using wordTrace_append hprefix tailTrace_247051
  have hstable : (prefixWord ++ tailWord_247051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247051).length < 2 ^ (prefixWord ++ tailWord_247051).sum := by decide
  have hdescent : baseEnd_247051 < baseStart_247051 := by decide
  rcases family_descends (prefixWord ++ tailWord_247051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247084 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_247084 : Nat := 118140960795 + 247084 * 2 ^ 59
def prefixEnd_247084 : Nat := 4983230072969 + 3 ^ 40 * 247084 * 2
def baseEnd_247084 : Nat := 42290951345205505471229

theorem tailTrace_247084 : CollatzResearch.WordTrace tailWord_247084 prefixEnd_247084 42290951345205505471229 := by
  unfold tailWord_247084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4505946918432170716354153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6007929224576227621805537 4505946918432170716354153)
  ·
    refine ⟨3379460188824128037265615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4505946918432170716354153 3379460188824128037265615)
    ·
      refine ⟨5069190283236192055898423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379460188824128037265615 5069190283236192055898423)
      ·
        refine ⟨7603785424854288083847635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069190283236192055898423 7603785424854288083847635)
        ·
          refine ⟨11405678137281432125771453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603785424854288083847635 11405678137281432125771453)
          ·
            refine ⟨4277129301480537047164295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11405678137281432125771453 4277129301480537047164295)
            ·
              refine ⟨6415693952220805570746443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277129301480537047164295 6415693952220805570746443)
              ·
                refine ⟨9623540928331208356119665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415693952220805570746443 9623540928331208356119665)
                ·
                  refine ⟨7217655696248406267089749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9623540928331208356119665 7217655696248406267089749)
                  ·
                    refine ⟨42290951345205505471229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 7217655696248406267089749 42290951345205505471229)
                    ·
                      rfl

theorem cell23_247084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_247084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247084 prefixEnd_247084 := by exact prefixLift 247084
  have htrace : WordTrace (prefixWord ++ tailWord_247084) baseStart_247084 baseEnd_247084 := by
    simpa [prefixWord, tailWord_247084, baseEnd_247084] using wordTrace_append hprefix tailTrace_247084
  have hstable : (prefixWord ++ tailWord_247084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247084).length < 2 ^ (prefixWord ++ tailWord_247084).sum := by decide
  have hdescent : baseEnd_247084 < baseStart_247084 := by decide
  rcases family_descends (prefixWord ++ tailWord_247084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247098 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_247098 : Nat := 118140960795 + 247098 * 2 ^ 59
def prefixEnd_247098 : Nat := 4983230072969 + 3 ^ 40 * 247098 * 2
def baseEnd_247098 : Nat := 126880042764779461638623

theorem tailTrace_247098 : CollatzResearch.WordTrace tailWord_247098 prefixEnd_247098 126880042764779461638623 := by
  unfold tailWord_247098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253101114703405455929487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6008269639209081215811965 2253101114703405455929487)
  ·
    refine ⟨3379651672055108183894231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2253101114703405455929487 3379651672055108183894231)
    ·
      refine ⟨5069477508082662275841347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379651672055108183894231 5069477508082662275841347)
      ·
        refine ⟨7604216262123993413762021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069477508082662275841347 7604216262123993413762021)
        ·
          refine ⟨1425790549148248765080379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7604216262123993413762021 1425790549148248765080379)
          ·
            refine ⟨2138685823722373147620569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425790549148248765080379 2138685823722373147620569)
            ·
              refine ⟨1604014367791779860715427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138685823722373147620569 1604014367791779860715427)
              ·
                refine ⟨2406021551687669791073141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604014367791779860715427 2406021551687669791073141)
                ·
                  refine ⟨225564520470719042913107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2406021551687669791073141 225564520470719042913107)
                  ·
                    refine ⟨338346780706078564369661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225564520470719042913107 338346780706078564369661)
                    ·
                      refine ⟨126880042764779461638623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 338346780706078564369661 126880042764779461638623)
                      ·
                        rfl

theorem cell23_247098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_247098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247098 prefixEnd_247098 := by exact prefixLift 247098
  have htrace : WordTrace (prefixWord ++ tailWord_247098) baseStart_247098 baseEnd_247098 := by
    simpa [prefixWord, tailWord_247098, baseEnd_247098] using wordTrace_append hprefix tailTrace_247098
  have hstable : (prefixWord ++ tailWord_247098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247098).length < 2 ^ (prefixWord ++ tailWord_247098).sum := by decide
  have hdescent : baseEnd_247098 < baseStart_247098 := by decide
  rcases family_descends (prefixWord ++ tailWord_247098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247125 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_247125 : Nat := 118140960795 + 247125 * 2 ^ 59
def prefixEnd_247125 : Nat := 4983230072969 + 3 ^ 40 * 247125 * 2
def baseEnd_247125 : Nat := 126893906742450856000999

theorem tailTrace_247125 : CollatzResearch.WordTrace tailWord_247125 prefixEnd_247125 126893906742450856000999 := by
  unfold tailWord_247125
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013389229715805434950829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6008926153143870289967219 9013389229715805434950829)
  ·
    refine ⟨3380020961143427038106561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9013389229715805434950829 3380020961143427038106561)
    ·
      refine ⟨2535015720857570278579921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3380020961143427038106561 2535015720857570278579921)
      ·
        refine ⟨1901261790643177708934941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535015720857570278579921 1901261790643177708934941)
        ·
          refine ⟨712973171491191640850603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1901261790643177708934941 712973171491191640850603)
          ·
            refine ⟨1069459757236787461275905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712973171491191640850603 1069459757236787461275905)
            ·
              refine ⟨802094817927590595956929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069459757236787461275905 802094817927590595956929)
              ·
                refine ⟨601571113445692946967697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802094817927590595956929 601571113445692946967697)
                ·
                  refine ⟨451178335084269710225773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601571113445692946967697 451178335084269710225773)
                  ·
                    refine ⟨169191875656601141334665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451178335084269710225773 169191875656601141334665)
                    ·
                      refine ⟨126893906742450856000999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 169191875656601141334665 126893906742450856000999)
                      ·
                        rfl

theorem cell23_247125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_247125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247125 prefixEnd_247125 := by exact prefixLift 247125
  have htrace : WordTrace (prefixWord ++ tailWord_247125) baseStart_247125 baseEnd_247125 := by
    simpa [prefixWord, tailWord_247125, baseEnd_247125] using wordTrace_append hprefix tailTrace_247125
  have hstable : (prefixWord ++ tailWord_247125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247125).length < 2 ^ (prefixWord ++ tailWord_247125).sum := by decide
  have hdescent : baseEnd_247125 < baseStart_247125 := by decide
  rcases family_descends (prefixWord ++ tailWord_247125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247138 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_247138 : Nat := 118140960795 + 247138 * 2 ^ 59
def prefixEnd_247138 : Nat := 4983230072969 + 3 ^ 40 * 247138 * 2
def baseEnd_247138 : Nat := 126900581990959305138439

theorem tailTrace_247138 : CollatzResearch.WordTrace tailWord_247138 prefixEnd_247138 126900581990959305138439 := by
  unfold tailWord_247138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253465844667177163793517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6009242252445805770116045 2253465844667177163793517)
  ·
    refine ⟨845049691750191436422569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2253465844667177163793517 845049691750191436422569)
    ·
      refine ⟨633787268812643577316927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845049691750191436422569 633787268812643577316927)
      ·
        refine ⟨950680903218965365975391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633787268812643577316927 950680903218965365975391)
        ·
          refine ⟨1426021354828448048963087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950680903218965365975391 1426021354828448048963087)
          ·
            refine ⟨2139032032242672073444631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426021354828448048963087 2139032032242672073444631)
            ·
              refine ⟨3208548048364008110166947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139032032242672073444631 3208548048364008110166947)
              ·
                refine ⟨4812822072546012165250421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208548048364008110166947 4812822072546012165250421)
                ·
                  refine ⟨451202069301188640492227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4812822072546012165250421 451202069301188640492227)
                  ·
                    refine ⟨676803103951782960738341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 451202069301188640492227 676803103951782960738341)
                    ·
                      refine ⟨126900581990959305138439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 676803103951782960738341 126900581990959305138439)
                      ·
                        rfl

theorem cell23_247138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_247138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247138 prefixEnd_247138 := by exact prefixLift 247138
  have htrace : WordTrace (prefixWord ++ tailWord_247138) baseStart_247138 baseEnd_247138 := by
    simpa [prefixWord, tailWord_247138, baseEnd_247138] using wordTrace_append hprefix tailTrace_247138
  have hstable : (prefixWord ++ tailWord_247138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247138).length < 2 ^ (prefixWord ++ tailWord_247138).sum := by decide
  have hdescent : baseEnd_247138 < baseStart_247138 := by decide
  rcases family_descends (prefixWord ++ tailWord_247138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247141 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_247141 : Nat := 118140960795 + 247141 * 2 ^ 59
def prefixEnd_247141 : Nat := 4983230072969 + 3 ^ 40 * 247141 * 2
def baseEnd_247141 : Nat := 126902122432922793400925

theorem tailTrace_247141 : CollatzResearch.WordTrace tailWord_247141 prefixEnd_247141 126902122432922793400925 := by
  unfold tailWord_247141
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013972797657840167533277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6009315198438560111688851 9013972797657840167533277)
  ·
    refine ⟨3380239799121690062824979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9013972797657840167533277 3380239799121690062824979)
    ·
      refine ⟨5070359698682535094237469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3380239799121690062824979 5070359698682535094237469)
      ·
        refine ⟨1901384887005950660339051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5070359698682535094237469 1901384887005950660339051)
        ·
          refine ⟨2852077330508925990508577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901384887005950660339051 2852077330508925990508577)
          ·
            refine ⟨2139057997881694492881433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852077330508925990508577 2139057997881694492881433)
            ·
              refine ⟨1604293498411270869661075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139057997881694492881433 1604293498411270869661075)
              ·
                refine ⟨2406440247616906304491613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604293498411270869661075 2406440247616906304491613)
                ·
                  refine ⟨902415092856339864184355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2406440247616906304491613 902415092856339864184355)
                  ·
                    refine ⟨1353622639284509796276533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 902415092856339864184355 1353622639284509796276533)
                    ·
                      refine ⟨126902122432922793400925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1353622639284509796276533 126902122432922793400925)
                      ·
                        rfl

theorem cell23_247141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_247141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247141 prefixEnd_247141 := by exact prefixLift 247141
  have htrace : WordTrace (prefixWord ++ tailWord_247141) baseStart_247141 baseEnd_247141 := by
    simpa [prefixWord, tailWord_247141, baseEnd_247141] using wordTrace_append hprefix tailTrace_247141
  have hstable : (prefixWord ++ tailWord_247141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247141).length < 2 ^ (prefixWord ++ tailWord_247141).sum := by decide
  have hdescent : baseEnd_247141 < baseStart_247141 := by decide
  rcases family_descends (prefixWord ++ tailWord_247141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247148 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_247148 : Nat := 118140960795 + 247148 * 2 ^ 59
def prefixEnd_247148 : Nat := 4983230072969 + 3 ^ 40 * 247148 * 2
def baseEnd_247148 : Nat := 42301905599168088671131

theorem tailTrace_247148 : CollatzResearch.WordTrace tailWord_247148 prefixEnd_247148 42301905599168088671131 := by
  unfold tailWord_247148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507114054316240181519049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6009485405754986908692065 4507114054316240181519049)
  ·
    refine ⟨3380335540737180136139287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4507114054316240181519049 3380335540737180136139287)
    ·
      refine ⟨5070503311105770204208931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3380335540737180136139287 5070503311105770204208931)
      ·
        refine ⟨7605754966658655306313397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070503311105770204208931 7605754966658655306313397)
        ·
          refine ⟨713039528124248934966881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7605754966658655306313397 713039528124248934966881)
          ·
            refine ⟨534779646093186701225161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713039528124248934966881 534779646093186701225161)
            ·
              refine ⟨401084734569890025918871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534779646093186701225161 401084734569890025918871)
              ·
                refine ⟨601627101854835038878307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401084734569890025918871 601627101854835038878307)
                ·
                  refine ⟨902440652782252558317461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601627101854835038878307 902440652782252558317461)
                  ·
                    refine ⟨42301905599168088671131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 902440652782252558317461 42301905599168088671131)
                    ·
                      rfl

theorem cell23_247148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_247148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247148 prefixEnd_247148 := by exact prefixLift 247148
  have htrace : WordTrace (prefixWord ++ tailWord_247148) baseStart_247148 baseEnd_247148 := by
    simpa [prefixWord, tailWord_247148, baseEnd_247148] using wordTrace_append hprefix tailTrace_247148
  have hstable : (prefixWord ++ tailWord_247148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247148).length < 2 ^ (prefixWord ++ tailWord_247148).sum := by decide
  have hdescent : baseEnd_247148 < baseStart_247148 := by decide
  rcases family_descends (prefixWord ++ tailWord_247148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247169 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 1, 5]
def baseStart_247169 : Nat := 118140960795 + 247169 * 2 ^ 59
def prefixEnd_247169 : Nat := 4983230072969 + 3 ^ 40 * 247169 * 2
def baseEnd_247169 : Nat := 42305499963749561283599

theorem tailTrace_247169 : CollatzResearch.WordTrace tailWord_247169 prefixEnd_247169 42305499963749561283599 := by
  unfold tailWord_247169
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014994041556400949552561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6009996027704267299701707 9014994041556400949552561)
  ·
    refine ⟨6761245531167300712164421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9014994041556400949552561 6761245531167300712164421)
    ·
      refine ⟨1267733537093868883530829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6761245531167300712164421 1267733537093868883530829)
      ·
        refine ⟨475400076410200831324061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1267733537093868883530829 475400076410200831324061)
        ·
          refine ⟨178275028653825311746523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475400076410200831324061 178275028653825311746523)
          ·
            refine ⟨267412542980737967619785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178275028653825311746523 267412542980737967619785)
            ·
              refine ⟨200559407235553475714839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267412542980737967619785 200559407235553475714839)
              ·
                refine ⟨300839110853330213572259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200559407235553475714839 300839110853330213572259)
                ·
                  refine ⟨451258666279995320358389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300839110853330213572259 451258666279995320358389)
                  ·
                    refine ⟨42305499963749561283599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 451258666279995320358389 42305499963749561283599)
                    ·
                      rfl

theorem cell23_247169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_247169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247169 prefixEnd_247169 := by exact prefixLift 247169
  have htrace : WordTrace (prefixWord ++ tailWord_247169) baseStart_247169 baseEnd_247169 := by
    simpa [prefixWord, tailWord_247169, baseEnd_247169] using wordTrace_append hprefix tailTrace_247169
  have hstable : (prefixWord ++ tailWord_247169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247169).length < 2 ^ (prefixWord ++ tailWord_247169).sum := by decide
  have hdescent : baseEnd_247169 < baseStart_247169 := by decide
  rcases family_descends (prefixWord ++ tailWord_247169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247172 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_247172 : Nat := 118140960795 + 247172 * 2 ^ 59
def prefixEnd_247172 : Nat := 4983230072969 + 3 ^ 40 * 247172 * 2
def baseEnd_247172 : Nat := 126918040333212172113283

theorem tailTrace_247172 : CollatzResearch.WordTrace tailWord_247172 prefixEnd_247172 126918040333212172113283 := by
  unfold tailWord_247172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507551730272766230955885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6010068973697021641274513 4507551730272766230955885)
  ·
    refine ⟨1690331898852287336608457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4507551730272766230955885 1690331898852287336608457)
    ·
      refine ⟨1267748924139215502456343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1690331898852287336608457 1267748924139215502456343)
      ·
        refine ⟨1901623386208823253684515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267748924139215502456343 1901623386208823253684515)
        ·
          refine ⟨2852435079313234880526773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901623386208823253684515 2852435079313234880526773)
          ·
            refine ⟨267415788685615770049385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2852435079313234880526773 267415788685615770049385)
            ·
              refine ⟨200561841514211827537039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267415788685615770049385 200561841514211827537039)
              ·
                refine ⟨300842762271317741305559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200561841514211827537039 300842762271317741305559)
                ·
                  refine ⟨451264143406976611958339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300842762271317741305559 451264143406976611958339)
                  ·
                    refine ⟨676896215110464917937509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 451264143406976611958339 676896215110464917937509)
                    ·
                      refine ⟨126918040333212172113283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 676896215110464917937509 126918040333212172113283)
                      ·
                        rfl

theorem cell23_247172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_247172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247172 prefixEnd_247172 := by exact prefixLift 247172
  have htrace : WordTrace (prefixWord ++ tailWord_247172) baseStart_247172 baseEnd_247172 := by
    simpa [prefixWord, tailWord_247172, baseEnd_247172] using wordTrace_append hprefix tailTrace_247172
  have hstable : (prefixWord ++ tailWord_247172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247172).length < 2 ^ (prefixWord ++ tailWord_247172).sum := by decide
  have hdescent : baseEnd_247172 < baseStart_247172 := by decide
  rcases family_descends (prefixWord ++ tailWord_247172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247175 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_247175 : Nat := 118140960795 + 247175 * 2 ^ 59
def prefixEnd_247175 : Nat := 4983230072969 + 3 ^ 40 * 247175 * 2
def baseEnd_247175 : Nat := 126919580775175660375769

theorem tailTrace_247175 : CollatzResearch.WordTrace tailWord_247175 prefixEnd_247175 126919580775175660375769 := by
  unfold tailWord_247175
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015212879534663974270979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6010141919689775982847319 9015212879534663974270979)
  ·
    refine ⟨13522819319301995961406469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9015212879534663974270979 13522819319301995961406469)
    ·
      refine ⟨2535528622369124242763713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13522819319301995961406469 2535528622369124242763713)
      ·
        refine ⟨1901646466776843182072785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535528622369124242763713 1901646466776843182072785)
        ·
          refine ⟨1426234850082632386554589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1901646466776843182072785 1426234850082632386554589)
          ·
            refine ⟨534838068780987144957971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1426234850082632386554589 534838068780987144957971)
            ·
              refine ⟨802257103171480717436957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534838068780987144957971 802257103171480717436957)
              ·
                refine ⟨300846413689305269038859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802257103171480717436957 300846413689305269038859)
                ·
                  refine ⟨451269620533957903558289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300846413689305269038859 451269620533957903558289)
                  ·
                    refine ⟨338452215400468427668717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 451269620533957903558289 338452215400468427668717)
                    ·
                      refine ⟨126919580775175660375769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 338452215400468427668717 126919580775175660375769)
                      ·
                        rfl

theorem cell23_247175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_247175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247175 prefixEnd_247175 := by exact prefixLift 247175
  have htrace : WordTrace (prefixWord ++ tailWord_247175) baseStart_247175 baseEnd_247175 := by
    simpa [prefixWord, tailWord_247175, baseEnd_247175] using wordTrace_append hprefix tailTrace_247175
  have hstable : (prefixWord ++ tailWord_247175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247175).length < 2 ^ (prefixWord ++ tailWord_247175).sum := by decide
  have hdescent : baseEnd_247175 < baseStart_247175 := by decide
  rcases family_descends (prefixWord ++ tailWord_247175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247291 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7]
def baseStart_247291 : Nat := 118140960795 + 247291 * 2 ^ 59
def prefixEnd_247291 : Nat := 4983230072969 + 3 ^ 40 * 247291 * 2
def baseEnd_247291 : Nat := 126979144531097206525235

theorem tailTrace_247291 : CollatzResearch.WordTrace tailWord_247291 prefixEnd_247291 126979144531097206525235 := by
  unfold tailWord_247291
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019443747114415785493727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6012962498076277190329151 9019443747114415785493727)
  ·
    refine ⟨13529165620671623678240591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9019443747114415785493727 13529165620671623678240591)
    ·
      refine ⟨20293748431007435517360887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13529165620671623678240591 20293748431007435517360887)
      ·
        refine ⟨30440622646511153276041331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20293748431007435517360887 30440622646511153276041331)
        ·
          refine ⟨45660933969766729914061997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30440622646511153276041331 45660933969766729914061997)
          ·
            refine ⟨17122850238662523717773249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45660933969766729914061997 17122850238662523717773249)
            ·
              refine ⟨12842137678996892788329937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17122850238662523717773249 12842137678996892788329937)
              ·
                refine ⟨9631603259247669591247453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12842137678996892788329937 9631603259247669591247453)
                ·
                  refine ⟨3611851222217876096717795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9631603259247669591247453 3611851222217876096717795)
                  ·
                    refine ⟨5417776833326814145076693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3611851222217876096717795 5417776833326814145076693)
                    ·
                      refine ⟨126979144531097206525235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5417776833326814145076693 126979144531097206525235)
                      ·
                        rfl

theorem cell23_247291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_247291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247291 prefixEnd_247291 := by exact prefixLift 247291
  have htrace : WordTrace (prefixWord ++ tailWord_247291) baseStart_247291 baseEnd_247291 := by
    simpa [prefixWord, tailWord_247291, baseEnd_247291] using wordTrace_append hprefix tailTrace_247291
  have hstable : (prefixWord ++ tailWord_247291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247291).length < 2 ^ (prefixWord ++ tailWord_247291).sum := by decide
  have hdescent : baseEnd_247291 < baseStart_247291 := by decide
  rcases family_descends (prefixWord ++ tailWord_247291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247309 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_247309 : Nat := 118140960795 + 247309 * 2 ^ 59
def prefixEnd_247309 : Nat := 4983230072969 + 3 ^ 40 * 247309 * 2
def baseEnd_247309 : Nat := 126988387182878136100153

theorem tailTrace_247309 : CollatzResearch.WordTrace tailWord_247309 prefixEnd_247309 126988387182878136100153 := by
  unfold tailWord_247309
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020100261049204859648981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6013400174032803239765987 9020100261049204859648981)
  ·
    refine ⟨211408599868340738898023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9020100261049204859648981 211408599868340738898023)
    ·
      refine ⟨317112899802511108347035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211408599868340738898023 317112899802511108347035)
      ·
        refine ⟨475669349703766662520553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317112899802511108347035 475669349703766662520553)
        ·
          refine ⟨356752012277824996890415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475669349703766662520553 356752012277824996890415)
          ·
            refine ⟨535128018416737495335623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356752012277824996890415 535128018416737495335623)
            ·
              refine ⟨802692027625106243003435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535128018416737495335623 802692027625106243003435)
              ·
                refine ⟨1204038041437659364505153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802692027625106243003435 1204038041437659364505153)
                ·
                  refine ⟨903028531078244523378865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204038041437659364505153 903028531078244523378865)
                  ·
                    refine ⟨677271398308683392534149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 903028531078244523378865 677271398308683392534149)
                    ·
                      refine ⟨126988387182878136100153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 677271398308683392534149 126988387182878136100153)
                      ·
                        rfl

theorem cell23_247309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_247309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247309 prefixEnd_247309 := by exact prefixLift 247309
  have htrace : WordTrace (prefixWord ++ tailWord_247309) baseStart_247309 baseEnd_247309 := by
    simpa [prefixWord, tailWord_247309, baseEnd_247309] using wordTrace_append hprefix tailTrace_247309
  have hstable : (prefixWord ++ tailWord_247309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247309).length < 2 ^ (prefixWord ++ tailWord_247309).sum := by decide
  have hdescent : baseEnd_247309 < baseStart_247309 := by decide
  rcases family_descends (prefixWord ++ tailWord_247309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247418 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_247418 : Nat := 118140960795 + 247418 * 2 ^ 59
def prefixEnd_247418 : Nat := 4983230072969 + 3 ^ 40 * 247418 * 2
def baseEnd_247418 : Nat := 42348118858072736545717

theorem tailTrace_247418 : CollatzResearch.WordTrace tailWord_247418 prefixEnd_247418 42348118858072736545717 := by
  unfold tailWord_247418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256018954413579118841727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6016050545102877650244605 2256018954413579118841727)
  ·
    refine ⟨3384028431620368678262591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2256018954413579118841727 3384028431620368678262591)
    ·
      refine ⟨5076042647430553017393887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3384028431620368678262591 5076042647430553017393887)
      ·
        refine ⟨7614063971145829526090831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076042647430553017393887 7614063971145829526090831)
        ·
          refine ⟨11421095956718744289136247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614063971145829526090831 11421095956718744289136247)
          ·
            refine ⟨17131643935078116433704371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421095956718744289136247 17131643935078116433704371)
            ·
              refine ⟨25697465902617174650556557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131643935078116433704371 25697465902617174650556557)
              ·
                refine ⟨9636549713481440493958709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25697465902617174650556557 9636549713481440493958709)
                ·
                  refine ⟨903426535638885046308629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9636549713481440493958709 903426535638885046308629)
                  ·
                    refine ⟨42348118858072736545717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 903426535638885046308629 42348118858072736545717)
                    ·
                      rfl

theorem cell23_247418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_247418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247418 prefixEnd_247418 := by exact prefixLift 247418
  have htrace : WordTrace (prefixWord ++ tailWord_247418) baseStart_247418 baseEnd_247418 := by
    simpa [prefixWord, tailWord_247418, baseEnd_247418] using wordTrace_append hprefix tailTrace_247418
  have hstable : (prefixWord ++ tailWord_247418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247418).length < 2 ^ (prefixWord ++ tailWord_247418).sum := by decide
  have hdescent : baseEnd_247418 < baseStart_247418 := by decide
  rcases family_descends (prefixWord ++ tailWord_247418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247452 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_247452 : Nat := 118140960795 + 247452 * 2 ^ 59
def prefixEnd_247452 : Nat := 4983230072969 + 3 ^ 40 * 247452 * 2
def baseEnd_247452 : Nat := 42353938305490358870665

theorem tailTrace_247452 : CollatzResearch.WordTrace tailWord_247452 prefixEnd_247452 42353938305490358870665 := by
  unfold tailWord_247452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512657949765570141052305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6016877266354093521403073 4512657949765570141052305)
  ·
    refine ⟨3384493462324177605789229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4512657949765570141052305 3384493462324177605789229)
    ·
      refine ⟨1269185048371566602170961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3384493462324177605789229 1269185048371566602170961)
      ·
        refine ⟨951888786278674951628221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269185048371566602170961 951888786278674951628221)
        ·
          refine ⟨356958294854503106860583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 951888786278674951628221 356958294854503106860583)
          ·
            refine ⟨535437442281754660290875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356958294854503106860583 535437442281754660290875)
            ·
              refine ⟨803156163422631990436313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535437442281754660290875 803156163422631990436313)
              ·
                refine ⟨602367122566973992827235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803156163422631990436313 602367122566973992827235)
                ·
                  refine ⟨903550683850460989240853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602367122566973992827235 903550683850460989240853)
                  ·
                    refine ⟨42353938305490358870665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 903550683850460989240853 42353938305490358870665)
                    ·
                      rfl

theorem cell23_247452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_247452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247452 prefixEnd_247452 := by exact prefixLift 247452
  have htrace : WordTrace (prefixWord ++ tailWord_247452) baseStart_247452 baseEnd_247452 := by
    simpa [prefixWord, tailWord_247452, baseEnd_247452] using wordTrace_append hprefix tailTrace_247452
  have hstable : (prefixWord ++ tailWord_247452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247452).length < 2 ^ (prefixWord ++ tailWord_247452).sum := by decide
  have hdescent : baseEnd_247452 < baseStart_247452 := by decide
  rcases family_descends (prefixWord ++ tailWord_247452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247468 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_247468 : Nat := 118140960795 + 247468 * 2 ^ 59
def prefixEnd_247468 : Nat := 4983230072969 + 3 ^ 40 * 247468 * 2
def baseEnd_247468 : Nat := 127070030606943014011921

theorem tailTrace_247468 : CollatzResearch.WordTrace tailWord_247468 prefixEnd_247468 127070030606943014011921 := by
  unfold tailWord_247468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512949733736587507343529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6017266311648783343124705 4512949733736587507343529)
  ·
    refine ⟨3384712300302440630507647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4512949733736587507343529 3384712300302440630507647)
    ·
      refine ⟨5077068450453660945761471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3384712300302440630507647 5077068450453660945761471)
      ·
        refine ⟨7615602675680491418642207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077068450453660945761471 7615602675680491418642207)
        ·
          refine ⟨11423404013520737127963311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615602675680491418642207 11423404013520737127963311)
          ·
            refine ⟨17135106020281105691944967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11423404013520737127963311 17135106020281105691944967)
            ·
              refine ⟨25702659030421658537917451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135106020281105691944967 25702659030421658537917451)
              ·
                refine ⟨38553988545632487806876177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25702659030421658537917451 38553988545632487806876177)
                ·
                  refine ⟨28915491409224365855157133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38553988545632487806876177 28915491409224365855157133)
                  ·
                    refine ⟨10843309278459137195683925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28915491409224365855157133 10843309278459137195683925)
                    ·
                      refine ⟨127070030606943014011921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 10843309278459137195683925 127070030606943014011921)
                      ·
                        rfl

theorem cell23_247468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_247468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247468 prefixEnd_247468 := by exact prefixLift 247468
  have htrace : WordTrace (prefixWord ++ tailWord_247468) baseStart_247468 baseEnd_247468 := by
    simpa [prefixWord, tailWord_247468, baseEnd_247468] using wordTrace_append hprefix tailTrace_247468
  have hstable : (prefixWord ++ tailWord_247468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247468).length < 2 ^ (prefixWord ++ tailWord_247468).sum := by decide
  have hdescent : baseEnd_247468 < baseStart_247468 := by decide
  rcases family_descends (prefixWord ++ tailWord_247468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247469 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_247469 : Nat := 118140960795 + 247469 * 2 ^ 59
def prefixEnd_247469 : Nat := 4983230072969 + 3 ^ 40 * 247469 * 2
def baseEnd_247469 : Nat := 42356848029199170033139

theorem tailTrace_247469 : CollatzResearch.WordTrace tailWord_247469 prefixEnd_247469 42356848029199170033139 := by
  unfold tailWord_247469
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025935940469552185473461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6017290626979701456982307 9025935940469552185473461)
  ·
    refine ⟨846181494419020517388137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9025935940469552185473461 846181494419020517388137)
    ·
      refine ⟨634636120814265388041103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 846181494419020517388137 634636120814265388041103)
      ·
        refine ⟨951954181221398082061655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634636120814265388041103 951954181221398082061655)
        ·
          refine ⟨1427931271832097123092483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951954181221398082061655 1427931271832097123092483)
          ·
            refine ⟨2141896907748145684638725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427931271832097123092483 2141896907748145684638725)
            ·
              refine ⟨401605670202777315869761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2141896907748145684638725 401605670202777315869761)
              ·
                refine ⟨301204252652082986902321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401605670202777315869761 301204252652082986902321)
                ·
                  refine ⟨225903189489062240176741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301204252652082986902321 225903189489062240176741)
                  ·
                    refine ⟨42356848029199170033139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225903189489062240176741 42356848029199170033139)
                    ·
                      rfl

theorem cell23_247469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_247469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247469 prefixEnd_247469 := by exact prefixLift 247469
  have htrace : WordTrace (prefixWord ++ tailWord_247469) baseStart_247469 baseEnd_247469 := by
    simpa [prefixWord, tailWord_247469, baseEnd_247469] using wordTrace_append hprefix tailTrace_247469
  have hstable : (prefixWord ++ tailWord_247469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247469).length < 2 ^ (prefixWord ++ tailWord_247469).sum := by decide
  have hdescent : baseEnd_247469 < baseStart_247469 := by decide
  rcases family_descends (prefixWord ++ tailWord_247469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247475 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 3]
def baseStart_247475 : Nat := 118140960795 + 247475 * 2 ^ 59
def prefixEnd_247475 : Nat := 4983230072969 + 3 ^ 40 * 247475 * 2
def baseEnd_247475 : Nat := 127073624971524486624389

theorem tailTrace_247475 : CollatzResearch.WordTrace tailWord_247475 prefixEnd_247475 127073624971524486624389 := by
  unfold tailWord_247475
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026154778447815210191879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6017436518965210140127919 9026154778447815210191879)
  ·
    refine ⟨13539232167671722815287819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9026154778447815210191879 13539232167671722815287819)
    ·
      refine ⟨20308848251507584222931729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13539232167671722815287819 20308848251507584222931729)
      ·
        refine ⟨15231636188630688167198797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20308848251507584222931729 15231636188630688167198797)
        ·
          refine ⟨5711863570736508062699549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15231636188630688167198797 5711863570736508062699549)
          ·
            refine ⟨2141948839026190523512331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5711863570736508062699549 2141948839026190523512331)
            ·
              refine ⟨3212923258539285785268497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141948839026190523512331 3212923258539285785268497)
              ·
                refine ⟨2409692443904464338951373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212923258539285785268497 2409692443904464338951373)
                ·
                  refine ⟨903634666464174127106765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2409692443904464338951373 903634666464174127106765)
                  ·
                    refine ⟨338862999924065297665037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903634666464174127106765 338862999924065297665037)
                    ·
                      refine ⟨127073624971524486624389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 338862999924065297665037 127073624971524486624389)
                      ·
                        rfl

theorem cell23_247475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_247475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247475 prefixEnd_247475 := by exact prefixLift 247475
  have htrace : WordTrace (prefixWord ++ tailWord_247475) baseStart_247475 baseEnd_247475 := by
    simpa [prefixWord, tailWord_247475, baseEnd_247475] using wordTrace_append hprefix tailTrace_247475
  have hstable : (prefixWord ++ tailWord_247475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247475).length < 2 ^ (prefixWord ++ tailWord_247475).sum := by decide
  have hdescent : baseEnd_247475 < baseStart_247475 := by decide
  rcases family_descends (prefixWord ++ tailWord_247475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247510 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_247510 : Nat := 118140960795 + 247510 * 2 ^ 59
def prefixEnd_247510 : Nat := 4983230072969 + 3 ^ 40 * 247510 * 2
def baseEnd_247510 : Nat := 127091596794431849686729

theorem tailTrace_247510 : CollatzResearch.WordTrace tailWord_247510 prefixEnd_247510 127091596794431849686729 := by
  unfold tailWord_247510
  simp only [CollatzResearch.WordTrace]
  refine ⟨564214458332563511732249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6018287555547344125143989 564214458332563511732249)
  ·
    refine ⟨423160843749422633799187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 564214458332563511732249 423160843749422633799187)
    ·
      refine ⟨634741265624133950698781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423160843749422633799187 634741265624133950698781)
      ·
        refine ⟨238027974609050231512043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634741265624133950698781 238027974609050231512043)
        ·
          refine ⟨357041961913575347268065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238027974609050231512043 357041961913575347268065)
          ·
            refine ⟨267781471435181510451049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357041961913575347268065 267781471435181510451049)
            ·
              refine ⟨200836103576386132838287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267781471435181510451049 200836103576386132838287)
              ·
                refine ⟨301254155364579199257431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200836103576386132838287 301254155364579199257431)
                ·
                  refine ⟨451881233046868798886147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301254155364579199257431 451881233046868798886147)
                  ·
                    refine ⟨677821849570303198329221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 451881233046868798886147 677821849570303198329221)
                    ·
                      refine ⟨127091596794431849686729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 677821849570303198329221 127091596794431849686729)
                      ·
                        rfl

theorem cell23_247510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_247510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247510 prefixEnd_247510 := by exact prefixLift 247510
  have htrace : WordTrace (prefixWord ++ tailWord_247510) baseStart_247510 baseEnd_247510 := by
    simpa [prefixWord, tailWord_247510, baseEnd_247510] using wordTrace_append hprefix tailTrace_247510
  have hstable : (prefixWord ++ tailWord_247510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247510).length < 2 ^ (prefixWord ++ tailWord_247510).sum := by decide
  have hdescent : baseEnd_247510 < baseStart_247510 := by decide
  rcases family_descends (prefixWord ++ tailWord_247510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247519 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 1, 3, 2]
def baseStart_247519 : Nat := 118140960795 + 247519 * 2 ^ 59
def prefixEnd_247519 : Nat := 4983230072969 + 3 ^ 40 * 247519 * 2
def baseEnd_247519 : Nat := 127096218120322314474187

theorem tailTrace_247519 : CollatzResearch.WordTrace tailWord_247519 prefixEnd_247519 127096218120322314474187 := by
  unfold tailWord_247519
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027759590288410724793611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6018506393525607149862407 9027759590288410724793611)
  ·
    refine ⟨13541639385432616087190417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9027759590288410724793611 13541639385432616087190417)
    ·
      refine ⟨10156229539074462065392813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13541639385432616087190417 10156229539074462065392813)
      ·
        refine ⟨3808586077152923274522305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10156229539074462065392813 3808586077152923274522305)
        ·
          refine ⟨2856439557864692455891729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3808586077152923274522305 2856439557864692455891729)
          ·
            refine ⟨2142329668398519341918797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2856439557864692455891729 2142329668398519341918797)
            ·
              refine ⟨803373625649444753219549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2142329668398519341918797 803373625649444753219549)
              ·
                refine ⟨301265109618541782457331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 803373625649444753219549 301265109618541782457331)
                ·
                  refine ⟨451897664427812673685997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301265109618541782457331 451897664427812673685997)
                  ·
                    refine ⟨169461624160429752632249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451897664427812673685997 169461624160429752632249)
                    ·
                      refine ⟨127096218120322314474187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 169461624160429752632249 127096218120322314474187)
                      ·
                        rfl

theorem cell23_247519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_247519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247519 prefixEnd_247519 := by exact prefixLift 247519
  have htrace : WordTrace (prefixWord ++ tailWord_247519) baseStart_247519 baseEnd_247519 := by
    simpa [prefixWord, tailWord_247519, baseEnd_247519] using wordTrace_append hprefix tailTrace_247519
  have hstable : (prefixWord ++ tailWord_247519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247519).length < 2 ^ (prefixWord ++ tailWord_247519).sum := by decide
  have hdescent : baseEnd_247519 < baseStart_247519 := by decide
  rcases family_descends (prefixWord ++ tailWord_247519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247525 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_247525 : Nat := 118140960795 + 247525 * 2 ^ 59
def prefixEnd_247525 : Nat := 4983230072969 + 3 ^ 40 * 247525 * 2
def baseEnd_247525 : Nat := 42366433001416430333053

theorem tailTrace_247525 : CollatzResearch.WordTrace tailWord_247525 prefixEnd_247525 42366433001416430333053 := by
  unfold tailWord_247525
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027978428266673749512029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6018652285511115833008019 9027978428266673749512029)
  ·
    refine ⟨3385491910600002656067011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9027978428266673749512029 3385491910600002656067011)
    ·
      refine ⟨5078237865900003984100517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385491910600002656067011 5078237865900003984100517)
      ·
        refine ⟨952169599856250747018847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5078237865900003984100517 952169599856250747018847)
        ·
          refine ⟨1428254399784376120528271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952169599856250747018847 1428254399784376120528271)
          ·
            refine ⟨2142381599676564180792407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428254399784376120528271 2142381599676564180792407)
            ·
              refine ⟨3213572399514846271188611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142381599676564180792407 3213572399514846271188611)
              ·
                refine ⟨4820358599272269406782917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213572399514846271188611 4820358599272269406782917)
                ·
                  refine ⟨903817237363550513771797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4820358599272269406782917 903817237363550513771797)
                  ·
                    refine ⟨42366433001416430333053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 903817237363550513771797 42366433001416430333053)
                    ·
                      rfl

theorem cell23_247525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_247525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247525 prefixEnd_247525 := by exact prefixLift 247525
  have htrace : WordTrace (prefixWord ++ tailWord_247525) baseStart_247525 baseEnd_247525 := by
    simpa [prefixWord, tailWord_247525, baseEnd_247525] using wordTrace_append hprefix tailTrace_247525
  have hstable : (prefixWord ++ tailWord_247525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247525).length < 2 ^ (prefixWord ++ tailWord_247525).sum := by decide
  have hdescent : baseEnd_247525 < baseStart_247525 := by decide
  rcases family_descends (prefixWord ++ tailWord_247525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247532 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 3, 4, 2]
def baseStart_247532 : Nat := 118140960795 + 247532 * 2 ^ 59
def prefixEnd_247532 : Nat := 4983230072969 + 3 ^ 40 * 247532 * 2
def baseEnd_247532 : Nat := 127102893368830763611627

theorem tailTrace_247532 : CollatzResearch.WordTrace tailWord_247532 prefixEnd_247532 127102893368830763611627 := by
  unfold tailWord_247532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514116869620656972508425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6018822492827542630011233 4514116869620656972508425)
  ·
    refine ⟨3385587652215492729381319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4514116869620656972508425 3385587652215492729381319)
    ·
      refine ⟨5078381478323239094071979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385587652215492729381319 5078381478323239094071979)
      ·
        refine ⟨7617572217484858641107969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078381478323239094071979 7617572217484858641107969)
        ·
          refine ⟨5713179163113643980830977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7617572217484858641107969 5713179163113643980830977)
          ·
            refine ⟨4284884372335232985623233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5713179163113643980830977 4284884372335232985623233)
            ·
              refine ⟨3213663279251424739217425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4284884372335232985623233 3213663279251424739217425)
              ·
                refine ⟨2410247459438568554413069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213663279251424739217425 2410247459438568554413069)
                ·
                  refine ⟨903842797289463207904901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2410247459438568554413069 903842797289463207904901)
                  ·
                    refine ⟨169470524491774351482169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 903842797289463207904901 169470524491774351482169)
                    ·
                      refine ⟨127102893368830763611627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 169470524491774351482169 127102893368830763611627)
                      ·
                        rfl

theorem cell23_247532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_247532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247532 prefixEnd_247532 := by exact prefixLift 247532
  have htrace : WordTrace (prefixWord ++ tailWord_247532) baseStart_247532 baseEnd_247532 := by
    simpa [prefixWord, tailWord_247532, baseEnd_247532] using wordTrace_append hprefix tailTrace_247532
  have hstable : (prefixWord ++ tailWord_247532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247532).length < 2 ^ (prefixWord ++ tailWord_247532).sum := by decide
  have hdescent : baseEnd_247532 < baseStart_247532 := by decide
  rcases family_descends (prefixWord ++ tailWord_247532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247542 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_247542 : Nat := 118140960795 + 247542 * 2 ^ 59
def prefixEnd_247542 : Nat := 4983230072969 + 3 ^ 40 * 247542 * 2
def baseEnd_247542 : Nat := 42369342725125241495527

theorem tailTrace_247542 : CollatzResearch.WordTrace tailWord_247542 prefixEnd_247542 42369342725125241495527 := by
  unfold tailWord_247542
  simp only [CollatzResearch.WordTrace]
  refine ⟨564287404325317853305055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6019065646136723768587253 564287404325317853305055)
  ·
    refine ⟨846431106487976779957583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564287404325317853305055 846431106487976779957583)
    ·
      refine ⟨1269646659731965169936375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846431106487976779957583 1269646659731965169936375)
      ·
        refine ⟨1904469989597947754904563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269646659731965169936375 1904469989597947754904563)
        ·
          refine ⟨2856704984396921632356845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904469989597947754904563 2856704984396921632356845)
          ·
            refine ⟨1071264369148845612133817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2856704984396921632356845 1071264369148845612133817)
            ·
              refine ⟨803448276861634209100363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071264369148845612133817 803448276861634209100363)
              ·
                refine ⟨1205172415292451313650545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803448276861634209100363 1205172415292451313650545)
                ·
                  refine ⟨903879311469338485237909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1205172415292451313650545 903879311469338485237909)
                  ·
                    refine ⟨42369342725125241495527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 903879311469338485237909 42369342725125241495527)
                    ·
                      rfl

theorem cell23_247542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_247542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247542 prefixEnd_247542 := by exact prefixLift 247542
  have htrace : WordTrace (prefixWord ++ tailWord_247542) baseStart_247542 baseEnd_247542 := by
    simpa [prefixWord, tailWord_247542, baseEnd_247542] using wordTrace_append hprefix tailTrace_247542
  have hstable : (prefixWord ++ tailWord_247542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247542).length < 2 ^ (prefixWord ++ tailWord_247542).sum := by decide
  have hdescent : baseEnd_247542 < baseStart_247542 := by decide
  rcases family_descends (prefixWord ++ tailWord_247542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247555 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 7]
def baseStart_247555 : Nat := 118140960795 + 247555 * 2 ^ 59
def prefixEnd_247555 : Nat := 4983230072969 + 3 ^ 40 * 247555 * 2
def baseEnd_247555 : Nat := 14123855935987130402669

theorem tailTrace_247555 : CollatzResearch.WordTrace tailWord_247555 prefixEnd_247555 14123855935987130402669 := by
  unfold tailWord_247555
  simp only [CollatzResearch.WordTrace]
  refine ⟨9029072618157988873104119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6019381745438659248736079 9029072618157988873104119)
  ·
    refine ⟨13543608927236983309656179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9029072618157988873104119 13543608927236983309656179)
    ·
      refine ⟨20315413390855474964484269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13543608927236983309656179 20315413390855474964484269)
      ·
        refine ⟨7618280021570803111681601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20315413390855474964484269 7618280021570803111681601)
        ·
          refine ⟨5713710016178102333761201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7618280021570803111681601 5713710016178102333761201)
          ·
            refine ⟨4285282512133576750320901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5713710016178102333761201 4285282512133576750320901)
            ·
              refine ⟨803490471025045640685169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4285282512133576750320901 803490471025045640685169)
              ·
                refine ⟨602617853268784230513877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803490471025045640685169 602617853268784230513877)
                ·
                  refine ⟨14123855935987130402669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 602617853268784230513877 14123855935987130402669)
                  ·
                    rfl

theorem cell23_247555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 7].length) (baseStart_247555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247555 prefixEnd_247555 := by exact prefixLift 247555
  have htrace : WordTrace (prefixWord ++ tailWord_247555) baseStart_247555 baseEnd_247555 := by
    simpa [prefixWord, tailWord_247555, baseEnd_247555] using wordTrace_append hprefix tailTrace_247555
  have hstable : (prefixWord ++ tailWord_247555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247555).length < 2 ^ (prefixWord ++ tailWord_247555).sum := by decide
  have hdescent : baseEnd_247555 < baseStart_247555 := by decide
  rcases family_descends (prefixWord ++ tailWord_247555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247629 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_247629 : Nat := 118140960795 + 247629 * 2 ^ 59
def prefixEnd_247629 : Nat := 4983230072969 + 3 ^ 40 * 247629 * 2
def baseEnd_247629 : Nat := 127152700992316884098681

theorem tailTrace_247629 : CollatzResearch.WordTrace tailWord_247629 prefixEnd_247629 127152700992316884098681 := by
  unfold tailWord_247629
  simp only [CollatzResearch.WordTrace]
  refine ⟨9031771619889899511297941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6021181079926599674198627 9031771619889899511297941)
  ·
    refine ⟨423364294682339039592091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9031771619889899511297941 423364294682339039592091)
    ·
      refine ⟨635046442023508559388137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423364294682339039592091 635046442023508559388137)
      ·
        refine ⟨476284831517631419541103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635046442023508559388137 476284831517631419541103)
        ·
          refine ⟨714427247276447129311655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476284831517631419541103 714427247276447129311655)
          ·
            refine ⟨1071640870914670693967483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714427247276447129311655 1071640870914670693967483)
            ·
              refine ⟨1607461306372006040951225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071640870914670693967483 1607461306372006040951225)
              ·
                refine ⟨1205595979779004530713419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607461306372006040951225 1205595979779004530713419)
                ·
                  refine ⟨1808393969668506796070129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205595979779004530713419 1808393969668506796070129)
                  ·
                    refine ⟨1356295477251380097052597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808393969668506796070129 1356295477251380097052597)
                    ·
                      refine ⟨127152700992316884098681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1356295477251380097052597 127152700992316884098681)
                      ·
                        rfl

theorem cell23_247629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_247629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247629 prefixEnd_247629 := by exact prefixLift 247629
  have htrace : WordTrace (prefixWord ++ tailWord_247629) baseStart_247629 baseEnd_247629 := by
    simpa [prefixWord, tailWord_247629, baseEnd_247629] using wordTrace_append hprefix tailTrace_247629
  have hstable : (prefixWord ++ tailWord_247629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247629).length < 2 ^ (prefixWord ++ tailWord_247629).sum := by decide
  have hdescent : baseEnd_247629 < baseStart_247629 := by decide
  rcases family_descends (prefixWord ++ tailWord_247629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247689 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 3]
def baseStart_247689 : Nat := 118140960795 + 247689 * 2 ^ 59
def prefixEnd_247689 : Nat := 4983230072969 + 3 ^ 40 * 247689 * 2
def baseEnd_247689 : Nat := 127183509831586649348405

theorem tailTrace_247689 : CollatzResearch.WordTrace tailWord_247689 prefixEnd_247689 127183509831586649348405 := by
  unfold tailWord_247689
  simp only [CollatzResearch.WordTrace]
  refine ⟨9033959999672529758482121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6022639999781686505654747 9033959999672529758482121)
  ·
    refine ⟨6775469999754397318861591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9033959999672529758482121 6775469999754397318861591)
    ·
      refine ⟨10163204999631595978292387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775469999754397318861591 10163204999631595978292387)
      ·
        refine ⟨15244807499447393967438581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10163204999631595978292387 15244807499447393967438581)
        ·
          refine ⟨1429200703073193184447367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15244807499447393967438581 1429200703073193184447367)
          ·
            refine ⟨2143801054609789776671051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429200703073193184447367 2143801054609789776671051)
            ·
              refine ⟨3215701581914684665006577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143801054609789776671051 3215701581914684665006577)
              ·
                refine ⟨2411776186436013498754933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215701581914684665006577 2411776186436013498754933)
                ·
                  refine ⟨226104017478376265508275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2411776186436013498754933 226104017478376265508275)
                  ·
                    refine ⟨339156026217564398262413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226104017478376265508275 339156026217564398262413)
                    ·
                      refine ⟨127183509831586649348405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 339156026217564398262413 127183509831586649348405)
                      ·
                        rfl

theorem cell23_247689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 3].length) (baseStart_247689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247689 prefixEnd_247689 := by exact prefixLift 247689
  have htrace : WordTrace (prefixWord ++ tailWord_247689) baseStart_247689 baseEnd_247689 := by
    simpa [prefixWord, tailWord_247689, baseEnd_247689] using wordTrace_append hprefix tailTrace_247689
  have hstable : (prefixWord ++ tailWord_247689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247689).length < 2 ^ (prefixWord ++ tailWord_247689).sum := by decide
  have hdescent : baseEnd_247689 < baseStart_247689 := by decide
  rcases family_descends (prefixWord ++ tailWord_247689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247706 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_247706 : Nat := 118140960795 + 247706 * 2 ^ 59
def prefixEnd_247706 : Nat := 4983230072969 + 3 ^ 40 * 247706 * 2
def baseEnd_247706 : Nat := 127192239002713082835827

theorem tailTrace_247706 : CollatzResearch.WordTrace tailWord_247706 prefixEnd_247706 127192239002713082835827 := by
  unfold tailWord_247706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258645010152735415462743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6023053360407294441233981 2258645010152735415462743)
  ·
    refine ⟨3387967515229103123194115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2258645010152735415462743 3387967515229103123194115)
    ·
      refine ⟨5081951272843654684791173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387967515229103123194115 5081951272843654684791173)
      ·
        refine ⟨952865863658185253398345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5081951272843654684791173 952865863658185253398345)
        ·
          refine ⟨714649397743638940048759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952865863658185253398345 714649397743638940048759)
          ·
            refine ⟨1071974096615458410073139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714649397743638940048759 1071974096615458410073139)
            ·
              refine ⟨1607961144923187615109709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071974096615458410073139 1607961144923187615109709)
              ·
                refine ⟨602985429346195355666141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607961144923187615109709 602985429346195355666141)
                ·
                  refine ⟨226119536004823258374803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602985429346195355666141 226119536004823258374803)
                  ·
                    refine ⟨339179304007234887562205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226119536004823258374803 339179304007234887562205)
                    ·
                      refine ⟨127192239002713082835827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 339179304007234887562205 127192239002713082835827)
                      ·
                        rfl

theorem cell23_247706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_247706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247706 prefixEnd_247706 := by exact prefixLift 247706
  have htrace : WordTrace (prefixWord ++ tailWord_247706) baseStart_247706 baseEnd_247706 := by
    simpa [prefixWord, tailWord_247706, baseEnd_247706] using wordTrace_append hprefix tailTrace_247706
  have hstable : (prefixWord ++ tailWord_247706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247706).length < 2 ^ (prefixWord ++ tailWord_247706).sum := by decide
  have hdescent : baseEnd_247706 < baseStart_247706 := by decide
  rcases family_descends (prefixWord ++ tailWord_247706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247752 : List Nat := [2, 1, 3, 1, 4, 1, 11]
def baseStart_247752 : Nat := 118140960795 + 247752 * 2 ^ 59
def prefixEnd_247752 : Nat := 4983230072969 + 3 ^ 40 * 247752 * 2
def baseEnd_247752 : Nat := 1570566161886665467415

theorem tailTrace_247752 : CollatzResearch.WordTrace tailWord_247752 prefixEnd_247752 1570566161886665467415 := by
  unfold tailWord_247752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518128899222145759012755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6024171865629527678683673 4518128899222145759012755)
  ·
    refine ⟨6777193348833218638519133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4518128899222145759012755 6777193348833218638519133)
    ·
      refine ⟨2541447505812456989444675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6777193348833218638519133 2541447505812456989444675)
      ·
        refine ⟨3812171258718685484167013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541447505812456989444675 3812171258718685484167013)
        ·
          refine ⟨714782111009753528281315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3812171258718685484167013 714782111009753528281315)
          ·
            refine ⟨1072173166514630292421973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714782111009753528281315 1072173166514630292421973)
            ·
              refine ⟨1570566161886665467415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1072173166514630292421973 1570566161886665467415)
              ·
                rfl

theorem cell23_247752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 11].length) (baseStart_247752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247752 prefixEnd_247752 := by exact prefixLift 247752
  have htrace : WordTrace (prefixWord ++ tailWord_247752) baseStart_247752 baseEnd_247752 := by
    simpa [prefixWord, tailWord_247752, baseEnd_247752] using wordTrace_append hprefix tailTrace_247752
  have hstable : (prefixWord ++ tailWord_247752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247752).length < 2 ^ (prefixWord ++ tailWord_247752).sum := by decide
  have hdescent : baseEnd_247752 < baseStart_247752 := by decide
  rcases family_descends (prefixWord ++ tailWord_247752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247769 : List Nat := [1, 2, 1, 2, 6, 1, 2, 8]
def baseStart_247769 : Nat := 118140960795 + 247769 * 2 ^ 59
def prefixEnd_247769 : Nat := 4983230072969 + 3 ^ 40 * 247769 * 2
def baseEnd_247769 : Nat := 4712021788294308753631

theorem tailTrace_247769 : CollatzResearch.WordTrace tailWord_247769 prefixEnd_247769 4712021788294308753631 := by
  unfold tailWord_247769
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036877839382703421394361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6024585226255135614262907 9036877839382703421394361)
  ·
    refine ⟨6777658379537027566045771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9036877839382703421394361 6777658379537027566045771)
    ·
      refine ⟨10166487569305541349068657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777658379537027566045771 10166487569305541349068657)
      ·
        refine ⟨7624865676979156011801493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10166487569305541349068657 7624865676979156011801493)
        ·
          refine ⟨357415578608397938053195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7624865676979156011801493 357415578608397938053195)
          ·
            refine ⟨536123367912596907079793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357415578608397938053195 536123367912596907079793)
            ·
              refine ⟨402092525934447680309845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536123367912596907079793 402092525934447680309845)
              ·
                refine ⟨4712021788294308753631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 402092525934447680309845 4712021788294308753631)
                ·
                  rfl

theorem cell23_247769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 8].length) (baseStart_247769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247769 prefixEnd_247769 := by exact prefixLift 247769
  have htrace : WordTrace (prefixWord ++ tailWord_247769) baseStart_247769 baseEnd_247769 := by
    simpa [prefixWord, tailWord_247769, baseEnd_247769] using wordTrace_append hprefix tailTrace_247769
  have hstable : (prefixWord ++ tailWord_247769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247769).length < 2 ^ (prefixWord ++ tailWord_247769).sum := by decide
  have hdescent : baseEnd_247769 < baseStart_247769 := by decide
  rcases family_descends (prefixWord ++ tailWord_247769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247773 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_247773 : Nat := 118140960795 + 247773 * 2 ^ 59
def prefixEnd_247773 : Nat := 4983230072969 + 3 ^ 40 * 247773 * 2
def baseEnd_247773 : Nat := 42408880735521440232673

theorem tailTrace_247773 : CollatzResearch.WordTrace tailWord_247773 prefixEnd_247773 42408880735521440232673 := by
  unfold tailWord_247773
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037023731368212104539973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6024682487578808069693315 9037023731368212104539973)
  ·
    refine ⟨1694441949631539769601245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9037023731368212104539973 1694441949631539769601245)
    ·
      refine ⟨635415731111827413600467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1694441949631539769601245 635415731111827413600467)
      ·
        refine ⟨953123596667741120400701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635415731111827413600467 953123596667741120400701)
        ·
          refine ⟨357421348750402920150263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953123596667741120400701 357421348750402920150263)
          ·
            refine ⟨536132023125604380225395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357421348750402920150263 536132023125604380225395)
            ·
              refine ⟨804198034688406570338093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536132023125604380225395 804198034688406570338093)
              ·
                refine ⟨301574263008152463876785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 804198034688406570338093 301574263008152463876785)
                ·
                  refine ⟨226180697256114347907589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301574263008152463876785 226180697256114347907589)
                  ·
                    refine ⟨42408880735521440232673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226180697256114347907589 42408880735521440232673)
                    ·
                      rfl

theorem cell23_247773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_247773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247773 prefixEnd_247773 := by exact prefixLift 247773
  have htrace : WordTrace (prefixWord ++ tailWord_247773) baseStart_247773 baseEnd_247773 := by
    simpa [prefixWord, tailWord_247773, baseEnd_247773] using wordTrace_append hprefix tailTrace_247773
  have hstable : (prefixWord ++ tailWord_247773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247773).length < 2 ^ (prefixWord ++ tailWord_247773).sum := by decide
  have hdescent : baseEnd_247773 < baseStart_247773 := by decide
  rcases family_descends (prefixWord ++ tailWord_247773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247792 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_247792 : Nat := 118140960795 + 247792 * 2 ^ 59
def prefixEnd_247792 : Nat := 4983230072969 + 3 ^ 40 * 247792 * 2
def baseEnd_247792 : Nat := 127236398338999746360431

theorem tailTrace_247792 : CollatzResearch.WordTrace tailWord_247792 prefixEnd_247792 127236398338999746360431 := by
  unfold tailWord_247792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518858359149689174740815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6025144478866252232987753 4518858359149689174740815)
  ·
    refine ⟨6778287538724533762111223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4518858359149689174740815 6778287538724533762111223)
    ·
      refine ⟨10167431308086800643166835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6778287538724533762111223 10167431308086800643166835)
      ·
        refine ⟨15251146962130200964750253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10167431308086800643166835 15251146962130200964750253)
        ·
          refine ⟨5719180110798825361781345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15251146962130200964750253 5719180110798825361781345)
          ·
            refine ⟨4289385083099119021336009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719180110798825361781345 4289385083099119021336009)
            ·
              refine ⟨3217038812324339266002007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4289385083099119021336009 3217038812324339266002007)
              ·
                refine ⟨4825558218486508899003011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217038812324339266002007 4825558218486508899003011)
                ·
                  refine ⟨7238337327729763348504517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825558218486508899003011 7238337327729763348504517)
                  ·
                    refine ⟨1357188248949330627844597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238337327729763348504517 1357188248949330627844597)
                    ·
                      refine ⟨127236398338999746360431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1357188248949330627844597 127236398338999746360431)
                      ·
                        rfl

theorem cell23_247792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_247792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247792 prefixEnd_247792 := by exact prefixLift 247792
  have htrace : WordTrace (prefixWord ++ tailWord_247792) baseStart_247792 baseEnd_247792 := by
    simpa [prefixWord, tailWord_247792, baseEnd_247792] using wordTrace_append hprefix tailTrace_247792
  have hstable : (prefixWord ++ tailWord_247792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247792).length < 2 ^ (prefixWord ++ tailWord_247792).sum := by decide
  have hdescent : baseEnd_247792 < baseStart_247792 := by decide
  rcases family_descends (prefixWord ++ tailWord_247792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247813 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_247813 : Nat := 118140960795 + 247813 * 2 ^ 59
def prefixEnd_247813 : Nat := 4983230072969 + 3 ^ 40 * 247813 * 2
def baseEnd_247813 : Nat := 127247181432744164197835

theorem tailTrace_247813 : CollatzResearch.WordTrace tailWord_247813 prefixEnd_247813 127247181432744164197835 := by
  unfold tailWord_247813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038482651223298935996093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6025655100815532623997395 9038482651223298935996093)
  ·
    refine ⟨3389430994208737100998535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9038482651223298935996093 3389430994208737100998535)
    ·
      refine ⟨5084146491313105651497803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389430994208737100998535 5084146491313105651497803)
      ·
        refine ⟨7626219736969658477246705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084146491313105651497803 7626219736969658477246705)
        ·
          refine ⟨5719664802727243857935029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7626219736969658477246705 5719664802727243857935029)
          ·
            refine ⟨536218575255679111681409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5719664802727243857935029 536218575255679111681409)
            ·
              refine ⟨402163931441759333761057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536218575255679111681409 402163931441759333761057)
              ·
                refine ⟨301622948581319500320793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402163931441759333761057 301622948581319500320793)
                ·
                  refine ⟨226217211435989625240595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301622948581319500320793 226217211435989625240595)
                  ·
                    refine ⟨339325817153984437860893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226217211435989625240595 339325817153984437860893)
                    ·
                      refine ⟨127247181432744164197835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 339325817153984437860893 127247181432744164197835)
                      ·
                        rfl

theorem cell23_247813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_247813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247813 prefixEnd_247813 := by exact prefixLift 247813
  have htrace : WordTrace (prefixWord ++ tailWord_247813) baseStart_247813 baseEnd_247813 := by
    simpa [prefixWord, tailWord_247813, baseEnd_247813] using wordTrace_append hprefix tailTrace_247813
  have hstable : (prefixWord ++ tailWord_247813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247813).length < 2 ^ (prefixWord ++ tailWord_247813).sum := by decide
  have hdescent : baseEnd_247813 < baseStart_247813 := by decide
  rcases family_descends (prefixWord ++ tailWord_247813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247839 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 3]
def baseStart_247839 : Nat := 118140960795 + 247839 * 2 ^ 59
def prefixEnd_247839 : Nat := 4983230072969 + 3 ^ 40 * 247839 * 2
def baseEnd_247839 : Nat := 127260531929761062472715

theorem tailTrace_247839 : CollatzResearch.WordTrace tailWord_247839 prefixEnd_247839 127260531929761062472715 := by
  unfold tailWord_247839
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039430949129105376442571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6026287299419403584295047 9039430949129105376442571)
  ·
    refine ⟨13559146423693658064663857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039430949129105376442571 13559146423693658064663857)
    ·
      refine ⟨10169359817770243548497893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13559146423693658064663857 10169359817770243548497893)
      ·
        refine ⟨1906754965831920665343355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10169359817770243548497893 1906754965831920665343355)
        ·
          refine ⟨2860132448747880998015033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906754965831920665343355 2860132448747880998015033)
          ·
            refine ⟨2145099336560910748511275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2860132448747880998015033 2145099336560910748511275)
            ·
              refine ⟨3217649004841366122766913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145099336560910748511275 3217649004841366122766913)
              ·
                refine ⟨2413236753631024592075185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217649004841366122766913 2413236753631024592075185)
                ·
                  refine ⟨1809927565223268444056389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2413236753631024592075185 1809927565223268444056389)
                  ·
                    refine ⟨339361418479362833260573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1809927565223268444056389 339361418479362833260573)
                    ·
                      refine ⟨127260531929761062472715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 339361418479362833260573 127260531929761062472715)
                      ·
                        rfl

theorem cell23_247839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_247839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247839 prefixEnd_247839 := by exact prefixLift 247839
  have htrace : WordTrace (prefixWord ++ tailWord_247839) baseStart_247839 baseEnd_247839 := by
    simpa [prefixWord, tailWord_247839, baseEnd_247839] using wordTrace_append hprefix tailTrace_247839
  have hstable : (prefixWord ++ tailWord_247839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247839).length < 2 ^ (prefixWord ++ tailWord_247839).sum := by decide
  have hdescent : baseEnd_247839 < baseStart_247839 := by decide
  rcases family_descends (prefixWord ++ tailWord_247839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247886 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_247886 : Nat := 118140960795 + 247886 * 2 ^ 59
def prefixEnd_247886 : Nat := 4983230072969 + 3 ^ 40 * 247886 * 2
def baseEnd_247886 : Nat := 127284665520522378584999

theorem tailTrace_247886 : CollatzResearch.WordTrace tailWord_247886 prefixEnd_247886 127284665520522378584999 := by
  unfold tailWord_247886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130143147494854050425439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6027430119972554935602341 1130143147494854050425439)
  ·
    refine ⟨1695214721242281075638159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1130143147494854050425439 1695214721242281075638159)
    ·
      refine ⟨2542822081863421613457239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695214721242281075638159 2542822081863421613457239)
      ·
        refine ⟨3814233122795132420185859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542822081863421613457239 3814233122795132420185859)
        ·
          refine ⟨5721349684192698630278789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3814233122795132420185859 5721349684192698630278789)
          ·
            refine ⟨1072753065786130993177273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5721349684192698630278789 1072753065786130993177273)
            ·
              refine ⟨804564799339598244882955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072753065786130993177273 804564799339598244882955)
              ·
                refine ⟨1206847199009397367324433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804564799339598244882955 1206847199009397367324433)
                ·
                  refine ⟨905135399257048025493325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206847199009397367324433 905135399257048025493325)
                  ·
                    refine ⟨339425774721393009559997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905135399257048025493325 339425774721393009559997)
                    ·
                      refine ⟨127284665520522378584999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 339425774721393009559997 127284665520522378584999)
                      ·
                        rfl

theorem cell23_247886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_247886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247886 prefixEnd_247886 := by exact prefixLift 247886
  have htrace : WordTrace (prefixWord ++ tailWord_247886) baseStart_247886 baseEnd_247886 := by
    simpa [prefixWord, tailWord_247886, baseEnd_247886] using wordTrace_append hprefix tailTrace_247886
  have hstable : (prefixWord ++ tailWord_247886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247886).length < 2 ^ (prefixWord ++ tailWord_247886).sum := by decide
  have hdescent : baseEnd_247886 < baseStart_247886 := by decide
  rcases family_descends (prefixWord ++ tailWord_247886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247993 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 3]
def baseStart_247993 : Nat := 118140960795 + 247993 * 2 ^ 59
def prefixEnd_247993 : Nat := 4983230072969 + 3 ^ 40 * 247993 * 2
def baseEnd_247993 : Nat := 127339607950553459947007

theorem tailTrace_247993 : CollatzResearch.WordTrace tailWord_247993 prefixEnd_247993 127339607950553459947007 := by
  unfold tailWord_247993
  simp only [CollatzResearch.WordTrace]
  refine ⟨9045047790571189677548633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6030031860380793118365755 9045047790571189677548633)
  ·
    refine ⟨6783785842928392258161475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9045047790571189677548633 6783785842928392258161475)
    ·
      refine ⟨10175678764392588387242213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783785842928392258161475 10175678764392588387242213)
      ·
        refine ⟨1907939768323610322607915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10175678764392588387242213 1907939768323610322607915)
        ·
          refine ⟨2861909652485415483911873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907939768323610322607915 2861909652485415483911873)
          ·
            refine ⟨2146432239364061612933905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861909652485415483911873 2146432239364061612933905)
            ·
              refine ⟨1609824179523046209700429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146432239364061612933905 1609824179523046209700429)
              ·
                refine ⟨603684067321142328637661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1609824179523046209700429 603684067321142328637661)
                ·
                  refine ⟨226381525245428373239123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603684067321142328637661 226381525245428373239123)
                  ·
                    refine ⟨339572287868142559858685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226381525245428373239123 339572287868142559858685)
                    ·
                      refine ⟨127339607950553459947007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 339572287868142559858685 127339607950553459947007)
                      ·
                        rfl

theorem cell23_247993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_247993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_247993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_247993 prefixEnd_247993 := by exact prefixLift 247993
  have htrace : WordTrace (prefixWord ++ tailWord_247993) baseStart_247993 baseEnd_247993 := by
    simpa [prefixWord, tailWord_247993, baseEnd_247993] using wordTrace_append hprefix tailTrace_247993
  have hstable : (prefixWord ++ tailWord_247993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247993).length < 2 ^ (prefixWord ++ tailWord_247993).sum := by decide
  have hdescent : baseEnd_247993 < baseStart_247993 := by decide
  rcases family_descends (prefixWord ++ tailWord_247993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248019 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5]
def baseStart_248019 : Nat := 118140960795 + 248019 * 2 ^ 59
def prefixEnd_248019 : Nat := 4983230072969 + 3 ^ 40 * 248019 * 2
def baseEnd_248019 : Nat := 127352958447570358221887

theorem tailTrace_248019 : CollatzResearch.WordTrace tailWord_248019 prefixEnd_248019 127352958447570358221887 := by
  unfold tailWord_248019
  simp only [CollatzResearch.WordTrace]
  refine ⟨9045996088476996117995111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6030664058984664078663407 9045996088476996117995111)
  ·
    refine ⟨13568994132715494176992667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9045996088476996117995111 13568994132715494176992667)
    ·
      refine ⟨20353491199073241265489001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13568994132715494176992667 20353491199073241265489001)
      ·
        refine ⟨15265118399304930949116751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20353491199073241265489001 15265118399304930949116751)
        ·
          refine ⟨22897677598957396423675127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15265118399304930949116751 22897677598957396423675127)
          ·
            refine ⟨34346516398436094635512691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22897677598957396423675127 34346516398436094635512691)
            ·
              refine ⟨51519774597654141953269037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34346516398436094635512691 51519774597654141953269037)
              ·
                refine ⟨19319915474120303232475889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51519774597654141953269037 19319915474120303232475889)
                ·
                  refine ⟨14489936605590227424356917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19319915474120303232475889 14489936605590227424356917)
                  ·
                    refine ⟨1358431556774083821033461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14489936605590227424356917 1358431556774083821033461)
                    ·
                      refine ⟨127352958447570358221887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1358431556774083821033461 127352958447570358221887)
                      ·
                        rfl

theorem cell23_248019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_248019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248019 prefixEnd_248019 := by exact prefixLift 248019
  have htrace : WordTrace (prefixWord ++ tailWord_248019) baseStart_248019 baseEnd_248019 := by
    simpa [prefixWord, tailWord_248019, baseEnd_248019] using wordTrace_append hprefix tailTrace_248019
  have hstable : (prefixWord ++ tailWord_248019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248019).length < 2 ^ (prefixWord ++ tailWord_248019).sum := by decide
  have hdescent : baseEnd_248019 < baseStart_248019 := by decide
  rcases family_descends (prefixWord ++ tailWord_248019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248026 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_248026 : Nat := 118140960795 + 248026 * 2 ^ 59
def prefixEnd_248026 : Nat := 4983230072969 + 3 ^ 40 * 248026 * 2
def baseEnd_248026 : Nat := 42452184270717276944785

theorem tailTrace_248026 : CollatzResearch.WordTrace tailWord_248026 prefixEnd_248026 42452184270717276944785 := by
  unfold tailWord_248026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261562849862909078374983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6030834266301090875666621 2261562849862909078374983)
  ·
    refine ⟨3392344274794363617562475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261562849862909078374983 3392344274794363617562475)
    ·
      refine ⟨5088516412191545426343713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392344274794363617562475 5088516412191545426343713)
      ·
        refine ⟨3816387309143659069757785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5088516412191545426343713 3816387309143659069757785)
        ·
          refine ⟨2862290481857744302318339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816387309143659069757785 2862290481857744302318339)
          ·
            refine ⟨4293435722786616453477509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862290481857744302318339 4293435722786616453477509)
            ·
              refine ⟨805019198022490585027033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4293435722786616453477509 805019198022490585027033)
              ·
                refine ⟨603764398516867938770275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805019198022490585027033 603764398516867938770275)
                ·
                  refine ⟨905646597775301908155413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603764398516867938770275 905646597775301908155413)
                  ·
                    refine ⟨42452184270717276944785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 905646597775301908155413 42452184270717276944785)
                    ·
                      rfl

theorem cell23_248026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_248026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248026 prefixEnd_248026 := by exact prefixLift 248026
  have htrace : WordTrace (prefixWord ++ tailWord_248026) baseStart_248026 baseEnd_248026 := by
    simpa [prefixWord, tailWord_248026, baseEnd_248026] using wordTrace_append hprefix tailTrace_248026
  have hstable : (prefixWord ++ tailWord_248026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248026).length < 2 ^ (prefixWord ++ tailWord_248026).sum := by decide
  have hdescent : baseEnd_248026 < baseStart_248026 := by decide
  rcases family_descends (prefixWord ++ tailWord_248026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248033 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_248033 : Nat := 118140960795 + 248033 * 2 ^ 59
def prefixEnd_248033 : Nat := 4983230072969 + 3 ^ 40 * 248033 * 2
def baseEnd_248033 : Nat := 127360147176733303446823

theorem tailTrace_248033 : CollatzResearch.WordTrace tailWord_248033 prefixEnd_248033 127360147176733303446823 := by
  unfold tailWord_248033
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046506710426276509004753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6031004473617517672669835 9046506710426276509004753)
  ·
    refine ⟨6784880032819707381753565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9046506710426276509004753 6784880032819707381753565)
    ·
      refine ⟨2544330012307390268157587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6784880032819707381753565 2544330012307390268157587)
      ·
        refine ⟨3816495018461085402236381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544330012307390268157587 3816495018461085402236381)
        ·
          refine ⟨1431185631922907025838643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3816495018461085402236381 1431185631922907025838643)
          ·
            refine ⟨2146778447884360538757965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431185631922907025838643 2146778447884360538757965)
            ·
              refine ⟨805041917956635202034237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2146778447884360538757965 805041917956635202034237)
              ·
                refine ⟨301890719233738200762839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805041917956635202034237 301890719233738200762839)
                ·
                  refine ⟨452836078850607301144259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301890719233738200762839 452836078850607301144259)
                  ·
                    refine ⟨679254118275910951716389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452836078850607301144259 679254118275910951716389)
                    ·
                      refine ⟨127360147176733303446823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 679254118275910951716389 127360147176733303446823)
                      ·
                        rfl

theorem cell23_248033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_248033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248033 prefixEnd_248033 := by exact prefixLift 248033
  have htrace : WordTrace (prefixWord ++ tailWord_248033) baseStart_248033 baseEnd_248033 := by
    simpa [prefixWord, tailWord_248033, baseEnd_248033] using wordTrace_append hprefix tailTrace_248033
  have hstable : (prefixWord ++ tailWord_248033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248033).length < 2 ^ (prefixWord ++ tailWord_248033).sum := by decide
  have hdescent : baseEnd_248033 < baseStart_248033 := by decide
  rcases family_descends (prefixWord ++ tailWord_248033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248034 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 6]
def baseStart_248034 : Nat := 118140960795 + 248034 * 2 ^ 59
def prefixEnd_248034 : Nat := 4983230072969 + 3 ^ 40 * 248034 * 2
def baseEnd_248034 : Nat := 14151184517487533281591

theorem tailTrace_248034 : CollatzResearch.WordTrace tailWord_248034 prefixEnd_248034 14151184517487533281591 := by
  unfold tailWord_248034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261635795855663419947789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6031028788948435786527437 2261635795855663419947789)
  ·
    refine ⟨848113423445873782480421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2261635795855663419947789 848113423445873782480421)
    ·
      refine ⟨159021266896101334215079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 848113423445873782480421 159021266896101334215079)
      ·
        refine ⟨238531900344152001322619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159021266896101334215079 238531900344152001322619)
        ·
          refine ⟨357797850516228001983929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238531900344152001322619 357797850516228001983929)
          ·
            refine ⟨268348387887171001487947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357797850516228001983929 268348387887171001487947)
            ·
              refine ⟨402522581830756502231921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268348387887171001487947 402522581830756502231921)
              ·
                refine ⟨301891936373067376673941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402522581830756502231921 301891936373067376673941)
                ·
                  refine ⟨14151184517487533281591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301891936373067376673941 14151184517487533281591)
                  ·
                    rfl

theorem cell23_248034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_248034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248034 prefixEnd_248034 := by exact prefixLift 248034
  have htrace : WordTrace (prefixWord ++ tailWord_248034) baseStart_248034 baseEnd_248034 := by
    simpa [prefixWord, tailWord_248034, baseEnd_248034] using wordTrace_append hprefix tailTrace_248034
  have hstable : (prefixWord ++ tailWord_248034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248034).length < 2 ^ (prefixWord ++ tailWord_248034).sum := by decide
  have hdescent : baseEnd_248034 < baseStart_248034 := by decide
  rcases family_descends (prefixWord ++ tailWord_248034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248036 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_248036 : Nat := 118140960795 + 248036 * 2 ^ 59
def prefixEnd_248036 : Nat := 4983230072969 + 3 ^ 40 * 248036 * 2
def baseEnd_248036 : Nat := 127361687618696791709309

theorem tailTrace_248036 : CollatzResearch.WordTrace tailWord_248036 prefixEnd_248036 127361687618696791709309 := by
  unfold tailWord_248036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523308064707704010681981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6031077419610272014242641 4523308064707704010681981)
  ·
    refine ⟨1696240524265389004005743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4523308064707704010681981 1696240524265389004005743)
    ·
      refine ⟨2544360786398083506008615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696240524265389004005743 2544360786398083506008615)
      ·
        refine ⟨3816541179597125259012923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544360786398083506008615 3816541179597125259012923)
        ·
          refine ⟨5724811769395687888519385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816541179597125259012923 5724811769395687888519385)
          ·
            refine ⟨4293608827046765916389539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5724811769395687888519385 4293608827046765916389539)
            ·
              refine ⟨6440413240570148874584309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293608827046765916389539 6440413240570148874584309)
              ·
                refine ⟨603788741303451456992279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6440413240570148874584309 603788741303451456992279)
                ·
                  refine ⟨905683111955177185488419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603788741303451456992279 905683111955177185488419)
                  ·
                    refine ⟨1358524667932765778232629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 905683111955177185488419 1358524667932765778232629)
                    ·
                      refine ⟨127361687618696791709309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1358524667932765778232629 127361687618696791709309)
                      ·
                        rfl

theorem cell23_248036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_248036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248036 prefixEnd_248036 := by exact prefixLift 248036
  have htrace : WordTrace (prefixWord ++ tailWord_248036) baseStart_248036 baseEnd_248036 := by
    simpa [prefixWord, tailWord_248036, baseEnd_248036] using wordTrace_append hprefix tailTrace_248036
  have hstable : (prefixWord ++ tailWord_248036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248036).length < 2 ^ (prefixWord ++ tailWord_248036).sum := by decide
  have hdescent : baseEnd_248036 < baseStart_248036 := by decide
  rcases family_descends (prefixWord ++ tailWord_248036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248046 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_248046 : Nat := 118140960795 + 248046 * 2 ^ 59
def prefixEnd_248046 : Nat := 4983230072969 + 3 ^ 40 * 248046 * 2
def baseEnd_248046 : Nat := 127366822425241752584263

theorem tailTrace_248046 : CollatzResearch.WordTrace tailWord_248046 prefixEnd_248046 127366822425241752584263 := by
  unfold tailWord_248046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130872607422397466153499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6031320572919453152818661 1130872607422397466153499)
  ·
    refine ⟨1696308911133596199230249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1130872607422397466153499 1696308911133596199230249)
    ·
      refine ⟨1272231683350197149422687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1696308911133596199230249 1272231683350197149422687)
      ·
        refine ⟨1908347525025295724134031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272231683350197149422687 1908347525025295724134031)
        ·
          refine ⟨2862521287537943586201047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908347525025295724134031 2862521287537943586201047)
          ·
            refine ⟨4293781931306915379301571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862521287537943586201047 4293781931306915379301571)
            ·
              refine ⟨6440672896960373068952357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293781931306915379301571 6440672896960373068952357)
              ·
                refine ⟨1207626168180069950428567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6440672896960373068952357 1207626168180069950428567)
                ·
                  refine ⟨1811439252270104925642851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207626168180069950428567 1811439252270104925642851)
                  ·
                    refine ⟨2717158878405157388464277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1811439252270104925642851 2717158878405157388464277)
                    ·
                      refine ⟨127366822425241752584263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2717158878405157388464277 127366822425241752584263)
                      ·
                        rfl

theorem cell23_248046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_248046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248046 prefixEnd_248046 := by exact prefixLift 248046
  have htrace : WordTrace (prefixWord ++ tailWord_248046) baseStart_248046 baseEnd_248046 := by
    simpa [prefixWord, tailWord_248046, baseEnd_248046] using wordTrace_append hprefix tailTrace_248046
  have hstable : (prefixWord ++ tailWord_248046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248046).length < 2 ^ (prefixWord ++ tailWord_248046).sum := by decide
  have hdescent : baseEnd_248046 < baseStart_248046 := by decide
  rcases family_descends (prefixWord ++ tailWord_248046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248073 : List Nat := [1, 2, 1, 1, 3, 6, 2, 7]
def baseStart_248073 : Nat := 118140960795 + 248073 * 2 ^ 59
def prefixEnd_248073 : Nat := 4983230072969 + 3 ^ 40 * 248073 * 2
def baseEnd_248073 : Nat := 4717803200107894331357

theorem tailTrace_248073 : CollatzResearch.WordTrace tailWord_248073 prefixEnd_248073 4717803200107894331357 := by
  unfold tailWord_248073
  simp only [CollatzResearch.WordTrace]
  refine ⟨9047965630281363340460873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6031977086854242226973915 9047965630281363340460873)
  ·
    refine ⟨6785974222711022505345655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9047965630281363340460873 6785974222711022505345655)
    ·
      refine ⟨10178961334066533758018483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6785974222711022505345655 10178961334066533758018483)
      ·
        refine ⟨15268442001099800637027725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10178961334066533758018483 15268442001099800637027725)
        ·
          refine ⟨5725665750412425238885397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15268442001099800637027725 5725665750412425238885397)
          ·
            refine ⟨268390582050582433072753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5725665750412425238885397 268390582050582433072753)
            ·
              refine ⟨201292936537936824804565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268390582050582433072753 201292936537936824804565)
              ·
                refine ⟨4717803200107894331357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201292936537936824804565 4717803200107894331357)
                ·
                  rfl

theorem cell23_248073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 7].length) (baseStart_248073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248073 prefixEnd_248073 := by exact prefixLift 248073
  have htrace : WordTrace (prefixWord ++ tailWord_248073) baseStart_248073 baseEnd_248073 := by
    simpa [prefixWord, tailWord_248073, baseEnd_248073] using wordTrace_append hprefix tailTrace_248073
  have hstable : (prefixWord ++ tailWord_248073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248073).length < 2 ^ (prefixWord ++ tailWord_248073).sum := by decide
  have hdescent : baseEnd_248073 < baseStart_248073 := by decide
  rcases family_descends (prefixWord ++ tailWord_248073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248100 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_248100 : Nat := 118140960795 + 248100 * 2 ^ 59
def prefixEnd_248100 : Nat := 4983230072969 + 3 ^ 40 * 248100 * 2
def baseEnd_248100 : Nat := 127394550380584541309015

theorem tailTrace_248100 : CollatzResearch.WordTrace tailWord_248100 prefixEnd_248100 127394550380584541309015 := by
  unfold tailWord_248100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524475200591773475846877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6032633600789031301129169 4524475200591773475846877)
  ·
    refine ⟨1696678200221915053442579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4524475200591773475846877 1696678200221915053442579)
    ·
      refine ⟨2545017300332872580163869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696678200221915053442579 2545017300332872580163869)
      ·
        refine ⟨954381487624827217561451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2545017300332872580163869 954381487624827217561451)
        ·
          refine ⟨1431572231437240826342177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954381487624827217561451 1431572231437240826342177)
          ·
            refine ⟨1073679173577930619756633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431572231437240826342177 1073679173577930619756633)
            ·
              refine ⟨805259380183447964817475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073679173577930619756633 805259380183447964817475)
              ·
                refine ⟨1207889070275171947226213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805259380183447964817475 1207889070275171947226213)
                ·
                  refine ⟨226479200676594740104915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207889070275171947226213 226479200676594740104915)
                  ·
                    refine ⟨339718801014892110157373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226479200676594740104915 339718801014892110157373)
                    ·
                      refine ⟨127394550380584541309015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 339718801014892110157373 127394550380584541309015)
                      ·
                        rfl

theorem cell23_248100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_248100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248100 prefixEnd_248100 := by exact prefixLift 248100
  have htrace : WordTrace (prefixWord ++ tailWord_248100) baseStart_248100 baseEnd_248100 := by
    simpa [prefixWord, tailWord_248100, baseEnd_248100] using wordTrace_append hprefix tailTrace_248100
  have hstable : (prefixWord ++ tailWord_248100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248100).length < 2 ^ (prefixWord ++ tailWord_248100).sum := by decide
  have hdescent : baseEnd_248100 < baseStart_248100 := by decide
  rcases family_descends (prefixWord ++ tailWord_248100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248101 : List Nat := [1, 3, 1, 2, 5, 1, 3, 2, 1, 2, 2]
def baseStart_248101 : Nat := 118140960795 + 248101 * 2 ^ 59
def prefixEnd_248101 : Nat := 4983230072969 + 3 ^ 40 * 248101 * 2
def baseEnd_248101 : Nat := 127395063861239037396511

theorem tailTrace_248101 : CollatzResearch.WordTrace tailWord_248101 prefixEnd_248101 127395063861239037396511 := by
  unfold tailWord_248101
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048986874179924122480157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6032657916119949414986771 9048986874179924122480157)
  ·
    refine ⟨3393370077817471545930059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9048986874179924122480157 3393370077817471545930059)
    ·
      refine ⟨5090055116726207318895089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393370077817471545930059 5090055116726207318895089)
      ·
        refine ⟨3817541337544655489171317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5090055116726207318895089 3817541337544655489171317)
        ·
          refine ⟨357894500394811452109811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3817541337544655489171317 357894500394811452109811)
          ·
            refine ⟨536841750592217178164717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357894500394811452109811 536841750592217178164717)
            ·
              refine ⟨201315656472081441811769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536841750592217178164717 201315656472081441811769)
              ·
                refine ⟨150986742354061081358827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201315656472081441811769 150986742354061081358827)
                ·
                  refine ⟨226480113531091622038241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150986742354061081358827 226480113531091622038241)
                  ·
                    refine ⟨169860085148318716528681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226480113531091622038241 169860085148318716528681)
                    ·
                      refine ⟨127395063861239037396511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 169860085148318716528681 127395063861239037396511)
                      ·
                        rfl

theorem cell23_248101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_248101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248101 prefixEnd_248101 := by exact prefixLift 248101
  have htrace : WordTrace (prefixWord ++ tailWord_248101) baseStart_248101 baseEnd_248101 := by
    simpa [prefixWord, tailWord_248101, baseEnd_248101] using wordTrace_append hprefix tailTrace_248101
  have hstable : (prefixWord ++ tailWord_248101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248101).length < 2 ^ (prefixWord ++ tailWord_248101).sum := by decide
  have hdescent : baseEnd_248101 < baseStart_248101 := by decide
  rcases family_descends (prefixWord ++ tailWord_248101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248140 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 1, 4, 2]
def baseStart_248140 : Nat := 118140960795 + 248140 * 2 ^ 59
def prefixEnd_248140 : Nat := 4983230072969 + 3 ^ 40 * 248140 * 2
def baseEnd_248140 : Nat := 127415089606764384808831

theorem tailTrace_248140 : CollatzResearch.WordTrace tailWord_248140 prefixEnd_248140 127415089606764384808831 := by
  unfold tailWord_248140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4525204660519316891574937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6033606214025755855433249 4525204660519316891574937)
  ·
    refine ⟨3393903495389487668681203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4525204660519316891574937 3393903495389487668681203)
    ·
      refine ⟨5090855243084231503021805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393903495389487668681203 5090855243084231503021805)
      ·
        refine ⟨1909070716156586813633177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5090855243084231503021805 1909070716156586813633177)
        ·
          refine ⟨1431803037117440110224883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1909070716156586813633177 1431803037117440110224883)
          ·
            refine ⟨2147704555676160165337325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431803037117440110224883 2147704555676160165337325)
            ·
              refine ⟨805389208378560062001497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2147704555676160165337325 805389208378560062001497)
              ·
                refine ⟨604041906283920046501123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805389208378560062001497 604041906283920046501123)
                ·
                  refine ⟨906062859425880069751685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604041906283920046501123 906062859425880069751685)
                  ·
                    refine ⟨169886786142352513078441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 906062859425880069751685 169886786142352513078441)
                    ·
                      refine ⟨127415089606764384808831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 169886786142352513078441 127415089606764384808831)
                      ·
                        rfl

theorem cell23_248140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_248140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248140 prefixEnd_248140 := by exact prefixLift 248140
  have htrace : WordTrace (prefixWord ++ tailWord_248140) baseStart_248140 baseEnd_248140 := by
    simpa [prefixWord, tailWord_248140, baseEnd_248140] using wordTrace_append hprefix tailTrace_248140
  have hstable : (prefixWord ++ tailWord_248140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248140).length < 2 ^ (prefixWord ++ tailWord_248140).sum := by decide
  have hdescent : baseEnd_248140 < baseStart_248140 := by decide
  rcases family_descends (prefixWord ++ tailWord_248140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248170 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_248170 : Nat := 118140960795 + 248170 * 2 ^ 59
def prefixEnd_248170 : Nat := 4983230072969 + 3 ^ 40 * 248170 * 2
def baseEnd_248170 : Nat := 127430494026399267433693

theorem tailTrace_248170 : CollatzResearch.WordTrace tailWord_248170 prefixEnd_248170 127430494026399267433693 := by
  unfold tailWord_248170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262875877732487226685491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6034335673953299271161309 2262875877732487226685491)
  ·
    refine ⟨3394313816598730840028237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2262875877732487226685491 3394313816598730840028237)
    ·
      refine ⟨1272867681224524065010589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3394313816598730840028237 1272867681224524065010589)
      ·
        refine ⟨477325380459196524378971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1272867681224524065010589 477325380459196524378971)
        ·
          refine ⟨715988070688794786568457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477325380459196524378971 715988070688794786568457)
          ·
            refine ⟨536991053016596089926343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715988070688794786568457 536991053016596089926343)
            ·
              refine ⟨805486579524894134889515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536991053016596089926343 805486579524894134889515)
              ·
                refine ⟨1208229869287341202334273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805486579524894134889515 1208229869287341202334273)
                ·
                  refine ⟨906172401965505901750705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208229869287341202334273 906172401965505901750705)
                  ·
                    refine ⟨679629301474129426313029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 906172401965505901750705 679629301474129426313029)
                    ·
                      refine ⟨127430494026399267433693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 679629301474129426313029 127430494026399267433693)
                      ·
                        rfl

theorem cell23_248170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_248170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248170 prefixEnd_248170 := by exact prefixLift 248170
  have htrace : WordTrace (prefixWord ++ tailWord_248170) baseStart_248170 baseEnd_248170 := by
    simpa [prefixWord, tailWord_248170, baseEnd_248170] using wordTrace_append hprefix tailTrace_248170
  have hstable : (prefixWord ++ tailWord_248170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248170).length < 2 ^ (prefixWord ++ tailWord_248170).sum := by decide
  have hdescent : baseEnd_248170 < baseStart_248170 := by decide
  rcases family_descends (prefixWord ++ tailWord_248170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248213 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_248213 : Nat := 118140960795 + 248213 * 2 ^ 59
def prefixEnd_248213 : Nat := 4983230072969 + 3 ^ 40 * 248213 * 2
def baseEnd_248213 : Nat := 127452573694542599195995

theorem tailTrace_248213 : CollatzResearch.WordTrace tailWord_248213 prefixEnd_248213 127452573694542599195995 := by
  unfold tailWord_248213
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053071849774167250557293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6035381233182778167038195 9053071849774167250557293)
  ·
    refine ⟨3394901943665312718958985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9053071849774167250557293 3394901943665312718958985)
    ·
      refine ⟨2546176457748984539219239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3394901943665312718958985 2546176457748984539219239)
      ·
        refine ⟨3819264686623476808828859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546176457748984539219239 3819264686623476808828859)
        ·
          refine ⟨5728897029935215213243289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819264686623476808828859 5728897029935215213243289)
          ·
            refine ⟨4296672772451411409932467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5728897029935215213243289 4296672772451411409932467)
            ·
              refine ⟨6445009158677117114898701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296672772451411409932467 6445009158677117114898701)
              ·
                refine ⟨2416878434503918918087013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6445009158677117114898701 2416878434503918918087013)
                ·
                  refine ⟨453164706469484797141315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416878434503918918087013 453164706469484797141315)
                  ·
                    refine ⟨679747059704227195711973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 453164706469484797141315 679747059704227195711973)
                    ·
                      refine ⟨127452573694542599195995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 679747059704227195711973 127452573694542599195995)
                      ·
                        rfl

theorem cell23_248213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_248213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248213 prefixEnd_248213 := by exact prefixLift 248213
  have htrace : WordTrace (prefixWord ++ tailWord_248213) baseStart_248213 baseEnd_248213 := by
    simpa [prefixWord, tailWord_248213, baseEnd_248213] using wordTrace_append hprefix tailTrace_248213
  have hstable : (prefixWord ++ tailWord_248213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248213).length < 2 ^ (prefixWord ++ tailWord_248213).sum := by decide
  have hdescent : baseEnd_248213 < baseStart_248213 := by decide
  rcases family_descends (prefixWord ++ tailWord_248213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248253 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 8]
def baseStart_248253 : Nat := 118140960795 + 248253 * 2 ^ 59
def prefixEnd_248253 : Nat := 4983230072969 + 3 ^ 40 * 248253 * 2
def baseEnd_248253 : Nat := 14163679213413604743979

theorem tailTrace_248253 : CollatzResearch.WordTrace tailWord_248253 prefixEnd_248253 14163679213413604743979 := by
  unfold tailWord_248253
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054530769629254082013413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6036353846419502721342275 9054530769629254082013413)
  ·
    refine ⟨1697724519305485140377515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9054530769629254082013413 1697724519305485140377515)
    ·
      refine ⟨2546586778958227710566273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1697724519305485140377515 2546586778958227710566273)
      ·
        refine ⟨1909940084218670782924705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2546586778958227710566273 1909940084218670782924705)
        ·
          refine ⟨1432455063164003087193529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1909940084218670782924705 1432455063164003087193529)
          ·
            refine ⟨1074341297373002315395147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432455063164003087193529 1074341297373002315395147)
            ·
              refine ⟨1611511946059503473092721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074341297373002315395147 1611511946059503473092721)
              ·
                refine ⟨1208633959544627604819541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611511946059503473092721 1208633959544627604819541)
                ·
                  refine ⟨14163679213413604743979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1208633959544627604819541 14163679213413604743979)
                  ·
                    rfl

theorem cell23_248253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_248253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248253 prefixEnd_248253 := by exact prefixLift 248253
  have htrace : WordTrace (prefixWord ++ tailWord_248253) baseStart_248253 baseEnd_248253 := by
    simpa [prefixWord, tailWord_248253, baseEnd_248253] using wordTrace_append hprefix tailTrace_248253
  have hstable : (prefixWord ++ tailWord_248253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248253).length < 2 ^ (prefixWord ++ tailWord_248253).sum := by decide
  have hdescent : baseEnd_248253 < baseStart_248253 := by decide
  rcases family_descends (prefixWord ++ tailWord_248253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248287 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 6]
def baseStart_248287 : Nat := 118140960795 + 248287 * 2 ^ 59
def prefixEnd_248287 : Nat := 4983230072969 + 3 ^ 40 * 248287 * 2
def baseEnd_248287 : Nat := 14165619029219478852295

theorem tailTrace_248287 : CollatzResearch.WordTrace tailWord_248287 prefixEnd_248287 14165619029219478852295 := by
  unfold tailWord_248287
  simp only [CollatzResearch.WordTrace]
  refine ⟨9055770851506077888751115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6037180567670718592500743 9055770851506077888751115)
  ·
    refine ⟨13583656277259116833126673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9055770851506077888751115 13583656277259116833126673)
    ·
      refine ⟨10187742207944337624845005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13583656277259116833126673 10187742207944337624845005)
      ·
        refine ⟨3820403327979126609316877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10187742207944337624845005 3820403327979126609316877)
        ·
          refine ⟨1432651247992172478493829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3820403327979126609316877 1432651247992172478493829)
          ·
            refine ⟨268622108998532339717593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1432651247992172478493829 268622108998532339717593)
            ·
              refine ⟨201466581748899254788195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268622108998532339717593 201466581748899254788195)
              ·
                refine ⟨302199872623348882182293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201466581748899254788195 302199872623348882182293)
                ·
                  refine ⟨14165619029219478852295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302199872623348882182293 14165619029219478852295)
                  ·
                    rfl

theorem cell23_248287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 6].length) (baseStart_248287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248287 prefixEnd_248287 := by exact prefixLift 248287
  have htrace : WordTrace (prefixWord ++ tailWord_248287) baseStart_248287 baseEnd_248287 := by
    simpa [prefixWord, tailWord_248287, baseEnd_248287] using wordTrace_append hprefix tailTrace_248287
  have hstable : (prefixWord ++ tailWord_248287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248287).length < 2 ^ (prefixWord ++ tailWord_248287).sum := by decide
  have hdescent : baseEnd_248287 < baseStart_248287 := by decide
  rcases family_descends (prefixWord ++ tailWord_248287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248307 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 2, 3, 2]
def baseStart_248307 : Nat := 118140960795 + 248307 * 2 ^ 59
def prefixEnd_248307 : Nat := 4983230072969 + 3 ^ 40 * 248307 * 2
def baseEnd_248307 : Nat := 127500840876065231420563

theorem tailTrace_248307 : CollatzResearch.WordTrace tailWord_248307 prefixEnd_248307 127500840876065231420563 := by
  unfold tailWord_248307
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056500311433621304479175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6037666874289080869652783 9056500311433621304479175)
  ·
    refine ⟨13584750467150431956718763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9056500311433621304479175 13584750467150431956718763)
    ·
      refine ⟨20377125700725647935078145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13584750467150431956718763 20377125700725647935078145)
      ·
        refine ⟨15282844275544235951308609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20377125700725647935078145 15282844275544235951308609)
        ·
          refine ⟨11462133206658176963481457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15282844275544235951308609 11462133206658176963481457)
          ·
            refine ⟨8596599904993632722611093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11462133206658176963481457 8596599904993632722611093)
            ·
              refine ⟨402965620546576533872395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8596599904993632722611093 402965620546576533872395)
              ·
                refine ⟨604448430819864800808593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402965620546576533872395 604448430819864800808593)
                ·
                  refine ⟨453336323114898600606445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604448430819864800808593 453336323114898600606445)
                  ·
                    refine ⟨170001121168086975227417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453336323114898600606445 170001121168086975227417)
                    ·
                      refine ⟨127500840876065231420563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170001121168086975227417 127500840876065231420563)
                      ·
                        rfl

theorem cell23_248307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3, 2].length) (baseStart_248307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248307 prefixEnd_248307 := by exact prefixLift 248307
  have htrace : WordTrace (prefixWord ++ tailWord_248307) baseStart_248307 baseEnd_248307 := by
    simpa [prefixWord, tailWord_248307, baseEnd_248307] using wordTrace_append hprefix tailTrace_248307
  have hstable : (prefixWord ++ tailWord_248307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248307).length < 2 ^ (prefixWord ++ tailWord_248307).sum := by decide
  have hdescent : baseEnd_248307 < baseStart_248307 := by decide
  rcases family_descends (prefixWord ++ tailWord_248307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248313 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 3, 6]
def baseStart_248313 : Nat := 118140960795 + 248313 * 2 ^ 59
def prefixEnd_248313 : Nat := 4983230072969 + 3 ^ 40 * 248313 * 2
def baseEnd_248313 : Nat := 42501307253330735981845

theorem tailTrace_248313 : CollatzResearch.WordTrace tailWord_248313 prefixEnd_248313 42501307253330735981845 := by
  unfold tailWord_248313
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056719149411884329197593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6037812766274589552798395 9056719149411884329197593)
  ·
    refine ⟨6792539362058913246898195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9056719149411884329197593 6792539362058913246898195)
    ·
      refine ⟨10188809043088369870347293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6792539362058913246898195 10188809043088369870347293)
      ·
        refine ⟨3820803391158138701380235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10188809043088369870347293 3820803391158138701380235)
        ·
          refine ⟨5731205086737208052070353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820803391158138701380235 5731205086737208052070353)
          ·
            refine ⟨4298403815052906039052765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5731205086737208052070353 4298403815052906039052765)
            ·
              refine ⟨1611901430644839764644787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4298403815052906039052765 1611901430644839764644787)
              ·
                refine ⟨2417852145967259646967181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611901430644839764644787 2417852145967259646967181)
                ·
                  refine ⟨906694554737722367612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2417852145967259646967181 906694554737722367612693)
                  ·
                    refine ⟨42501307253330735981845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 906694554737722367612693 42501307253330735981845)
                    ·
                      rfl

theorem cell23_248313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_248313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248313 prefixEnd_248313 := by exact prefixLift 248313
  have htrace : WordTrace (prefixWord ++ tailWord_248313) baseStart_248313 baseEnd_248313 := by
    simpa [prefixWord, tailWord_248313, baseEnd_248313] using wordTrace_append hprefix tailTrace_248313
  have hstable : (prefixWord ++ tailWord_248313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248313).length < 2 ^ (prefixWord ++ tailWord_248313).sum := by decide
  have hdescent : baseEnd_248313 < baseStart_248313 := by decide
  rcases family_descends (prefixWord ++ tailWord_248313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248317 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_248317 : Nat := 118140960795 + 248317 * 2 ^ 59
def prefixEnd_248317 : Nat := 4983230072969 + 3 ^ 40 * 248317 * 2
def baseEnd_248317 : Nat := 42501991894203397431839

theorem tailTrace_248317 : CollatzResearch.WordTrace tailWord_248317 prefixEnd_248317 42501991894203397431839 := by
  unfold tailWord_248317
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056865041397393012343205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6037910027598262008228803 9056865041397393012343205)
  ·
    refine ⟨1698162195262011189814351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9056865041397393012343205 1698162195262011189814351)
    ·
      refine ⟨2547243292893016784721527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698162195262011189814351 2547243292893016784721527)
      ·
        refine ⟨3820864939339525177082291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547243292893016784721527 3820864939339525177082291)
        ·
          refine ⟨5731297409009287765623437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820864939339525177082291 5731297409009287765623437)
          ·
            refine ⟨2149236528378482912108789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5731297409009287765623437 2149236528378482912108789)
            ·
              refine ⟨201490924535482773010199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2149236528378482912108789 201490924535482773010199)
              ·
                refine ⟨302236386803224159515299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201490924535482773010199 302236386803224159515299)
                ·
                  refine ⟨453354580204836239272949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302236386803224159515299 453354580204836239272949)
                  ·
                    refine ⟨42501991894203397431839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 453354580204836239272949 42501991894203397431839)
                    ·
                      rfl

theorem cell23_248317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_248317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248317 prefixEnd_248317 := by exact prefixLift 248317
  have htrace : WordTrace (prefixWord ++ tailWord_248317) baseStart_248317 baseEnd_248317 := by
    simpa [prefixWord, tailWord_248317, baseEnd_248317] using wordTrace_append hprefix tailTrace_248317
  have hstable : (prefixWord ++ tailWord_248317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248317).length < 2 ^ (prefixWord ++ tailWord_248317).sum := by decide
  have hdescent : baseEnd_248317 < baseStart_248317 := by decide
  rcases family_descends (prefixWord ++ tailWord_248317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248324 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_248324 : Nat := 118140960795 + 248324 * 2 ^ 59
def prefixEnd_248324 : Nat := 4983230072969 + 3 ^ 40 * 248324 * 2
def baseEnd_248324 : Nat := 127509570047191664907985

theorem tailTrace_248324 : CollatzResearch.WordTrace tailWord_248324 prefixEnd_248324 127509570047191664907985 := by
  unfold tailWord_248324
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528560176186016603924013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6038080234914688805232017 4528560176186016603924013)
  ·
    refine ⟨1698210066069756226471505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4528560176186016603924013 1698210066069756226471505)
    ·
      refine ⟨1273657549552317169853629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1698210066069756226471505 1273657549552317169853629)
      ·
        refine ⟨477621581082118938695111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1273657549552317169853629 477621581082118938695111)
        ·
          refine ⟨716432371623178408042667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477621581082118938695111 716432371623178408042667)
          ·
            refine ⟨1074648557434767612064001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716432371623178408042667 1074648557434767612064001)
            ·
              refine ⟨805986418076075709048001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074648557434767612064001 805986418076075709048001)
              ·
                refine ⟨604489813557056781786001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805986418076075709048001 604489813557056781786001)
                ·
                  refine ⟨453367360167792586339501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604489813557056781786001 453367360167792586339501)
                  ·
                    refine ⟨170012760062922219877313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453367360167792586339501 170012760062922219877313)
                    ·
                      refine ⟨127509570047191664907985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170012760062922219877313 127509570047191664907985)
                      ·
                        rfl

theorem cell23_248324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_248324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248324 prefixEnd_248324 := by exact prefixLift 248324
  have htrace : WordTrace (prefixWord ++ tailWord_248324) baseStart_248324 baseEnd_248324 := by
    simpa [prefixWord, tailWord_248324, baseEnd_248324] using wordTrace_append hprefix tailTrace_248324
  have hstable : (prefixWord ++ tailWord_248324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248324).length < 2 ^ (prefixWord ++ tailWord_248324).sum := by decide
  have hdescent : baseEnd_248324 < baseStart_248324 := by decide
  rcases family_descends (prefixWord ++ tailWord_248324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248331 : List Nat := [1, 1, 1, 1, 7, 1, 4, 2, 1, 1, 3]
def baseStart_248331 : Nat := 118140960795 + 248331 * 2 ^ 59
def prefixEnd_248331 : Nat := 4983230072969 + 3 ^ 40 * 248331 * 2
def baseEnd_248331 : Nat := 127513164411773137520453

theorem tailTrace_248331 : CollatzResearch.WordTrace tailWord_248331 prefixEnd_248331 127513164411773137520453 := by
  unfold tailWord_248331
  simp only [CollatzResearch.WordTrace]
  refine ⟨9057375663346673403352847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6038250442231115602235231 9057375663346673403352847)
  ·
    refine ⟨13586063495020010105029271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9057375663346673403352847 13586063495020010105029271)
    ·
      refine ⟨20379095242530015157543907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13586063495020010105029271 20379095242530015157543907)
      ·
        refine ⟨30568642863795022736315861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20379095242530015157543907 30568642863795022736315861)
        ·
          refine ⟨716452567120195845382403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30568642863795022736315861 716452567120195845382403)
          ·
            refine ⟨1074678850680293768073605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716452567120195845382403 1074678850680293768073605)
            ·
              refine ⟨201502284502555081513801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1074678850680293768073605 201502284502555081513801)
              ·
                refine ⟨151126713376916311135351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201502284502555081513801 151126713376916311135351)
                ·
                  refine ⟨226690070065374466703027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151126713376916311135351 226690070065374466703027)
                  ·
                    refine ⟨340035105098061700054541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226690070065374466703027 340035105098061700054541)
                    ·
                      refine ⟨127513164411773137520453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 340035105098061700054541 127513164411773137520453)
                      ·
                        rfl

theorem cell23_248331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 1, 3].length) (baseStart_248331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248331 prefixEnd_248331 := by exact prefixLift 248331
  have htrace : WordTrace (prefixWord ++ tailWord_248331) baseStart_248331 baseEnd_248331 := by
    simpa [prefixWord, tailWord_248331, baseEnd_248331] using wordTrace_append hprefix tailTrace_248331
  have hstable : (prefixWord ++ tailWord_248331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248331).length < 2 ^ (prefixWord ++ tailWord_248331).sum := by decide
  have hdescent : baseEnd_248331 < baseStart_248331 := by decide
  rcases family_descends (prefixWord ++ tailWord_248331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248371 : List Nat := [1, 1, 1, 2, 4, 2, 4, 3, 1, 2, 2]
def baseStart_248371 : Nat := 118140960795 + 248371 * 2 ^ 59
def prefixEnd_248371 : Nat := 4983230072969 + 3 ^ 40 * 248371 * 2
def baseEnd_248371 : Nat := 127533703637952981020269

theorem tailTrace_248371 : CollatzResearch.WordTrace tailWord_248371 prefixEnd_248371 127533703637952981020269 := by
  unfold tailWord_248371
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058834583201760234808967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6039223055467840156539311 9058834583201760234808967)
  ·
    refine ⟨13588251874802640352213451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9058834583201760234808967 13588251874802640352213451)
    ·
      refine ⟨20382377812203960528320177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13588251874802640352213451 20382377812203960528320177)
      ·
        refine ⟨15286783359152970396240133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20382377812203960528320177 15286783359152970396240133)
        ·
          refine ⟨2866271879841181949295025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15286783359152970396240133 2866271879841181949295025)
          ·
            refine ⟨2149703909880886461971269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866271879841181949295025 2149703909880886461971269)
            ·
              refine ⟨403069483102666211619613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2149703909880886461971269 403069483102666211619613)
              ·
                refine ⟨151151056163499829357355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403069483102666211619613 151151056163499829357355)
                ·
                  refine ⟨226726584245249744036033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151151056163499829357355 226726584245249744036033)
                  ·
                    refine ⟨170044938183937308027025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226726584245249744036033 170044938183937308027025)
                    ·
                      refine ⟨127533703637952981020269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170044938183937308027025 127533703637952981020269)
                      ·
                        rfl

theorem cell23_248371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 2, 2].length) (baseStart_248371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248371 prefixEnd_248371 := by exact prefixLift 248371
  have htrace : WordTrace (prefixWord ++ tailWord_248371) baseStart_248371 baseEnd_248371 := by
    simpa [prefixWord, tailWord_248371, baseEnd_248371] using wordTrace_append hprefix tailTrace_248371
  have hstable : (prefixWord ++ tailWord_248371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248371).length < 2 ^ (prefixWord ++ tailWord_248371).sum := by decide
  have hdescent : baseEnd_248371 < baseStart_248371 := by decide
  rcases family_descends (prefixWord ++ tailWord_248371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248404 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_248404 : Nat := 118140960795 + 248404 * 2 ^ 59
def prefixEnd_248404 : Nat := 4983230072969 + 3 ^ 40 * 248404 * 2
def baseEnd_248404 : Nat := 127550648499551351907617

theorem tailTrace_248404 : CollatzResearch.WordTrace tailWord_248404 prefixEnd_248404 127550648499551351907617 := by
  unfold tailWord_248404
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530019096041103435380133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6040025461388137913840177 4530019096041103435380133)
  ·
    refine ⟨849378580507706894133775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4530019096041103435380133 849378580507706894133775)
    ·
      refine ⟨1274067870761560341200663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849378580507706894133775 1274067870761560341200663)
      ·
        refine ⟨1911101806142340511800995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274067870761560341200663 1911101806142340511800995)
        ·
          refine ⟨2866652709213510767701493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911101806142340511800995 2866652709213510767701493)
          ·
            refine ⟨268748691488766634472015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2866652709213510767701493 268748691488766634472015)
            ·
              refine ⟨403123037233149951708023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268748691488766634472015 403123037233149951708023)
              ·
                refine ⟨604684555849724927562035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403123037233149951708023 604684555849724927562035)
                ·
                  refine ⟨907026833774587391343053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604684555849724927562035 907026833774587391343053)
                  ·
                    refine ⟨340135062665470271753645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 907026833774587391343053 340135062665470271753645)
                    ·
                      refine ⟨127550648499551351907617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 340135062665470271753645 127550648499551351907617)
                      ·
                        rfl

theorem cell23_248404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_248404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248404 prefixEnd_248404 := by exact prefixLift 248404
  have htrace : WordTrace (prefixWord ++ tailWord_248404) baseStart_248404 baseEnd_248404 := by
    simpa [prefixWord, tailWord_248404, baseEnd_248404] using wordTrace_append hprefix tailTrace_248404
  have hstable : (prefixWord ++ tailWord_248404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248404).length < 2 ^ (prefixWord ++ tailWord_248404).sum := by decide
  have hdescent : baseEnd_248404 < baseStart_248404 := by decide
  rcases family_descends (prefixWord ++ tailWord_248404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248444 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_248444 : Nat := 118140960795 + 248444 * 2 ^ 59
def prefixEnd_248444 : Nat := 4983230072969 + 3 ^ 40 * 248444 * 2
def baseEnd_248444 : Nat := 127571187725731195407433

theorem tailTrace_248444 : CollatzResearch.WordTrace tailWord_248444 prefixEnd_248444 127571187725731195407433 := by
  unfold tailWord_248444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530748555968646851108193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6040998074624862468144257 4530748555968646851108193)
  ·
    refine ⟨3398061416976485138331145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4530748555968646851108193 3398061416976485138331145)
    ·
      refine ⟨2548546062732363853748359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3398061416976485138331145 2548546062732363853748359)
      ·
        refine ⟨3822819094098545780622539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548546062732363853748359 3822819094098545780622539)
        ·
          refine ⟨5734228641147818670933809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3822819094098545780622539 5734228641147818670933809)
          ·
            refine ⟨4300671480860864003200357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5734228641147818670933809 4300671480860864003200357)
            ·
              refine ⟨806375902661412000600067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4300671480860864003200357 806375902661412000600067)
              ·
                refine ⟨1209563853992118000900101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806375902661412000600067 1209563853992118000900101)
                ·
                  refine ⟨226793222623522125168769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209563853992118000900101 226793222623522125168769)
                  ·
                    refine ⟨170094916967641593876577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226793222623522125168769 170094916967641593876577)
                    ·
                      refine ⟨127571187725731195407433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170094916967641593876577 127571187725731195407433)
                      ·
                        rfl

theorem cell23_248444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_248444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248444 prefixEnd_248444 := by exact prefixLift 248444
  have htrace : WordTrace (prefixWord ++ tailWord_248444) baseStart_248444 baseEnd_248444 := by
    simpa [prefixWord, tailWord_248444, baseEnd_248444] using wordTrace_append hprefix tailTrace_248444
  have hstable : (prefixWord ++ tailWord_248444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248444).length < 2 ^ (prefixWord ++ tailWord_248444).sum := by decide
  have hdescent : baseEnd_248444 < baseStart_248444 := by decide
  rcases family_descends (prefixWord ++ tailWord_248444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248501 : List Nat := [1, 3, 3, 3, 1, 1, 4, 2, 5]
def baseStart_248501 : Nat := 118140960795 + 248501 * 2 ^ 59
def prefixEnd_248501 : Nat := 4983230072969 + 3 ^ 40 * 248501 * 2
def baseEnd_248501 : Nat := 14177828458115274710519

theorem tailTrace_248501 : CollatzResearch.WordTrace tailWord_248501 prefixEnd_248501 14177828458115274710519 := by
  unfold tailWord_248501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063576072730792437041357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6042384048487194958027571 9063576072730792437041357)
  ·
    refine ⟨3398841027274047163890509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9063576072730792437041357 3398841027274047163890509)
    ·
      refine ⟨1274565385227767686458941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3398841027274047163890509 1274565385227767686458941)
      ·
        refine ⟨477962019460412882422103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1274565385227767686458941 477962019460412882422103)
        ·
          refine ⟨716943029190619323633155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477962019460412882422103 716943029190619323633155)
          ·
            refine ⟨1075414543785928985449733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716943029190619323633155 1075414543785928985449733)
            ·
              refine ⟨201640226959861684771825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1075414543785928985449733 201640226959861684771825)
              ·
                refine ⟨151230170219896263578869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201640226959861684771825 151230170219896263578869)
                ·
                  refine ⟨14177828458115274710519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151230170219896263578869 14177828458115274710519)
                  ·
                    rfl

theorem cell23_248501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_248501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248501 prefixEnd_248501 := by exact prefixLift 248501
  have htrace : WordTrace (prefixWord ++ tailWord_248501) baseStart_248501 baseEnd_248501 := by
    simpa [prefixWord, tailWord_248501, baseEnd_248501] using wordTrace_append hprefix tailTrace_248501
  have hstable : (prefixWord ++ tailWord_248501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248501).length < 2 ^ (prefixWord ++ tailWord_248501).sum := by decide
  have hdescent : baseEnd_248501 < baseStart_248501 := by decide
  rcases family_descends (prefixWord ++ tailWord_248501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248537 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 3]
def baseStart_248537 : Nat := 118140960795 + 248537 * 2 ^ 59
def prefixEnd_248537 : Nat := 4983230072969 + 3 ^ 40 * 248537 * 2
def baseEnd_248537 : Nat := 127618941426599331544505

theorem tailTrace_248537 : CollatzResearch.WordTrace tailWord_248537 prefixEnd_248537 127618941426599331544505 := by
  unfold tailWord_248537
  simp only [CollatzResearch.WordTrace]
  refine ⟨9064889100600370585351865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6043259400400247056901243 9064889100600370585351865)
  ·
    refine ⟨6798666825450277939013899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9064889100600370585351865 6798666825450277939013899)
    ·
      refine ⟨10198000238175416908520849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6798666825450277939013899 10198000238175416908520849)
      ·
        refine ⟨7648500178631562681390637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10198000238175416908520849 7648500178631562681390637)
        ·
          refine ⟨2868187566986836005521489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7648500178631562681390637 2868187566986836005521489)
          ·
            refine ⟨2151140675240127004141117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868187566986836005521489 2151140675240127004141117)
            ·
              refine ⟨806677753215047626552919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2151140675240127004141117 806677753215047626552919)
              ·
                refine ⟨1210016629822571439829379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806677753215047626552919 1210016629822571439829379)
                ·
                  refine ⟨1815024944733857159744069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210016629822571439829379 1815024944733857159744069)
                  ·
                    refine ⟨340317177137598217452013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1815024944733857159744069 340317177137598217452013)
                    ·
                      refine ⟨127618941426599331544505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 340317177137598217452013 127618941426599331544505)
                      ·
                        rfl

theorem cell23_248537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_248537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248537 prefixEnd_248537 := by exact prefixLift 248537
  have htrace : WordTrace (prefixWord ++ tailWord_248537) baseStart_248537 baseEnd_248537 := by
    simpa [prefixWord, tailWord_248537, baseEnd_248537] using wordTrace_append hprefix tailTrace_248537
  have hstable : (prefixWord ++ tailWord_248537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248537).length < 2 ^ (prefixWord ++ tailWord_248537).sum := by decide
  have hdescent : baseEnd_248537 < baseStart_248537 := by decide
  rcases family_descends (prefixWord ++ tailWord_248537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248547 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 6]
def baseStart_248547 : Nat := 118140960795 + 248547 * 2 ^ 59
def prefixEnd_248547 : Nat := 4983230072969 + 3 ^ 40 * 248547 * 2
def baseEnd_248547 : Nat := 127624076233144292419459

theorem tailTrace_248547 : CollatzResearch.WordTrace tailWord_248547 prefixEnd_248547 127624076233144292419459 := by
  unfold tailWord_248547
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065253830564142293215895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6043502553709428195477263 9065253830564142293215895)
  ·
    refine ⟨13597880745846213439823843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9065253830564142293215895 13597880745846213439823843)
    ·
      refine ⟨20396821118769320159735765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13597880745846213439823843 20396821118769320159735765)
      ·
        refine ⟨478050494971155941243807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20396821118769320159735765 478050494971155941243807)
        ·
          refine ⟨717075742456733911865711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478050494971155941243807 717075742456733911865711)
          ·
            refine ⟨1075613613685100867798567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717075742456733911865711 1075613613685100867798567)
            ·
              refine ⟨1613420420527651301697851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075613613685100867798567 1613420420527651301697851)
              ·
                refine ⟨2420130630791476952546777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613420420527651301697851 2420130630791476952546777)
                ·
                  refine ⟨1815097973093607714410083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2420130630791476952546777 1815097973093607714410083)
                  ·
                    refine ⟨2722646959640411571615125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1815097973093607714410083 2722646959640411571615125)
                    ·
                      refine ⟨127624076233144292419459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2722646959640411571615125 127624076233144292419459)
                      ·
                        rfl

theorem cell23_248547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_248547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248547 prefixEnd_248547 := by exact prefixLift 248547
  have htrace : WordTrace (prefixWord ++ tailWord_248547) baseStart_248547 baseEnd_248547 := by
    simpa [prefixWord, tailWord_248547, baseEnd_248547] using wordTrace_append hprefix tailTrace_248547
  have hstable : (prefixWord ++ tailWord_248547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248547).length < 2 ^ (prefixWord ++ tailWord_248547).sum := by decide
  have hdescent : baseEnd_248547 < baseStart_248547 := by decide
  rcases family_descends (prefixWord ++ tailWord_248547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248557 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 8]
def baseStart_248557 : Nat := 118140960795 + 248557 * 2 ^ 59
def prefixEnd_248557 : Nat := 4983230072969 + 3 ^ 40 * 248557 * 2
def baseEnd_248557 : Nat := 14181023448854361477157

theorem tailTrace_248557 : CollatzResearch.WordTrace tailWord_248557 prefixEnd_248557 14181023448854361477157 := by
  unfold tailWord_248557
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065618560527914001079925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6043745707018609334053283 9065618560527914001079925)
  ·
    refine ⟨849901740049491937601243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9065618560527914001079925 849901740049491937601243)
    ·
      refine ⟨1274852610074237906401865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849901740049491937601243 1274852610074237906401865)
      ·
        refine ⟨956139457555678429801399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1274852610074237906401865 956139457555678429801399)
        ·
          refine ⟨1434209186333517644702099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956139457555678429801399 1434209186333517644702099)
          ·
            refine ⟨2151313779500276467053149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434209186333517644702099 2151313779500276467053149)
            ·
              refine ⟨806742667312603675144931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2151313779500276467053149 806742667312603675144931)
              ·
                refine ⟨1210114000968905512717397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806742667312603675144931 1210114000968905512717397)
                ·
                  refine ⟨14181023448854361477157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1210114000968905512717397 14181023448854361477157)
                  ·
                    rfl

theorem cell23_248557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_248557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248557 prefixEnd_248557 := by exact prefixLift 248557
  have htrace : WordTrace (prefixWord ++ tailWord_248557) baseStart_248557 baseEnd_248557 := by
    simpa [prefixWord, tailWord_248557, baseEnd_248557] using wordTrace_append hprefix tailTrace_248557
  have hstable : (prefixWord ++ tailWord_248557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248557).length < 2 ^ (prefixWord ++ tailWord_248557).sum := by decide
  have hdescent : baseEnd_248557 < baseStart_248557 := by decide
  rcases family_descends (prefixWord ++ tailWord_248557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248560 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_248560 : Nat := 118140960795 + 248560 * 2 ^ 59
def prefixEnd_248560 : Nat := 4983230072969 + 3 ^ 40 * 248560 * 2
def baseEnd_248560 : Nat := 127630751481652741556899

theorem tailTrace_248560 : CollatzResearch.WordTrace tailWord_248560 prefixEnd_248560 127630751481652741556899 := by
  unfold tailWord_248560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532863989758522756719567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6043818653011363675626089 4532863989758522756719567)
  ·
    refine ⟨6799295984637784135079351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4532863989758522756719567 6799295984637784135079351)
    ·
      refine ⟨10198943976956676202619027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6799295984637784135079351 10198943976956676202619027)
      ·
        refine ⟨15298415965435014303928541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10198943976956676202619027 15298415965435014303928541)
        ·
          refine ⟨5736905987038130363973203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15298415965435014303928541 5736905987038130363973203)
          ·
            refine ⟨8605358980557195545959805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736905987038130363973203 8605358980557195545959805)
            ·
              refine ⟨3227009617708948329734927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8605358980557195545959805 3227009617708948329734927)
              ·
                refine ⟨4840514426563422494602391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227009617708948329734927 4840514426563422494602391)
                ·
                  refine ⟨7260771639845133741903587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840514426563422494602391 7260771639845133741903587)
                  ·
                    refine ⟨10891157459767700612855381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7260771639845133741903587 10891157459767700612855381)
                    ·
                      refine ⟨127630751481652741556899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 10891157459767700612855381 127630751481652741556899)
                      ·
                        rfl

theorem cell23_248560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_248560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248560 prefixEnd_248560 := by exact prefixLift 248560
  have htrace : WordTrace (prefixWord ++ tailWord_248560) baseStart_248560 baseEnd_248560 := by
    simpa [prefixWord, tailWord_248560, baseEnd_248560] using wordTrace_append hprefix tailTrace_248560
  have hstable : (prefixWord ++ tailWord_248560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248560).length < 2 ^ (prefixWord ++ tailWord_248560).sum := by decide
  have hdescent : baseEnd_248560 < baseStart_248560 := by decide
  rcases family_descends (prefixWord ++ tailWord_248560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248601 : List Nat := [1, 2, 1, 2, 1, 1, 1, 9, 1, 1, 3]
def baseStart_248601 : Nat := 118140960795 + 248601 * 2 ^ 59
def prefixEnd_248601 : Nat := 4983230072969 + 3 ^ 40 * 248601 * 2
def baseEnd_248601 : Nat := 127651804188487081144211

theorem tailTrace_248601 : CollatzResearch.WordTrace tailWord_248601 prefixEnd_248601 127651804188487081144211 := by
  unfold tailWord_248601
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067223372368509515681657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6044815581579006343787771 9067223372368509515681657)
  ·
    refine ⟨6800417529276382136761243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9067223372368509515681657 6800417529276382136761243)
    ·
      refine ⟨10200626293914573205141865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6800417529276382136761243 10200626293914573205141865)
      ·
        refine ⟨7650469720435929903856399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10200626293914573205141865 7650469720435929903856399)
        ·
          refine ⟨11475704580653894855784599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650469720435929903856399 11475704580653894855784599)
          ·
            refine ⟨17213556870980842283676899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475704580653894855784599 17213556870980842283676899)
            ·
              refine ⟨25820335306471263425515349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17213556870980842283676899 25820335306471263425515349)
              ·
                refine ⟨151291027186355059133879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25820335306471263425515349 151291027186355059133879)
                ·
                  refine ⟨226936540779532588700819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151291027186355059133879 226936540779532588700819)
                  ·
                    refine ⟨340404811169298883051229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226936540779532588700819 340404811169298883051229)
                    ·
                      refine ⟨127651804188487081144211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 340404811169298883051229 127651804188487081144211)
                      ·
                        rfl

theorem cell23_248601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_248601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248601 prefixEnd_248601 := by exact prefixLift 248601
  have htrace : WordTrace (prefixWord ++ tailWord_248601) baseStart_248601 baseEnd_248601 := by
    simpa [prefixWord, tailWord_248601, baseEnd_248601] using wordTrace_append hprefix tailTrace_248601
  have hstable : (prefixWord ++ tailWord_248601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248601).length < 2 ^ (prefixWord ++ tailWord_248601).sum := by decide
  have hdescent : baseEnd_248601 < baseStart_248601 := by decide
  rcases family_descends (prefixWord ++ tailWord_248601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248604 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_248604 : Nat := 118140960795 + 248604 * 2 ^ 59
def prefixEnd_248604 : Nat := 4983230072969 + 3 ^ 40 * 248604 * 2
def baseEnd_248604 : Nat := 42551114876816856468899

theorem tailTrace_248604 : CollatzResearch.WordTrace tailWord_248604 prefixEnd_248604 42551114876816856468899 := by
  unfold tailWord_248604
  simp only [CollatzResearch.WordTrace]
  refine ⟨4533666395678820514020433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6044888527571760685360577 4533666395678820514020433)
  ·
    refine ⟨3400249796759115385515325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4533666395678820514020433 3400249796759115385515325)
    ·
      refine ⟨1275093673784668269568247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3400249796759115385515325 1275093673784668269568247)
      ·
        refine ⟨1912640510677002404352371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275093673784668269568247 1912640510677002404352371)
        ·
          refine ⟨2868960766015503606528557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912640510677002404352371 2868960766015503606528557)
          ·
            refine ⟨1075860287255813852448209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2868960766015503606528557 1075860287255813852448209)
            ·
              refine ⟨806895215441860389336157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075860287255813852448209 806895215441860389336157)
              ·
                refine ⟨302585705790697646001059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 806895215441860389336157 302585705790697646001059)
                ·
                  refine ⟨453878558686046469001589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302585705790697646001059 453878558686046469001589)
                  ·
                    refine ⟨42551114876816856468899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 453878558686046469001589 42551114876816856468899)
                    ·
                      rfl

theorem cell23_248604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_248604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248604 prefixEnd_248604 := by exact prefixLift 248604
  have htrace : WordTrace (prefixWord ++ tailWord_248604) baseStart_248604 baseEnd_248604 := by
    simpa [prefixWord, tailWord_248604, baseEnd_248604] using wordTrace_append hprefix tailTrace_248604
  have hstable : (prefixWord ++ tailWord_248604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248604).length < 2 ^ (prefixWord ++ tailWord_248604).sum := by decide
  have hdescent : baseEnd_248604 < baseStart_248604 := by decide
  rcases family_descends (prefixWord ++ tailWord_248604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248638 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_248638 : Nat := 118140960795 + 248638 * 2 ^ 59
def prefixEnd_248638 : Nat := 4983230072969 + 3 ^ 40 * 248638 * 2
def baseEnd_248638 : Nat := 42556934324234478793847

theorem tailTrace_248638 : CollatzResearch.WordTrace tailWord_248638 prefixEnd_248638 42556934324234478793847 := by
  unfold tailWord_248638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133571609154308104347321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6045715248822976556519045 1133571609154308104347321)
  ·
    refine ⟨850178706865731078260491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1133571609154308104347321 850178706865731078260491)
    ·
      refine ⟨1275268060298596617390737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850178706865731078260491 1275268060298596617390737)
      ·
        refine ⟨956451045223947463043053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1275268060298596617390737 956451045223947463043053)
        ·
          refine ⟨358669141958980298641145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 956451045223947463043053 358669141958980298641145)
          ·
            refine ⟨269001856469235223980859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358669141958980298641145 269001856469235223980859)
            ·
              refine ⟨403502784703852835971289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269001856469235223980859 403502784703852835971289)
              ·
                refine ⟨302627088527889626978467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403502784703852835971289 302627088527889626978467)
                ·
                  refine ⟨453940632791834440467701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302627088527889626978467 453940632791834440467701)
                  ·
                    refine ⟨42556934324234478793847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 453940632791834440467701 42556934324234478793847)
                    ·
                      rfl

theorem cell23_248638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_248638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248638 prefixEnd_248638 := by exact prefixLift 248638
  have htrace : WordTrace (prefixWord ++ tailWord_248638) baseStart_248638 baseEnd_248638 := by
    simpa [prefixWord, tailWord_248638, baseEnd_248638] using wordTrace_append hprefix tailTrace_248638
  have hstable : (prefixWord ++ tailWord_248638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248638).length < 2 ^ (prefixWord ++ tailWord_248638).sum := by decide
  have hdescent : baseEnd_248638 < baseStart_248638 := by decide
  rcases family_descends (prefixWord ++ tailWord_248638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248668 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_248668 : Nat := 118140960795 + 248668 * 2 ^ 59
def prefixEnd_248668 : Nat := 4983230072969 + 3 ^ 40 * 248668 * 2
def baseEnd_248668 : Nat := 42562069130779439668801

theorem tailTrace_248668 : CollatzResearch.WordTrace tailWord_248668 prefixEnd_248668 42562069130779439668801 := by
  unfold tailWord_248668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534833531562889979185329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6046444708750519972247105 4534833531562889979185329)
  ·
    refine ⟨3401125148672167484388997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4534833531562889979185329 3401125148672167484388997)
    ·
      refine ⟨637710965376031403322937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3401125148672167484388997 637710965376031403322937)
      ·
        refine ⟨478283224032023552492203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637710965376031403322937 478283224032023552492203)
        ·
          refine ⟨717424836048035328738305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478283224032023552492203 717424836048035328738305)
          ·
            refine ⟨538068627036026496553729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717424836048035328738305 538068627036026496553729)
            ·
              refine ⟨403551470277019872415297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538068627036026496553729 403551470277019872415297)
              ·
                refine ⟨302663602707764904311473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403551470277019872415297 302663602707764904311473)
                ·
                  refine ⟨226997702030823678233605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302663602707764904311473 226997702030823678233605)
                  ·
                    refine ⟨42562069130779439668801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226997702030823678233605 42562069130779439668801)
                    ·
                      rfl

theorem cell23_248668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_248668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248668 prefixEnd_248668 := by exact prefixLift 248668
  have htrace : WordTrace (prefixWord ++ tailWord_248668) baseStart_248668 baseEnd_248668 := by
    simpa [prefixWord, tailWord_248668, baseEnd_248668] using wordTrace_append hprefix tailTrace_248668
  have hstable : (prefixWord ++ tailWord_248668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248668).length < 2 ^ (prefixWord ++ tailWord_248668).sum := by decide
  have hdescent : baseEnd_248668 < baseStart_248668 := by decide
  rcases family_descends (prefixWord ++ tailWord_248668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248675 : List Nat := [1, 1, 1, 5, 3, 2, 1, 4, 1, 2, 2]
def baseStart_248675 : Nat := 118140960795 + 248675 * 2 ^ 59
def prefixEnd_248675 : Nat := 4983230072969 + 3 ^ 40 * 248675 * 2
def baseEnd_248675 : Nat := 127689801756919791618871

theorem tailTrace_248675 : CollatzResearch.WordTrace tailWord_248675 prefixEnd_248675 127689801756919791618871 := by
  unfold tailWord_248675
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069922374100420153875479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6046614916066946769250319 9069922374100420153875479)
  ·
    refine ⟨13604883561150630230813219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9069922374100420153875479 13604883561150630230813219)
    ·
      refine ⟨20407325341725945346219829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13604883561150630230813219 20407325341725945346219829)
      ·
        refine ⟨1913186750786807376208109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20407325341725945346219829 1913186750786807376208109)
        ·
          refine ⟨717445031545052766078041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1913186750786807376208109 717445031545052766078041)
          ·
            refine ⟨538083773658789574558531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717445031545052766078041 538083773658789574558531)
            ·
              refine ⟨807125660488184361837797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538083773658789574558531 807125660488184361837797)
              ·
                refine ⟨151336061341534567844587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807125660488184361837797 151336061341534567844587)
                ·
                  refine ⟨227004092012301851766881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151336061341534567844587 227004092012301851766881)
                  ·
                    refine ⟨170253069009226388825161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227004092012301851766881 170253069009226388825161)
                    ·
                      refine ⟨127689801756919791618871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170253069009226388825161 127689801756919791618871)
                      ·
                        rfl

theorem cell23_248675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_248675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248675 prefixEnd_248675 := by exact prefixLift 248675
  have htrace : WordTrace (prefixWord ++ tailWord_248675) baseStart_248675 baseEnd_248675 := by
    simpa [prefixWord, tailWord_248675, baseEnd_248675] using wordTrace_append hprefix tailTrace_248675
  have hstable : (prefixWord ++ tailWord_248675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248675).length < 2 ^ (prefixWord ++ tailWord_248675).sum := by decide
  have hdescent : baseEnd_248675 < baseStart_248675 := by decide
  rcases family_descends (prefixWord ++ tailWord_248675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248677 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_248677 : Nat := 118140960795 + 248677 * 2 ^ 59
def prefixEnd_248677 : Nat := 4983230072969 + 3 ^ 40 * 248677 * 2
def baseEnd_248677 : Nat := 42563609572742927931287

theorem tailTrace_248677 : CollatzResearch.WordTrace tailWord_248677 prefixEnd_248677 42563609572742927931287 := by
  unfold tailWord_248677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069995320093174495448285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6046663546728782996965523 9069995320093174495448285)
  ·
    refine ⟨3401248245034940435793107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9069995320093174495448285 3401248245034940435793107)
    ·
      refine ⟨5101872367552410653689661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3401248245034940435793107 5101872367552410653689661)
      ·
        refine ⟨1913202137832153995133623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5101872367552410653689661 1913202137832153995133623)
        ·
          refine ⟨2869803206748230992700435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913202137832153995133623 2869803206748230992700435)
          ·
            refine ⟨4304704810122346489050653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869803206748230992700435 4304704810122346489050653)
            ·
              refine ⟨1614264303795879933393995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4304704810122346489050653 1614264303795879933393995)
              ·
                refine ⟨2421396455693819900090993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614264303795879933393995 2421396455693819900090993)
                ·
                  refine ⟨1816047341770364925068245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2421396455693819900090993 1816047341770364925068245)
                  ·
                    refine ⟨42563609572742927931287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1816047341770364925068245 42563609572742927931287)
                    ·
                      rfl

theorem cell23_248677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_248677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248677 prefixEnd_248677 := by exact prefixLift 248677
  have htrace : WordTrace (prefixWord ++ tailWord_248677) baseStart_248677 baseEnd_248677 := by
    simpa [prefixWord, tailWord_248677, baseEnd_248677] using wordTrace_append hprefix tailTrace_248677
  have hstable : (prefixWord ++ tailWord_248677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248677).length < 2 ^ (prefixWord ++ tailWord_248677).sum := by decide
  have hdescent : baseEnd_248677 < baseStart_248677 := by decide
  rcases family_descends (prefixWord ++ tailWord_248677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248691 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 3]
def baseStart_248691 : Nat := 118140960795 + 248691 * 2 ^ 59
def prefixEnd_248691 : Nat := 4983230072969 + 3 ^ 40 * 248691 * 2
def baseEnd_248691 : Nat := 127698017447391729018797

theorem tailTrace_248691 : CollatzResearch.WordTrace tailWord_248691 prefixEnd_248691 127698017447391729018797 := by
  unfold tailWord_248691
  simp only [CollatzResearch.WordTrace]
  refine ⟨9070505942042454886457927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6047003961361636590971951 9070505942042454886457927)
  ·
    refine ⟨13605758913063682329686891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9070505942042454886457927 13605758913063682329686891)
    ·
      refine ⟨20408638369595523494530337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13605758913063682329686891 20408638369595523494530337)
      ·
        refine ⟨15306478777196642620897753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20408638369595523494530337 15306478777196642620897753)
        ·
          refine ⟨11479859082897481965673315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15306478777196642620897753 11479859082897481965673315)
          ·
            refine ⟨17219788624346222948509973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11479859082897481965673315 17219788624346222948509973)
            ·
              refine ⟨807177591766229200711405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17219788624346222948509973 807177591766229200711405)
              ·
                refine ⟨302691596912335950266777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 807177591766229200711405 302691596912335950266777)
                ·
                  refine ⟨227018697684251962700083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302691596912335950266777 227018697684251962700083)
                  ·
                    refine ⟨340528046526377944050125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227018697684251962700083 340528046526377944050125)
                    ·
                      refine ⟨127698017447391729018797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 340528046526377944050125 127698017447391729018797)
                      ·
                        rfl

theorem cell23_248691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 3].length) (baseStart_248691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248691 prefixEnd_248691 := by exact prefixLift 248691
  have htrace : WordTrace (prefixWord ++ tailWord_248691) baseStart_248691 baseEnd_248691 := by
    simpa [prefixWord, tailWord_248691, baseEnd_248691] using wordTrace_append hprefix tailTrace_248691
  have hstable : (prefixWord ++ tailWord_248691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248691).length < 2 ^ (prefixWord ++ tailWord_248691).sum := by decide
  have hdescent : baseEnd_248691 < baseStart_248691 := by decide
  rcases family_descends (prefixWord ++ tailWord_248691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248701 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_248701 : Nat := 118140960795 + 248701 * 2 ^ 59
def prefixEnd_248701 : Nat := 4983230072969 + 3 ^ 40 * 248701 * 2
def baseEnd_248701 : Nat := 127703152253936689893751

theorem tailTrace_248701 : CollatzResearch.WordTrace tailWord_248701 prefixEnd_248701 127703152253936689893751 := by
  unfold tailWord_248701
  simp only [CollatzResearch.WordTrace]
  refine ⟨9070870672006226594321957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6047247114670817729547971 9070870672006226594321957)
  ·
    refine ⟨1700788251001167486435367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9070870672006226594321957 1700788251001167486435367)
    ·
      refine ⟨2551182376501751229653051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700788251001167486435367 2551182376501751229653051)
      ·
        refine ⟨3826773564752626844479577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551182376501751229653051 3826773564752626844479577)
        ·
          refine ⟨2870080173564470133359683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3826773564752626844479577 2870080173564470133359683)
          ·
            refine ⟨4305120260346705200039525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870080173564470133359683 4305120260346705200039525)
            ·
              refine ⟨807210048815007225007411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4305120260346705200039525 807210048815007225007411)
              ·
                refine ⟨1210815073222510837511117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807210048815007225007411 1210815073222510837511117)
                ·
                  refine ⟨454055652458441564066669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210815073222510837511117 454055652458441564066669)
                  ·
                    refine ⟨170270869671915586525001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454055652458441564066669 170270869671915586525001)
                    ·
                      refine ⟨127703152253936689893751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170270869671915586525001 127703152253936689893751)
                      ·
                        rfl

theorem cell23_248701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_248701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248701 prefixEnd_248701 := by exact prefixLift 248701
  have htrace : WordTrace (prefixWord ++ tailWord_248701) baseStart_248701 baseEnd_248701 := by
    simpa [prefixWord, tailWord_248701, baseEnd_248701] using wordTrace_append hprefix tailTrace_248701
  have hstable : (prefixWord ++ tailWord_248701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248701).length < 2 ^ (prefixWord ++ tailWord_248701).sum := by decide
  have hdescent : baseEnd_248701 < baseStart_248701 := by decide
  rcases family_descends (prefixWord ++ tailWord_248701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248707 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 1, 8]
def baseStart_248707 : Nat := 118140960795 + 248707 * 2 ^ 59
def prefixEnd_248707 : Nat := 4983230072969 + 3 ^ 40 * 248707 * 2
def baseEnd_248707 : Nat := 42568744379287888806241

theorem tailTrace_248707 : CollatzResearch.WordTrace tailWord_248707 prefixEnd_248707 42568744379287888806241 := by
  unfold tailWord_248707
  simp only [CollatzResearch.WordTrace]
  refine ⟨9071089509984489619040375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6047393006656326412693583 9071089509984489619040375)
  ·
    refine ⟨13606634264976734428560563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9071089509984489619040375 13606634264976734428560563)
    ·
      refine ⟨20409951397465101642840845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13606634264976734428560563 20409951397465101642840845)
      ·
        refine ⟨7653731774049413116065317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20409951397465101642840845 7653731774049413116065317)
        ·
          refine ⟨1435074707634264959262247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7653731774049413116065317 1435074707634264959262247)
          ·
            refine ⟨2152612061451397438893371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435074707634264959262247 2152612061451397438893371)
            ·
              refine ⟨3228918092177096158340057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152612061451397438893371 3228918092177096158340057)
              ·
                refine ⟨2421688569132822118755043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3228918092177096158340057 2421688569132822118755043)
                ·
                  refine ⟨3632532853699233178132565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421688569132822118755043 3632532853699233178132565)
                  ·
                    refine ⟨42568744379287888806241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3632532853699233178132565 42568744379287888806241)
                    ·
                      rfl

theorem cell23_248707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 8].length) (baseStart_248707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248707 prefixEnd_248707 := by exact prefixLift 248707
  have htrace : WordTrace (prefixWord ++ tailWord_248707) baseStart_248707 baseEnd_248707 := by
    simpa [prefixWord, tailWord_248707, baseEnd_248707] using wordTrace_append hprefix tailTrace_248707
  have hstable : (prefixWord ++ tailWord_248707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248707).length < 2 ^ (prefixWord ++ tailWord_248707).sum := by decide
  have hdescent : baseEnd_248707 < baseStart_248707 := by decide
  rcases family_descends (prefixWord ++ tailWord_248707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248724 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_248724 : Nat := 118140960795 + 248724 * 2 ^ 59
def prefixEnd_248724 : Nat := 4983230072969 + 3 ^ 40 * 248724 * 2
def baseEnd_248724 : Nat := 42571654102996699968715

theorem tailTrace_248724 : CollatzResearch.WordTrace tailWord_248724 prefixEnd_248724 42571654102996699968715 := by
  unfold tailWord_248724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4535854775461450761204613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6047806367281934348272817 4535854775461450761204613)
  ·
    refine ⟨850472770399022017725865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4535854775461450761204613 850472770399022017725865)
    ·
      refine ⟨637854577799266513294399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 850472770399022017725865 637854577799266513294399)
      ·
        refine ⟨956781866698899769941599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637854577799266513294399 956781866698899769941599)
        ·
          refine ⟨1435172800048349654912399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956781866698899769941599 1435172800048349654912399)
          ·
            refine ⟨2152759200072524482368599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435172800048349654912399 2152759200072524482368599)
            ·
              refine ⟨3229138800108786723552899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152759200072524482368599 3229138800108786723552899)
              ·
                refine ⟨4843708200163180085329349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229138800108786723552899 4843708200163180085329349)
                ·
                  refine ⟨908195287530596265999253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4843708200163180085329349 908195287530596265999253)
                  ·
                    refine ⟨42571654102996699968715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 908195287530596265999253 42571654102996699968715)
                    ·
                      rfl

theorem cell23_248724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_248724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248724 prefixEnd_248724 := by exact prefixLift 248724
  have htrace : WordTrace (prefixWord ++ tailWord_248724) baseStart_248724 baseEnd_248724 := by
    simpa [prefixWord, tailWord_248724, baseEnd_248724] using wordTrace_append hprefix tailTrace_248724
  have hstable : (prefixWord ++ tailWord_248724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248724).length < 2 ^ (prefixWord ++ tailWord_248724).sum := by decide
  have hdescent : baseEnd_248724 < baseStart_248724 := by decide
  rcases family_descends (prefixWord ++ tailWord_248724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248794 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_248794 : Nat := 118140960795 + 248794 * 2 ^ 59
def prefixEnd_248794 : Nat := 4983230072969 + 3 ^ 40 * 248794 * 2
def baseEnd_248794 : Nat := 127750905954804826030823

theorem tailTrace_248794 : CollatzResearch.WordTrace tailWord_248794 prefixEnd_248794 127750905954804826030823 := by
  unfold tailWord_248794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268565665167325869364359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6049508440446202318304957 2268565665167325869364359)
  ·
    refine ⟨3402848497750988804046539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2268565665167325869364359 3402848497750988804046539)
    ·
      refine ⟨5104272746626483206069809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3402848497750988804046539 5104272746626483206069809)
      ·
        refine ⟨3828204559969862404552357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5104272746626483206069809 3828204559969862404552357)
        ·
          refine ⟨717788354994349200853567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3828204559969862404552357 717788354994349200853567)
          ·
            refine ⟨1076682532491523801280351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717788354994349200853567 1076682532491523801280351)
            ·
              refine ⟨1615023798737285701920527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076682532491523801280351 1615023798737285701920527)
              ·
                refine ⟨2422535698105928552880791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615023798737285701920527 2422535698105928552880791)
                ·
                  refine ⟨3633803547158892829321187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422535698105928552880791 3633803547158892829321187)
                  ·
                    refine ⟨5450705320738339243981781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633803547158892829321187 5450705320738339243981781)
                    ·
                      refine ⟨127750905954804826030823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5450705320738339243981781 127750905954804826030823)
                      ·
                        rfl

theorem cell23_248794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_248794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248794 prefixEnd_248794 := by exact prefixLift 248794
  have htrace : WordTrace (prefixWord ++ tailWord_248794) baseStart_248794 baseEnd_248794 := by
    simpa [prefixWord, tailWord_248794, baseEnd_248794] using wordTrace_append hprefix tailTrace_248794
  have hstable : (prefixWord ++ tailWord_248794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248794).length < 2 ^ (prefixWord ++ tailWord_248794).sum := by decide
  have hdescent : baseEnd_248794 < baseStart_248794 := by decide
  rcases family_descends (prefixWord ++ tailWord_248794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248799 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 2, 2, 2]
def baseStart_248799 : Nat := 118140960795 + 248799 * 2 ^ 59
def prefixEnd_248799 : Nat := 4983230072969 + 3 ^ 40 * 248799 * 2
def baseEnd_248799 : Nat := 127753473358077306468301

theorem tailTrace_248799 : CollatzResearch.WordTrace tailWord_248799 prefixEnd_248799 127753473358077306468301 := by
  unfold tailWord_248799
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074445025651189331389451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6049630017100792887592967 9074445025651189331389451)
  ·
    refine ⟨13611667538476783997084177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9074445025651189331389451 13611667538476783997084177)
    ·
      refine ⟨10208750653857587997813133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13611667538476783997084177 10208750653857587997813133)
      ·
        refine ⟨3828281495196595499179925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10208750653857587997813133 3828281495196595499179925)
        ·
          refine ⟨179450695087340414024059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3828281495196595499179925 179450695087340414024059)
          ·
            refine ⟨269176042631010621036089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179450695087340414024059 269176042631010621036089)
            ·
              refine ⟨201882031973257965777067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269176042631010621036089 201882031973257965777067)
              ·
                refine ⟨302823047959886948665601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201882031973257965777067 302823047959886948665601)
                ·
                  refine ⟨227117285969915211499201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302823047959886948665601 227117285969915211499201)
                  ·
                    refine ⟨170337964477436408624401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227117285969915211499201 170337964477436408624401)
                    ·
                      refine ⟨127753473358077306468301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170337964477436408624401 127753473358077306468301)
                      ·
                        rfl

theorem cell23_248799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_248799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248799 prefixEnd_248799 := by exact prefixLift 248799
  have htrace : WordTrace (prefixWord ++ tailWord_248799) baseStart_248799 baseEnd_248799 := by
    simpa [prefixWord, tailWord_248799, baseEnd_248799] using wordTrace_append hprefix tailTrace_248799
  have hstable : (prefixWord ++ tailWord_248799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248799).length < 2 ^ (prefixWord ++ tailWord_248799).sum := by decide
  have hdescent : baseEnd_248799 < baseStart_248799 := by decide
  rcases family_descends (prefixWord ++ tailWord_248799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248804 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_248804 : Nat := 118140960795 + 248804 * 2 ^ 59
def prefixEnd_248804 : Nat := 4983230072969 + 3 ^ 40 * 248804 * 2
def baseEnd_248804 : Nat := 127756040761349786905777

theorem tailTrace_248804 : CollatzResearch.WordTrace tailWord_248804 prefixEnd_248804 127756040761349786905777 := by
  unfold tailWord_248804
  simp only [CollatzResearch.WordTrace]
  refine ⟨4537313695316537592660733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6049751593755383456880977 4537313695316537592660733)
  ·
    refine ⟨1701492635743701597247775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4537313695316537592660733 1701492635743701597247775)
    ·
      refine ⟨2552238953615552395871663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701492635743701597247775 2552238953615552395871663)
      ·
        refine ⟨3828358430423328593807495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552238953615552395871663 3828358430423328593807495)
        ·
          refine ⟨5742537645634992890711243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3828358430423328593807495 5742537645634992890711243)
          ·
            refine ⟨8613806468452489336066865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742537645634992890711243 8613806468452489336066865)
            ·
              refine ⟨6460354851339367002050149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8613806468452489336066865 6460354851339367002050149)
              ·
                refine ⟨1211316534626131312884403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6460354851339367002050149 1211316534626131312884403)
                ·
                  refine ⟨1816974801939196969326605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211316534626131312884403 1816974801939196969326605)
                  ·
                    refine ⟨681365550727198863497477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816974801939196969326605 681365550727198863497477)
                    ·
                      refine ⟨127756040761349786905777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 681365550727198863497477 127756040761349786905777)
                      ·
                        rfl

theorem cell23_248804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_248804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248804 prefixEnd_248804 := by exact prefixLift 248804
  have htrace : WordTrace (prefixWord ++ tailWord_248804) baseStart_248804 baseEnd_248804 := by
    simpa [prefixWord, tailWord_248804, baseEnd_248804] using wordTrace_append hprefix tailTrace_248804
  have hstable : (prefixWord ++ tailWord_248804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248804).length < 2 ^ (prefixWord ++ tailWord_248804).sum := by decide
  have hdescent : baseEnd_248804 < baseStart_248804 := by decide
  rcases family_descends (prefixWord ++ tailWord_248804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248911 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 4, 6, 2]
def baseStart_248911 : Nat := 118140960795 + 248911 * 2 ^ 59
def prefixEnd_248911 : Nat := 4983230072969 + 3 ^ 40 * 248911 * 2
def baseEnd_248911 : Nat := 127810983191380868267785

theorem tailTrace_248911 : CollatzResearch.WordTrace tailWord_248911 prefixEnd_248911 127810983191380868267785 := by
  unfold tailWord_248911
  simp only [CollatzResearch.WordTrace]
  refine ⟨9078530001245432459466587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6052353334163621639644391 9078530001245432459466587)
  ·
    refine ⟨13617795001868148689199881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9078530001245432459466587 13617795001868148689199881)
    ·
      refine ⟨10213346251401111516899911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13617795001868148689199881 10213346251401111516899911)
      ·
        refine ⟨15320019377101667275349867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10213346251401111516899911 15320019377101667275349867)
        ·
          refine ⟨22980029065652500913024801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15320019377101667275349867 22980029065652500913024801)
          ·
            refine ⟨17235021799239375684768601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22980029065652500913024801 17235021799239375684768601)
            ·
              refine ⟨12926266349429531763576451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17235021799239375684768601 12926266349429531763576451)
              ·
                refine ⟨19389399524144297645364677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12926266349429531763576451 19389399524144297645364677)
                ·
                  refine ⟨3635512410777055808505877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19389399524144297645364677 3635512410777055808505877)
                  ·
                    refine ⟨170414644255174491023713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3635512410777055808505877 170414644255174491023713)
                    ·
                      refine ⟨127810983191380868267785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170414644255174491023713 127810983191380868267785)
                      ·
                        rfl

theorem cell23_248911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6, 2].length) (baseStart_248911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248911 prefixEnd_248911 := by exact prefixLift 248911
  have htrace : WordTrace (prefixWord ++ tailWord_248911) baseStart_248911 baseEnd_248911 := by
    simpa [prefixWord, tailWord_248911, baseEnd_248911] using wordTrace_append hprefix tailTrace_248911
  have hstable : (prefixWord ++ tailWord_248911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248911).length < 2 ^ (prefixWord ++ tailWord_248911).sum := by decide
  have hdescent : baseEnd_248911 < baseStart_248911 := by decide
  rcases family_descends (prefixWord ++ tailWord_248911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248928 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4]
def baseStart_248928 : Nat := 118140960795 + 248928 * 2 ^ 59
def prefixEnd_248928 : Nat := 4983230072969 + 3 ^ 40 * 248928 * 2
def baseEnd_248928 : Nat := 127819712362507301755207

theorem tailTrace_248928 : CollatzResearch.WordTrace tailWord_248928 prefixEnd_248928 127819712362507301755207 := by
  unfold tailWord_248928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539575021091922181417719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6052766694789229575223625 4539575021091922181417719)
  ·
    refine ⟨6809362531637883272126579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4539575021091922181417719 6809362531637883272126579)
    ·
      refine ⟨10214043797456824908189869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809362531637883272126579 10214043797456824908189869)
      ·
        refine ⟨3830266424046309340571201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10214043797456824908189869 3830266424046309340571201)
        ·
          refine ⟨2872699818034732005428401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3830266424046309340571201 2872699818034732005428401)
          ·
            refine ⟨2154524863526049004071301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2872699818034732005428401 2154524863526049004071301)
            ·
              refine ⟨403973411911134188263369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2154524863526049004071301 403973411911134188263369)
              ·
                refine ⟨302980058933350641197527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403973411911134188263369 302980058933350641197527)
                ·
                  refine ⟨454470088400025961796291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302980058933350641197527 454470088400025961796291)
                  ·
                    refine ⟨681705132600038942694437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 454470088400025961796291 681705132600038942694437)
                    ·
                      refine ⟨127819712362507301755207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 681705132600038942694437 127819712362507301755207)
                      ·
                        rfl

theorem cell23_248928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_248928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248928 prefixEnd_248928 := by exact prefixLift 248928
  have htrace : WordTrace (prefixWord ++ tailWord_248928) baseStart_248928 baseEnd_248928 := by
    simpa [prefixWord, tailWord_248928, baseEnd_248928] using wordTrace_append hprefix tailTrace_248928
  have hstable : (prefixWord ++ tailWord_248928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248928).length < 2 ^ (prefixWord ++ tailWord_248928).sum := by decide
  have hdescent : baseEnd_248928 < baseStart_248928 := by decide
  rcases family_descends (prefixWord ++ tailWord_248928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248938 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_248938 : Nat := 118140960795 + 248938 * 2 ^ 59
def prefixEnd_248938 : Nat := 4983230072969 + 3 ^ 40 * 248938 * 2
def baseEnd_248938 : Nat := 42608282389684087543387

theorem tailTrace_248938 : CollatzResearch.WordTrace tailWord_248938 prefixEnd_248938 42608282389684087543387 := by
  unfold tailWord_248938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269878693036904017674867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6053009848098410713799645 2269878693036904017674867)
  ·
    refine ⟨3404818039555356026512301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2269878693036904017674867 3404818039555356026512301)
    ·
      refine ⟨1276806764833258509942113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3404818039555356026512301 1276806764833258509942113)
      ·
        refine ⟨957605073624943882456585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1276806764833258509942113 957605073624943882456585)
        ·
          refine ⟨718203805218707911842439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957605073624943882456585 718203805218707911842439)
          ·
            refine ⟨1077305707828061867763659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718203805218707911842439 1077305707828061867763659)
            ·
              refine ⟨1615958561742092801645489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077305707828061867763659 1615958561742092801645489)
              ·
                refine ⟨1211968921306569601234117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615958561742092801645489 1211968921306569601234117)
                ·
                  refine ⟨227244172744981800231397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211968921306569601234117 227244172744981800231397)
                  ·
                    refine ⟨42608282389684087543387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227244172744981800231397 42608282389684087543387)
                    ·
                      rfl

theorem cell23_248938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_248938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248938 prefixEnd_248938 := by exact prefixLift 248938
  have htrace : WordTrace (prefixWord ++ tailWord_248938) baseStart_248938 baseEnd_248938 := by
    simpa [prefixWord, tailWord_248938, baseEnd_248938] using wordTrace_append hprefix tailTrace_248938
  have hstable : (prefixWord ++ tailWord_248938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248938).length < 2 ^ (prefixWord ++ tailWord_248938).sum := by decide
  have hdescent : baseEnd_248938 < baseStart_248938 := by decide
  rcases family_descends (prefixWord ++ tailWord_248938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248968 : List Nat := [2, 1, 3, 4, 2, 1, 2, 8]
def baseStart_248968 : Nat := 118140960795 + 248968 * 2 ^ 59
def prefixEnd_248968 : Nat := 4983230072969 + 3 ^ 40 * 248968 * 2
def baseEnd_248968 : Nat := 4734824132914338713149

theorem tailTrace_248968 : CollatzResearch.WordTrace tailWord_248968 prefixEnd_248968 4734824132914338713149 := by
  unfold tailWord_248968
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540304481019465597145779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6053739308025954129527705 4540304481019465597145779)
  ·
    refine ⟨6810456721529198395718669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4540304481019465597145779 6810456721529198395718669)
    ·
      refine ⟨2553921270573449398394501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6810456721529198395718669 2553921270573449398394501)
      ·
        refine ⟨478860238232521762198969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2553921270573449398394501 478860238232521762198969)
        ·
          refine ⟨359145178674391321649227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478860238232521762198969 359145178674391321649227)
          ·
            refine ⟨538717768011586982473841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359145178674391321649227 538717768011586982473841)
            ·
              refine ⟨404038326008690236855381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538717768011586982473841 404038326008690236855381)
              ·
                refine ⟨4734824132914338713149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 404038326008690236855381 4734824132914338713149)
                ·
                  rfl

theorem cell23_248968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 8].length) (baseStart_248968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_248968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_248968 prefixEnd_248968 := by exact prefixLift 248968
  have htrace : WordTrace (prefixWord ++ tailWord_248968) baseStart_248968 baseEnd_248968 := by
    simpa [prefixWord, tailWord_248968, baseEnd_248968] using wordTrace_append hprefix tailTrace_248968
  have hstable : (prefixWord ++ tailWord_248968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248968).length < 2 ^ (prefixWord ++ tailWord_248968).sum := by decide
  have hdescent : baseEnd_248968 < baseStart_248968 := by decide
  rcases family_descends (prefixWord ++ tailWord_248968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249018 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2]
def baseStart_249018 : Nat := 118140960795 + 249018 * 2 ^ 59
def prefixEnd_249018 : Nat := 4983230072969 + 3 ^ 40 * 249018 * 2
def baseEnd_249018 : Nat := 127865925621411949629793

theorem tailTrace_249018 : CollatzResearch.WordTrace tailWord_249018 prefixEnd_249018 127865925621411949629793 := by
  unfold tailWord_249018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270608152964447433402927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6054955074571859822407805 2270608152964447433402927)
  ·
    refine ⟨3405912229446671150104391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2270608152964447433402927 3405912229446671150104391)
    ·
      refine ⟨5108868344170006725156587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405912229446671150104391 5108868344170006725156587)
      ·
        refine ⟨7663302516255010087734881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108868344170006725156587 7663302516255010087734881)
        ·
          refine ⟨5747476887191257565801161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7663302516255010087734881 5747476887191257565801161)
          ·
            refine ⟨4310607665393443174350871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5747476887191257565801161 4310607665393443174350871)
            ·
              refine ⟨6465911498090164761526307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310607665393443174350871 6465911498090164761526307)
              ·
                refine ⟨9698867247135247142289461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465911498090164761526307 9698867247135247142289461)
                ·
                  refine ⟨909268804418929419589637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9698867247135247142289461 909268804418929419589637)
                  ·
                    refine ⟨170487900828549266173057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909268804418929419589637 170487900828549266173057)
                    ·
                      refine ⟨127865925621411949629793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170487900828549266173057 127865925621411949629793)
                      ·
                        rfl

theorem cell23_249018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_249018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249018 prefixEnd_249018 := by exact prefixLift 249018
  have htrace : WordTrace (prefixWord ++ tailWord_249018) baseStart_249018 baseEnd_249018 := by
    simpa [prefixWord, tailWord_249018, baseEnd_249018] using wordTrace_append hprefix tailTrace_249018
  have hstable : (prefixWord ++ tailWord_249018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249018).length < 2 ^ (prefixWord ++ tailWord_249018).sum := by decide
  have hdescent : baseEnd_249018 < baseStart_249018 := by decide
  rcases family_descends (prefixWord ++ tailWord_249018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249021 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_249021 : Nat := 118140960795 + 249021 * 2 ^ 59
def prefixEnd_249021 : Nat := 4983230072969 + 3 ^ 40 * 249021 * 2
def baseEnd_249021 : Nat := 127867466063375437892279

theorem tailTrace_249021 : CollatzResearch.WordTrace tailWord_249021 prefixEnd_249021 127867466063375437892279 := by
  unfold tailWord_249021
  simp only [CollatzResearch.WordTrace]
  refine ⟨9082542030846921245970917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6055028020564614163980611 9082542030846921245970917)
  ·
    refine ⟨1702976630783797733619547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9082542030846921245970917 1702976630783797733619547)
    ·
      refine ⟨2554464946175696600429321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702976630783797733619547 2554464946175696600429321)
      ·
        refine ⟨1915848709631772450321991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2554464946175696600429321 1915848709631772450321991)
        ·
          refine ⟨2873773064447658675482987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915848709631772450321991 2873773064447658675482987)
          ·
            refine ⟨4310659596671488013224481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873773064447658675482987 4310659596671488013224481)
            ·
              refine ⟨3232994697503616009918361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310659596671488013224481 3232994697503616009918361)
              ·
                refine ⟨2424746023127712007438771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3232994697503616009918361 2424746023127712007438771)
                ·
                  refine ⟨3637119034691568011158157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424746023127712007438771 3637119034691568011158157)
                  ·
                    refine ⟨1363919638009338004184309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637119034691568011158157 1363919638009338004184309)
                    ·
                      refine ⟨127867466063375437892279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1363919638009338004184309 127867466063375437892279)
                      ·
                        rfl

theorem cell23_249021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_249021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249021 prefixEnd_249021 := by exact prefixLift 249021
  have htrace : WordTrace (prefixWord ++ tailWord_249021) baseStart_249021 baseEnd_249021 := by
    simpa [prefixWord, tailWord_249021, baseEnd_249021] using wordTrace_append hprefix tailTrace_249021
  have hstable : (prefixWord ++ tailWord_249021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249021).length < 2 ^ (prefixWord ++ tailWord_249021).sum := by decide
  have hdescent : baseEnd_249021 < baseStart_249021 := by decide
  rcases family_descends (prefixWord ++ tailWord_249021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249068 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_249068 : Nat := 118140960795 + 249068 * 2 ^ 59
def prefixEnd_249068 : Nat := 4983230072969 + 3 ^ 40 * 249068 * 2
def baseEnd_249068 : Nat := 127891599654136754004563

theorem tailTrace_249068 : CollatzResearch.WordTrace tailWord_249068 prefixEnd_249068 127891599654136754004563 := by
  unfold tailWord_249068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4542128130838324136465929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6056170841117765515287905 4542128130838324136465929)
  ·
    refine ⟨3406596098128743102349447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4542128130838324136465929 3406596098128743102349447)
    ·
      refine ⟨5109894147193114653524171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406596098128743102349447 5109894147193114653524171)
      ·
        refine ⟨7664841220789671980286257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109894147193114653524171 7664841220789671980286257)
        ·
          refine ⟨5748630915592253985214693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7664841220789671980286257 5748630915592253985214693)
          ·
            refine ⟨1077868296673547622227755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5748630915592253985214693 1077868296673547622227755)
            ·
              refine ⟨1616802445010321433341633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077868296673547622227755 1616802445010321433341633)
              ·
                refine ⟨1212601833757741075006225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616802445010321433341633 1212601833757741075006225)
                ·
                  refine ⟨909451375318305806254669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1212601833757741075006225 909451375318305806254669)
                  ·
                    refine ⟨341044265744364677345501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909451375318305806254669 341044265744364677345501)
                    ·
                      refine ⟨127891599654136754004563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 341044265744364677345501 127891599654136754004563)
                      ·
                        rfl

theorem cell23_249068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_249068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249068 prefixEnd_249068 := by exact prefixLift 249068
  have htrace : WordTrace (prefixWord ++ tailWord_249068) baseStart_249068 baseEnd_249068 := by
    simpa [prefixWord, tailWord_249068, baseEnd_249068] using wordTrace_append hprefix tailTrace_249068
  have hstable : (prefixWord ++ tailWord_249068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249068).length < 2 ^ (prefixWord ++ tailWord_249068).sum := by decide
  have hdescent : baseEnd_249068 < baseStart_249068 := by decide
  rcases family_descends (prefixWord ++ tailWord_249068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249069 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_249069 : Nat := 118140960795 + 249069 * 2 ^ 59
def prefixEnd_249069 : Nat := 4983230072969 + 3 ^ 40 * 249069 * 2
def baseEnd_249069 : Nat := 127892113134791250092059

theorem tailTrace_249069 : CollatzResearch.WordTrace tailWord_249069 prefixEnd_249069 127892113134791250092059 := by
  unfold tailWord_249069
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084292734673025443718261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6056195156448683629145507 9084292734673025443718261)
  ·
    refine ⟨851652443875596135348587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9084292734673025443718261 851652443875596135348587)
    ·
      refine ⟨1277478665813394203022881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 851652443875596135348587 1277478665813394203022881)
      ·
        refine ⟨958108999360045652267161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1277478665813394203022881 958108999360045652267161)
        ·
          refine ⟨718581749520034239200371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958108999360045652267161 718581749520034239200371)
          ·
            refine ⟨1077872624280051358800557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718581749520034239200371 1077872624280051358800557)
            ·
              refine ⟨404202234105019259550209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077872624280051358800557 404202234105019259550209)
              ·
                refine ⟨303151675578764444662657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404202234105019259550209 303151675578764444662657)
                ·
                  refine ⟨227363756684073333496993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303151675578764444662657 227363756684073333496993)
                  ·
                    refine ⟨170522817513055000122745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227363756684073333496993 170522817513055000122745)
                    ·
                      refine ⟨127892113134791250092059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170522817513055000122745 127892113134791250092059)
                      ·
                        rfl

theorem cell23_249069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_249069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249069 prefixEnd_249069 := by exact prefixLift 249069
  have htrace : WordTrace (prefixWord ++ tailWord_249069) baseStart_249069 baseEnd_249069 := by
    simpa [prefixWord, tailWord_249069, baseEnd_249069] using wordTrace_append hprefix tailTrace_249069
  have hstable : (prefixWord ++ tailWord_249069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249069).length < 2 ^ (prefixWord ++ tailWord_249069).sum := by decide
  have hdescent : baseEnd_249069 < baseStart_249069 := by decide
  rcases family_descends (prefixWord ++ tailWord_249069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249081 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_249081 : Nat := 118140960795 + 249081 * 2 ^ 59
def prefixEnd_249081 : Nat := 4983230072969 + 3 ^ 40 * 249081 * 2
def baseEnd_249081 : Nat := 127898274902645203142003

theorem tailTrace_249081 : CollatzResearch.WordTrace tailWord_249081 prefixEnd_249081 127898274902645203142003 := by
  unfold tailWord_249081
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084730410629551493155097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6056486940419700995436731 9084730410629551493155097)
  ·
    refine ⟨6813547807972163619866323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9084730410629551493155097 6813547807972163619866323)
    ·
      refine ⟨10220321711958245429799485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813547807972163619866323 10220321711958245429799485)
      ·
        refine ⟨3832620641984342036174807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10220321711958245429799485 3832620641984342036174807)
        ·
          refine ⟨5748930962976513054262211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832620641984342036174807 5748930962976513054262211)
          ·
            refine ⟨8623396444464769581393317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748930962976513054262211 8623396444464769581393317)
            ·
              refine ⟨1616886833337144296511247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8623396444464769581393317 1616886833337144296511247)
              ·
                refine ⟨2425330250005716444766871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616886833337144296511247 2425330250005716444766871)
                ·
                  refine ⟨3637995375008574667150307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425330250005716444766871 3637995375008574667150307)
                  ·
                    refine ⟨5456993062512862000725461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3637995375008574667150307 5456993062512862000725461)
                    ·
                      refine ⟨127898274902645203142003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5456993062512862000725461 127898274902645203142003)
                      ·
                        rfl

theorem cell23_249081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_249081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249081 prefixEnd_249081 := by exact prefixLift 249081
  have htrace : WordTrace (prefixWord ++ tailWord_249081) baseStart_249081 baseEnd_249081 := by
    simpa [prefixWord, tailWord_249081, baseEnd_249081] using wordTrace_append hprefix tailTrace_249081
  have hstable : (prefixWord ++ tailWord_249081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249081).length < 2 ^ (prefixWord ++ tailWord_249081).sum := by decide
  have hdescent : baseEnd_249081 < baseStart_249081 := by decide
  rcases family_descends (prefixWord ++ tailWord_249081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249086 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_249086 : Nat := 118140960795 + 249086 * 2 ^ 59
def prefixEnd_249086 : Nat := 4983230072969 + 3 ^ 40 * 249086 * 2
def baseEnd_249086 : Nat := 127900842305917683579481

theorem tailTrace_249086 : CollatzResearch.WordTrace tailWord_249086 prefixEnd_249086 127900842305917683579481 := by
  unfold tailWord_249086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135614096951429668385889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6056608517074291564724741 1135614096951429668385889)
  ·
    refine ⟨851710572713572251289417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1135614096951429668385889 851710572713572251289417)
    ·
      refine ⟨638782929535179188467063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 851710572713572251289417 638782929535179188467063)
      ·
        refine ⟨958174394302768782700595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638782929535179188467063 958174394302768782700595)
        ·
          refine ⟨1437261591454153174050893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958174394302768782700595 1437261591454153174050893)
          ·
            refine ⟨538973096795307440269085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1437261591454153174050893 538973096795307440269085)
            ·
              refine ⟨202114911298240290100907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538973096795307440269085 202114911298240290100907)
              ·
                refine ⟨303172366947360435151361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202114911298240290100907 303172366947360435151361)
                ·
                  refine ⟨227379275210520326363521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303172366947360435151361 227379275210520326363521)
                  ·
                    refine ⟨170534456407890244772641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227379275210520326363521 170534456407890244772641)
                    ·
                      refine ⟨127900842305917683579481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170534456407890244772641 127900842305917683579481)
                      ·
                        rfl

theorem cell23_249086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_249086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249086 prefixEnd_249086 := by exact prefixLift 249086
  have htrace : WordTrace (prefixWord ++ tailWord_249086) baseStart_249086 baseEnd_249086 := by
    simpa [prefixWord, tailWord_249086, baseEnd_249086] using wordTrace_append hprefix tailTrace_249086
  have hstable : (prefixWord ++ tailWord_249086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249086).length < 2 ^ (prefixWord ++ tailWord_249086).sum := by decide
  have hdescent : baseEnd_249086 < baseStart_249086 := by decide
  rcases family_descends (prefixWord ++ tailWord_249086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249125 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_249125 : Nat := 118140960795 + 249125 * 2 ^ 59
def prefixEnd_249125 : Nat := 4983230072969 + 3 ^ 40 * 249125 * 2
def baseEnd_249125 : Nat := 127920868051443030991801

theorem tailTrace_249125 : CollatzResearch.WordTrace tailWord_249125 prefixEnd_249125 127920868051443030991801 := by
  unfold tailWord_249125
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086335222470147007756829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6057556814980098005171219 9086335222470147007756829)
  ·
    refine ⟨3407375708426305127908811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9086335222470147007756829 3407375708426305127908811)
    ·
      refine ⟨5111063562639457691863217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407375708426305127908811 5111063562639457691863217)
      ·
        refine ⟨3833297671979593268897413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5111063562639457691863217 3833297671979593268897413)
        ·
          refine ⟨718743313496173737918265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3833297671979593268897413 718743313496173737918265)
          ·
            refine ⟨539057485122130303438699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718743313496173737918265 539057485122130303438699)
            ·
              refine ⟨808586227683195455158049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539057485122130303438699 808586227683195455158049)
              ·
                refine ⟨606439670762396591368537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808586227683195455158049 606439670762396591368537)
                ·
                  refine ⟨454829753071797443526403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606439670762396591368537 454829753071797443526403)
                  ·
                    refine ⟨682244629607696165289605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 454829753071797443526403 682244629607696165289605)
                    ·
                      refine ⟨127920868051443030991801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 682244629607696165289605 127920868051443030991801)
                      ·
                        rfl

theorem cell23_249125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_249125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249125 prefixEnd_249125 := by exact prefixLift 249125
  have htrace : WordTrace (prefixWord ++ tailWord_249125) baseStart_249125 baseEnd_249125 := by
    simpa [prefixWord, tailWord_249125, baseEnd_249125] using wordTrace_append hprefix tailTrace_249125
  have hstable : (prefixWord ++ tailWord_249125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249125).length < 2 ^ (prefixWord ++ tailWord_249125).sum := by decide
  have hdescent : baseEnd_249125 < baseStart_249125 := by decide
  rcases family_descends (prefixWord ++ tailWord_249125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249219 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 2, 3, 2]
def baseStart_249219 : Nat := 118140960795 + 249219 * 2 ^ 59
def prefixEnd_249219 : Nat := 4983230072969 + 3 ^ 40 * 249219 * 2
def baseEnd_249219 : Nat := 127969135232965663216369

theorem tailTrace_249219 : CollatzResearch.WordTrace tailWord_249219 prefixEnd_249219 127969135232965663216369 := by
  unfold tailWord_249219
  simp only [CollatzResearch.WordTrace]
  refine ⟨9089763684129601061678711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6059842456086400707785807 9089763684129601061678711)
  ·
    refine ⟨13634645526194401592518067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9089763684129601061678711 13634645526194401592518067)
    ·
      refine ⟨20451968289291602388777101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13634645526194401592518067 20451968289291602388777101)
      ·
        refine ⟨7669488108484350895791413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20451968289291602388777101 7669488108484350895791413)
        ·
          refine ⟨719014510170407896480445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7669488108484350895791413 719014510170407896480445)
          ·
            refine ⟨269630441313902961180167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 719014510170407896480445 269630441313902961180167)
            ·
              refine ⟨404445661970854441770251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269630441313902961180167 404445661970854441770251)
              ·
                refine ⟨606668492956281662655377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404445661970854441770251 606668492956281662655377)
                ·
                  refine ⟨455001369717211246991533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606668492956281662655377 455001369717211246991533)
                  ·
                    refine ⟨170625513643954217621825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 455001369717211246991533 170625513643954217621825)
                    ·
                      refine ⟨127969135232965663216369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 170625513643954217621825 127969135232965663216369)
                      ·
                        rfl

theorem cell23_249219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_249219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_249219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_249219 prefixEnd_249219 := by exact prefixLift 249219
  have htrace : WordTrace (prefixWord ++ tailWord_249219) baseStart_249219 baseEnd_249219 := by
    simpa [prefixWord, tailWord_249219, baseEnd_249219] using wordTrace_append hprefix tailTrace_249219
  have hstable : (prefixWord ++ tailWord_249219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249219).length < 2 ^ (prefixWord ++ tailWord_249219).sum := by decide
  have hdescent : baseEnd_249219 < baseStart_249219 := by decide
  rcases family_descends (prefixWord ++ tailWord_249219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
