import V185TrunkScan23Chunk0379

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2246256 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 1, 1, 4]
def baseStart_2246256 : Nat := 118140960795 + 2246256 * 2 ^ 59
def prefixEnd_2246256 : Nat := 4983230072969 + 3 ^ 40 * 2246256 * 2
def baseEnd_2246256 : Nat := 1153409001045868746769663

theorem tailTrace_2246256 : CollatzResearch.WordTrace tailWord_2246256 prefixEnd_2246256 1153409001045868746769663 := by
  unfold tailWord_2246256
  simp only [CollatzResearch.WordTrace]
  refine ⟨40963843475102808413783311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54618457966803744551711081 40963843475102808413783311)
  ·
    refine ⟨61445765212654212620674967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40963843475102808413783311 61445765212654212620674967)
    ·
      refine ⟨92168647818981318931012451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61445765212654212620674967 92168647818981318931012451)
      ·
        refine ⟨138252971728471978396518677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92168647818981318931012451 138252971728471978396518677)
        ·
          refine ⟨6480608049772123987336813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 138252971728471978396518677 6480608049772123987336813)
          ·
            refine ⟨2430228018664546495251305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6480608049772123987336813 2430228018664546495251305)
            ·
              refine ⟨1822671013998409871438479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430228018664546495251305 1822671013998409871438479)
              ·
                refine ⟨2734006520997614807157719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822671013998409871438479 2734006520997614807157719)
                ·
                  refine ⟨4101009781496422210736579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734006520997614807157719 4101009781496422210736579)
                  ·
                    refine ⟨6151514672244633316104869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4101009781496422210736579 6151514672244633316104869)
                    ·
                      refine ⟨1153409001045868746769663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6151514672244633316104869 1153409001045868746769663)
                      ·
                        rfl

theorem cell23_2246256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 1, 4].length) (baseStart_2246256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246256 prefixEnd_2246256 := by exact prefixLift 2246256
  have htrace : WordTrace (prefixWord ++ tailWord_2246256) baseStart_2246256 baseEnd_2246256 := by
    simpa [prefixWord, tailWord_2246256, baseEnd_2246256] using wordTrace_append hprefix tailTrace_2246256
  have hstable : (prefixWord ++ tailWord_2246256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246256).length < 2 ^ (prefixWord ++ tailWord_2246256).sum := by decide
  have hdescent : baseEnd_2246256 < baseStart_2246256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246262 : List Nat := [5, 1, 1, 2, 2, 2, 10]
def baseStart_2246262 : Nat := 118140960795 + 2246262 * 2 ^ 59
def prefixEnd_2246262 : Nat := 4983230072969 + 3 ^ 40 * 2246262 * 2
def baseEnd_2246262 : Nat := 14239655332466613867835

theorem tailTrace_2246262 : CollatzResearch.WordTrace tailWord_2246262 prefixEnd_2246262 14239655332466613867835 := by
  unfold tailWord_2246262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120494111761492490767815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54618603858789253234856693 5120494111761492490767815)
  ·
    refine ⟨7680741167642238736151723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5120494111761492490767815 7680741167642238736151723)
    ·
      refine ⟨11521111751463358104227585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7680741167642238736151723 11521111751463358104227585)
      ·
        refine ⟨8640833813597518578170689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11521111751463358104227585 8640833813597518578170689)
        ·
          refine ⟨6480625360198138933628017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8640833813597518578170689 6480625360198138933628017)
          ·
            refine ⟨4860469020148604200221013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6480625360198138933628017 4860469020148604200221013)
            ·
              refine ⟨14239655332466613867835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4860469020148604200221013 14239655332466613867835)
              ·
                rfl

theorem cell23_2246262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 10].length) (baseStart_2246262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246262 prefixEnd_2246262 := by exact prefixLift 2246262
  have htrace : WordTrace (prefixWord ++ tailWord_2246262) baseStart_2246262 baseEnd_2246262 := by
    simpa [prefixWord, tailWord_2246262, baseEnd_2246262] using wordTrace_append hprefix tailTrace_2246262
  have hstable : (prefixWord ++ tailWord_2246262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246262).length < 2 ^ (prefixWord ++ tailWord_2246262).sum := by decide
  have hdescent : baseEnd_2246262 < baseStart_2246262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246273 : List Nat := [1, 2, 4, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_2246273 : Nat := 118140960795 + 2246273 * 2 ^ 59
def prefixEnd_2246273 : Nat := 4983230072969 + 3 ^ 40 * 2246273 * 2
def baseEnd_2246273 : Nat := 1153417730216995180257085

theorem tailTrace_2246273 : CollatzResearch.WordTrace tailWord_2246273 prefixEnd_2246273 1153417730216995180257085 := by
  unfold tailWord_2246273
  simp only [CollatzResearch.WordTrace]
  refine ⟨81928306991144028730935473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54618871327429352487290315 81928306991144028730935473)
  ·
    refine ⟨61446230243358021548201605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81928306991144028730935473 61446230243358021548201605)
    ·
      refine ⟨11521168170629629040287801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61446230243358021548201605 11521168170629629040287801)
      ·
        refine ⟨8640876127972221780215851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11521168170629629040287801 8640876127972221780215851)
        ·
          refine ⟨12961314191958332670323777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640876127972221780215851 12961314191958332670323777)
          ·
            refine ⟨9720985643968749502742833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12961314191958332670323777 9720985643968749502742833)
            ·
              refine ⟨7290739232976562127057125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9720985643968749502742833 7290739232976562127057125)
              ·
                refine ⟨1367013606183105398823211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7290739232976562127057125 1367013606183105398823211)
                ·
                  refine ⟨2050520409274658098234817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367013606183105398823211 2050520409274658098234817)
                  ·
                    refine ⟨1537890306955993573676113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2050520409274658098234817 1537890306955993573676113)
                    ·
                      refine ⟨1153417730216995180257085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537890306955993573676113 1153417730216995180257085)
                      ·
                        rfl

theorem cell23_2246273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_2246273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246273 prefixEnd_2246273 := by exact prefixLift 2246273
  have htrace : WordTrace (prefixWord ++ tailWord_2246273) baseStart_2246273 baseEnd_2246273 := by
    simpa [prefixWord, tailWord_2246273, baseEnd_2246273] using wordTrace_append hprefix tailTrace_2246273
  have hstable : (prefixWord ++ tailWord_2246273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246273).length < 2 ^ (prefixWord ++ tailWord_2246273).sum := by decide
  have hdescent : baseEnd_2246273 < baseStart_2246273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246432 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2246432 : Nat := 118140960795 + 2246432 * 2 ^ 59
def prefixEnd_2246432 : Nat := 4983230072969 + 3 ^ 40 * 2246432 * 2
def baseEnd_2246432 : Nat := 1153499373641060058168853

theorem tailTrace_2246432 : CollatzResearch.WordTrace tailWord_2246432 prefixEnd_2246432 1153499373641060058168853 := by
  unfold tailWord_2246432
  simp only [CollatzResearch.WordTrace]
  refine ⟨40967053098783999442986775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54622737465045332590649033 40967053098783999442986775)
  ·
    refine ⟨61450579648175999164480163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40967053098783999442986775 61450579648175999164480163)
    ·
      refine ⟨92175869472263998746720245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61450579648175999164480163 92175869472263998746720245)
      ·
        refine ⟨8641487763024749882505023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92175869472263998746720245 8641487763024749882505023)
        ·
          refine ⟨12962231644537124823757535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8641487763024749882505023 12962231644537124823757535)
          ·
            refine ⟨19443347466805687235636303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12962231644537124823757535 19443347466805687235636303)
            ·
              refine ⟨29165021200208530853454455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19443347466805687235636303 29165021200208530853454455)
              ·
                refine ⟨43747531800312796280181683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29165021200208530853454455 43747531800312796280181683)
                ·
                  refine ⟨65621297700469194420272525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43747531800312796280181683 65621297700469194420272525)
                  ·
                    refine ⟨24607986637675947907602197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65621297700469194420272525 24607986637675947907602197)
                    ·
                      refine ⟨1153499373641060058168853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24607986637675947907602197 1153499373641060058168853)
                      ·
                        rfl

theorem cell23_2246432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2246432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246432 prefixEnd_2246432 := by exact prefixLift 2246432
  have htrace : WordTrace (prefixWord ++ tailWord_2246432) baseStart_2246432 baseEnd_2246432 := by
    simpa [prefixWord, tailWord_2246432, baseEnd_2246432] using wordTrace_append hprefix tailTrace_2246432
  have hstable : (prefixWord ++ tailWord_2246432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246432).length < 2 ^ (prefixWord ++ tailWord_2246432).sum := by decide
  have hdescent : baseEnd_2246432 < baseStart_2246432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246436 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_2246436 : Nat := 118140960795 + 2246436 * 2 ^ 59
def prefixEnd_2246436 : Nat := 4983230072969 + 3 ^ 40 * 2246436 * 2
def baseEnd_2246436 : Nat := 1153501427563678042518835

theorem tailTrace_2246436 : CollatzResearch.WordTrace tailWord_2246436 prefixEnd_2246436 1153501427563678042518835 := by
  unfold tailWord_2246436
  simp only [CollatzResearch.WordTrace]
  refine ⟨40967126044776753784559581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54622834726369005046079441 40967126044776753784559581)
  ·
    refine ⟨15362672266791282669209843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40967126044776753784559581 15362672266791282669209843)
    ·
      refine ⟨23044008400186924003814765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15362672266791282669209843 23044008400186924003814765)
      ·
        refine ⟨8641503150070096501430537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23044008400186924003814765 8641503150070096501430537)
        ·
          refine ⟨6481127362552572376072903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8641503150070096501430537 6481127362552572376072903)
          ·
            refine ⟨9721691043828858564109355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481127362552572376072903 9721691043828858564109355)
            ·
              refine ⟨14582536565743287846164033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721691043828858564109355 14582536565743287846164033)
              ·
                refine ⟨10936902424307465884623025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14582536565743287846164033 10936902424307465884623025)
                ·
                  refine ⟨8202676818230599413467269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10936902424307465884623025 8202676818230599413467269)
                  ·
                    refine ⟨1538001903418237390025113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8202676818230599413467269 1538001903418237390025113)
                    ·
                      refine ⟨1153501427563678042518835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538001903418237390025113 1153501427563678042518835)
                      ·
                        rfl

theorem cell23_2246436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_2246436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246436 prefixEnd_2246436 := by exact prefixLift 2246436
  have htrace : WordTrace (prefixWord ++ tailWord_2246436) baseStart_2246436 baseEnd_2246436 := by
    simpa [prefixWord, tailWord_2246436, baseEnd_2246436] using wordTrace_append hprefix tailTrace_2246436
  have hstable : (prefixWord ++ tailWord_2246436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246436).length < 2 ^ (prefixWord ++ tailWord_2246436).sum := by decide
  have hdescent : baseEnd_2246436 < baseStart_2246436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246489 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 1, 5]
def baseStart_2246489 : Nat := 118140960795 + 2246489 * 2 ^ 59
def prefixEnd_2246489 : Nat := 4983230072969 + 3 ^ 40 * 2246489 * 2
def baseEnd_2246489 : Nat := 384509547346122111718697

theorem tailTrace_2246489 : CollatzResearch.WordTrace tailWord_2246489 prefixEnd_2246489 384509547346122111718697 := by
  unfold tailWord_2246489
  simp only [CollatzResearch.WordTrace]
  refine ⟨81936185158361497620798521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54624123438907665080532347 81936185158361497620798521)
  ·
    refine ⟨61452138868771123215598891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81936185158361497620798521 61452138868771123215598891)
    ·
      refine ⟨92178208303156684823398337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61452138868771123215598891 92178208303156684823398337)
      ·
        refine ⟨69133656227367513617548753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92178208303156684823398337 69133656227367513617548753)
        ·
          refine ⟨51850242170525635213161565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69133656227367513617548753 51850242170525635213161565)
          ·
            refine ⟨19443840813947113204935587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51850242170525635213161565 19443840813947113204935587)
            ·
              refine ⟨29165761220920669807403381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19443840813947113204935587 29165761220920669807403381)
              ·
                refine ⟨2734290114461312794444067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29165761220920669807403381 2734290114461312794444067)
                ·
                  refine ⟨4101435171691969191666101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734290114461312794444067 4101435171691969191666101)
                  ·
                    refine ⟨384509547346122111718697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4101435171691969191666101 384509547346122111718697)
                    ·
                      rfl

theorem cell23_2246489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_2246489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246489 prefixEnd_2246489 := by exact prefixLift 2246489
  have htrace : WordTrace (prefixWord ++ tailWord_2246489) baseStart_2246489 baseEnd_2246489 := by
    simpa [prefixWord, tailWord_2246489, baseEnd_2246489] using wordTrace_append hprefix tailTrace_2246489
  have hstable : (prefixWord ++ tailWord_2246489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246489).length < 2 ^ (prefixWord ++ tailWord_2246489).sum := by decide
  have hdescent : baseEnd_2246489 < baseStart_2246489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246496 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 4, 3, 2]
def baseStart_2246496 : Nat := 118140960795 + 2246496 * 2 ^ 59
def prefixEnd_2246496 : Nat := 4983230072969 + 3 ^ 40 * 2246496 * 2
def baseEnd_2246496 : Nat := 1153532236402947807768559

theorem tailTrace_2246496 : CollatzResearch.WordTrace tailWord_2246496 prefixEnd_2246496 1153532236402947807768559 := by
  unfold tailWord_2246496
  simp only [CollatzResearch.WordTrace]
  refine ⟨40968220234668068908151671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54624293646224091877535561 40968220234668068908151671)
  ·
    refine ⟨61452330352002103362227507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40968220234668068908151671 61452330352002103362227507)
    ·
      refine ⟨92178495528003155043341261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61452330352002103362227507 92178495528003155043341261)
      ·
        refine ⟨34566935823001183141252973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92178495528003155043341261 34566935823001183141252973)
        ·
          refine ⟨12962600933625443677969865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34566935823001183141252973 12962600933625443677969865)
          ·
            refine ⟨9721950700219082758477399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12962600933625443677969865 9721950700219082758477399)
            ·
              refine ⟨14582926050328624137716099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721950700219082758477399 14582926050328624137716099)
              ·
                refine ⟨21874389075492936206574149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582926050328624137716099 21874389075492936206574149)
                ·
                  refine ⟨4101447951654925538732653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21874389075492936206574149 4101447951654925538732653)
                  ·
                    refine ⟨1538042981870597077024745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4101447951654925538732653 1538042981870597077024745)
                    ·
                      refine ⟨1153532236402947807768559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538042981870597077024745 1153532236402947807768559)
                      ·
                        rfl

theorem cell23_2246496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_2246496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246496 prefixEnd_2246496 := by exact prefixLift 2246496
  have htrace : WordTrace (prefixWord ++ tailWord_2246496) baseStart_2246496 baseEnd_2246496 := by
    simpa [prefixWord, tailWord_2246496, baseEnd_2246496] using wordTrace_append hprefix tailTrace_2246496
  have hstable : (prefixWord ++ tailWord_2246496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246496).length < 2 ^ (prefixWord ++ tailWord_2246496).sum := by decide
  have hdescent : baseEnd_2246496 < baseStart_2246496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246536 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 1, 6]
def baseStart_2246536 : Nat := 118140960795 + 2246536 * 2 ^ 59
def prefixEnd_2246536 : Nat := 4983230072969 + 3 ^ 40 * 2246536 * 2
def baseEnd_2246536 : Nat := 384517591876375883756125

theorem tailTrace_2246536 : CollatzResearch.WordTrace tailWord_2246536 prefixEnd_2246536 384517591876375883756125 := by
  unfold tailWord_2246536
  simp only [CollatzResearch.WordTrace]
  refine ⟨40968949694595612323879731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54625266259460816431839641 40968949694595612323879731)
  ·
    refine ⟨61453424541893418485819597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40968949694595612323879731 61453424541893418485819597)
    ·
      refine ⟨23045034203210031932182349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61453424541893418485819597 23045034203210031932182349)
      ·
        refine ⟨8641887826203761974568381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23045034203210031932182349 8641887826203761974568381)
        ·
          refine ⟨3240707934826410740463143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8641887826203761974568381 3240707934826410740463143)
          ·
            refine ⟨4861061902239616110694715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240707934826410740463143 4861061902239616110694715)
            ·
              refine ⟨7291592853359424166042073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861061902239616110694715 7291592853359424166042073)
              ·
                refine ⟨5468694640019568124531555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7291592853359424166042073 5468694640019568124531555)
                ·
                  refine ⟨8203041960029352186797333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5468694640019568124531555 8203041960029352186797333)
                  ·
                    refine ⟨384517591876375883756125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8203041960029352186797333 384517591876375883756125)
                    ·
                      rfl

theorem cell23_2246536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_2246536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246536 prefixEnd_2246536 := by exact prefixLift 2246536
  have htrace : WordTrace (prefixWord ++ tailWord_2246536) baseStart_2246536 baseEnd_2246536 := by
    simpa [prefixWord, tailWord_2246536, baseEnd_2246536] using wordTrace_append hprefix tailTrace_2246536
  have hstable : (prefixWord ++ tailWord_2246536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246536).length < 2 ^ (prefixWord ++ tailWord_2246536).sum := by decide
  have hdescent : baseEnd_2246536 < baseStart_2246536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246603 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 1, 3, 2]
def baseStart_2246603 : Nat := 118140960795 + 2246603 * 2 ^ 59
def prefixEnd_2246603 : Nat := 4983230072969 + 3 ^ 40 * 2246603 * 2
def baseEnd_2246603 : Nat := 1153587178832978889130567

theorem tailTrace_2246603 : CollatzResearch.WordTrace tailWord_2246603 prefixEnd_2246603 1153587178832978889130567 := by
  unfold tailWord_2246603
  simp only [CollatzResearch.WordTrace]
  refine ⟨81940343079948495090448463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54626895386632330060298975 81940343079948495090448463)
  ·
    refine ⟨122910514619922742635672695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81940343079948495090448463 122910514619922742635672695)
    ·
      refine ⟨184365771929884113953509043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122910514619922742635672695 184365771929884113953509043)
      ·
        refine ⟨276548657894826170930263565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184365771929884113953509043 276548657894826170930263565)
        ·
          refine ⟨103705746710559814098848837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276548657894826170930263565 103705746710559814098848837)
          ·
            refine ⟨19444827508229965143534157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103705746710559814098848837 19444827508229965143534157)
            ·
              refine ⟨7291810315586236928825309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19444827508229965143534157 7291810315586236928825309)
              ·
                refine ⟨2734428868344838848309491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7291810315586236928825309 2734428868344838848309491)
                ·
                  refine ⟨4101643302517258272464237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734428868344838848309491 4101643302517258272464237)
                  ·
                    refine ⟨1538116238443971852174089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4101643302517258272464237 1538116238443971852174089)
                    ·
                      refine ⟨1153587178832978889130567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538116238443971852174089 1153587178832978889130567)
                      ·
                        rfl

theorem cell23_2246603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 3, 2].length) (baseStart_2246603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246603 prefixEnd_2246603 := by exact prefixLift 2246603
  have htrace : WordTrace (prefixWord ++ tailWord_2246603) baseStart_2246603 baseEnd_2246603 := by
    simpa [prefixWord, tailWord_2246603, baseEnd_2246603] using wordTrace_append hprefix tailTrace_2246603
  have hstable : (prefixWord ++ tailWord_2246603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246603).length < 2 ^ (prefixWord ++ tailWord_2246603).sum := by decide
  have hdescent : baseEnd_2246603 < baseStart_2246603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246610 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2246610 : Nat := 118140960795 + 2246610 * 2 ^ 59
def prefixEnd_2246610 : Nat := 4983230072969 + 3 ^ 40 * 2246610 * 2
def baseEnd_2246610 : Nat := 1153590773197560361743035

theorem tailTrace_2246610 : CollatzResearch.WordTrace tailWord_2246610 prefixEnd_2246610 1153590773197560361743035 := by
  unfold tailWord_2246610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20485149597730783821488321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54627065593948756857302189 20485149597730783821488321)
  ·
    refine ⟨15363862198298087866116241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20485149597730783821488321 15363862198298087866116241)
    ·
      refine ⟨11522896648723565899587181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15363862198298087866116241 11522896648723565899587181)
      ·
        refine ⟨4321086243271337212345193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11522896648723565899587181 4321086243271337212345193)
        ·
          refine ⟨3240814682453502909258895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4321086243271337212345193 3240814682453502909258895)
          ·
            refine ⟨4861222023680254363888343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240814682453502909258895 4861222023680254363888343)
            ·
              refine ⟨7291833035520381545832515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861222023680254363888343 7291833035520381545832515)
              ·
                refine ⟨10937749553280572318748773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7291833035520381545832515 10937749553280572318748773)
                ·
                  refine ⟨2050828041240107309765395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10937749553280572318748773 2050828041240107309765395)
                  ·
                    refine ⟨3076242061860160964648093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2050828041240107309765395 3076242061860160964648093)
                    ·
                      refine ⟨1153590773197560361743035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3076242061860160964648093 1153590773197560361743035)
                      ·
                        rfl

theorem cell23_2246610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2246610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246610 prefixEnd_2246610 := by exact prefixLift 2246610
  have htrace : WordTrace (prefixWord ++ tailWord_2246610) baseStart_2246610 baseEnd_2246610 := by
    simpa [prefixWord, tailWord_2246610, baseEnd_2246610] using wordTrace_append hprefix tailTrace_2246610
  have hstable : (prefixWord ++ tailWord_2246610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246610).length < 2 ^ (prefixWord ++ tailWord_2246610).sum := by decide
  have hdescent : baseEnd_2246610 < baseStart_2246610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246639 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 7]
def baseStart_2246639 : Nat := 118140960795 + 2246639 * 2 ^ 59
def prefixEnd_2246639 : Nat := 4983230072969 + 3 ^ 40 * 2246639 * 2
def baseEnd_2246639 : Nat := 128178407126282305364489

theorem tailTrace_2246639 : CollatzResearch.WordTrace tailWord_2246639 prefixEnd_2246639 128178407126282305364489 := by
  unfold tailWord_2246639
  simp only [CollatzResearch.WordTrace]
  refine ⟨81941656107818073238758971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54627770738545382159172647 81941656107818073238758971)
  ·
    refine ⟨122912484161727109858138457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81941656107818073238758971 122912484161727109858138457)
    ·
      refine ⟨92184363121295332393603843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122912484161727109858138457 92184363121295332393603843)
      ·
        refine ⟨138276544681942998590405765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92184363121295332393603843 138276544681942998590405765)
        ·
          refine ⟨25926852127864312235701081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138276544681942998590405765 25926852127864312235701081)
          ·
            refine ⟨19445139095898234176775811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25926852127864312235701081 19445139095898234176775811)
            ·
              refine ⟨29167708643847351265163717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19445139095898234176775811 29167708643847351265163717)
              ·
                refine ⟨5468945370721378362218197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29167708643847351265163717 5468945370721378362218197)
                ·
                  refine ⟨128178407126282305364489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5468945370721378362218197 128178407126282305364489)
                  ·
                    rfl

theorem cell23_2246639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 7].length) (baseStart_2246639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246639 prefixEnd_2246639 := by exact prefixLift 2246639
  have htrace : WordTrace (prefixWord ++ tailWord_2246639) baseStart_2246639 baseEnd_2246639 := by
    simpa [prefixWord, tailWord_2246639, baseEnd_2246639] using wordTrace_append hprefix tailTrace_2246639
  have hstable : (prefixWord ++ tailWord_2246639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246639).length < 2 ^ (prefixWord ++ tailWord_2246639).sum := by decide
  have hdescent : baseEnd_2246639 < baseStart_2246639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246656 : List Nat := [2, 1, 1, 2, 1, 1, 1, 9, 5]
def baseStart_2246656 : Nat := 118140960795 + 2246656 * 2 ^ 59
def prefixEnd_2246656 : Nat := 4983230072969 + 3 ^ 40 * 2246656 * 2
def baseEnd_2246656 : Nat := 128179377034185242418647

theorem tailTrace_2246656 : CollatzResearch.WordTrace tailWord_2246656 prefixEnd_2246656 128179377034185242418647 := by
  unfold tailWord_2246656
  simp only [CollatzResearch.WordTrace]
  refine ⟨40971138074378242571063911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54628184099170990094751881 40971138074378242571063911)
  ·
    refine ⟨61456707111567363856595867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40971138074378242571063911 61456707111567363856595867)
    ·
      refine ⟨92185060667351045784893801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61456707111567363856595867 92185060667351045784893801)
      ·
        refine ⟨69138795500513284338670351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92185060667351045784893801 69138795500513284338670351)
        ·
          refine ⟨103708193250769926508005527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69138795500513284338670351 103708193250769926508005527)
          ·
            refine ⟨155562289876154889762008291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103708193250769926508005527 155562289876154889762008291)
            ·
              refine ⟨233343434814232334643012437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155562289876154889762008291 233343434814232334643012437)
              ·
                refine ⟨1367246688364642585798901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 233343434814232334643012437 1367246688364642585798901)
                ·
                  refine ⟨128179377034185242418647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1367246688364642585798901 128179377034185242418647)
                  ·
                    rfl

theorem cell23_2246656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 5].length) (baseStart_2246656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246656 prefixEnd_2246656 := by exact prefixLift 2246656
  have htrace : WordTrace (prefixWord ++ tailWord_2246656) baseStart_2246656 baseEnd_2246656 := by
    simpa [prefixWord, tailWord_2246656, baseEnd_2246656] using wordTrace_append hprefix tailTrace_2246656
  have hstable : (prefixWord ++ tailWord_2246656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246656).length < 2 ^ (prefixWord ++ tailWord_2246656).sum := by decide
  have hdescent : baseEnd_2246656 < baseStart_2246656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246684 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_2246684 : Nat := 118140960795 + 2246684 * 2 ^ 59
def prefixEnd_2246684 : Nat := 4983230072969 + 3 ^ 40 * 2246684 * 2
def baseEnd_2246684 : Nat := 1153628770765993072217695

theorem tailTrace_2246684 : CollatzResearch.WordTrace tailWord_2246684 prefixEnd_2246684 1153628770765993072217695 := by
  unfold tailWord_2246684
  simp only [CollatzResearch.WordTrace]
  refine ⟨40971648696327522962073553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54628864928436697282764737 40971648696327522962073553)
  ·
    refine ⟨30728736522245642221555165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40971648696327522962073553 30728736522245642221555165)
    ·
      refine ⟨11523276195842115833083187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30728736522245642221555165 11523276195842115833083187)
      ·
        refine ⟨17284914293763173749624781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11523276195842115833083187 17284914293763173749624781)
        ·
          refine ⟨6481842860161190156109293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17284914293763173749624781 6481842860161190156109293)
          ·
            refine ⟨2430691072560446308540985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6481842860161190156109293 2430691072560446308540985)
            ·
              refine ⟨1823018304420334731405739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430691072560446308540985 1823018304420334731405739)
              ·
                refine ⟨2734527456630502097108609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823018304420334731405739 2734527456630502097108609)
                ·
                  refine ⟨2050895592472876572831457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2734527456630502097108609 2050895592472876572831457)
                  ·
                    refine ⟨1538171694354657429623593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2050895592472876572831457 1538171694354657429623593)
                    ·
                      refine ⟨1153628770765993072217695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538171694354657429623593 1153628770765993072217695)
                      ·
                        rfl

theorem cell23_2246684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_2246684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246684 prefixEnd_2246684 := by exact prefixLift 2246684
  have htrace : WordTrace (prefixWord ++ tailWord_2246684) baseStart_2246684 baseEnd_2246684 := by
    simpa [prefixWord, tailWord_2246684, baseEnd_2246684] using wordTrace_append hprefix tailTrace_2246684
  have hstable : (prefixWord ++ tailWord_2246684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246684).length < 2 ^ (prefixWord ++ tailWord_2246684).sum := by decide
  have hdescent : baseEnd_2246684 < baseStart_2246684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246739 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9]
def baseStart_2246739 : Nat := 118140960795 + 2246739 * 2 ^ 59
def prefixEnd_2246739 : Nat := 4983230072969 + 3 ^ 40 * 2246739 * 2
def baseEnd_2246739 : Nat := 1153657012201990357029941

theorem tailTrace_2246739 : CollatzResearch.WordTrace tailWord_2246739 prefixEnd_2246739 1153657012201990357029941 := by
  unfold tailWord_2246739
  simp only [CollatzResearch.WordTrace]
  refine ⟨81945303407455790317399271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54630202271637193544932847 81945303407455790317399271)
  ·
    refine ⟨122917955111183685476098907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81945303407455790317399271 122917955111183685476098907)
    ·
      refine ⟨184376932666775528214148361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122917955111183685476098907 184376932666775528214148361)
      ·
        refine ⟨138282699500081646160611271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184376932666775528214148361 138282699500081646160611271)
        ·
          refine ⟨207424049250122469240916907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138282699500081646160611271 207424049250122469240916907)
          ·
            refine ⟨311136073875183703861375361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207424049250122469240916907 311136073875183703861375361)
            ·
              refine ⟨233352055406387777896031521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311136073875183703861375361 233352055406387777896031521)
              ·
                refine ⟨175014041554790833422023641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233352055406387777896031521 175014041554790833422023641)
                ·
                  refine ⟨131260531166093125066517731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175014041554790833422023641 131260531166093125066517731)
                  ·
                    refine ⟨196890796749139687599776597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131260531166093125066517731 196890796749139687599776597)
                    ·
                      refine ⟨1153657012201990357029941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 196890796749139687599776597 1153657012201990357029941)
                      ·
                        rfl

theorem cell23_2246739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_2246739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246739 prefixEnd_2246739 := by exact prefixLift 2246739
  have htrace : WordTrace (prefixWord ++ tailWord_2246739) baseStart_2246739 baseEnd_2246739 := by
    simpa [prefixWord, tailWord_2246739, baseEnd_2246739] using wordTrace_append hprefix tailTrace_2246739
  have hstable : (prefixWord ++ tailWord_2246739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246739).length < 2 ^ (prefixWord ++ tailWord_2246739).sum := by decide
  have hdescent : baseEnd_2246739 < baseStart_2246739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246746 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 6]
def baseStart_2246746 : Nat := 118140960795 + 2246746 * 2 ^ 59
def prefixEnd_2246746 : Nat := 4983230072969 + 3 ^ 40 * 2246746 * 2
def baseEnd_2246746 : Nat := 128184511840730203293601

theorem tailTrace_2246746 : CollatzResearch.WordTrace tailWord_2246746 prefixEnd_2246746 128184511840730203293601 := by
  unfold tailWord_2246746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20486389679607607628226023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54630372478953620341936061 20486389679607607628226023)
  ·
    refine ⟨30729584519411411442339035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20486389679607607628226023 30729584519411411442339035)
    ·
      refine ⟨46094376779117117163508553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30729584519411411442339035 46094376779117117163508553)
      ·
        refine ⟨34570782584337837872631415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46094376779117117163508553 34570782584337837872631415)
        ·
          refine ⟨51856173876506756808947123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34570782584337837872631415 51856173876506756808947123)
          ·
            refine ⟨77784260814760135213420685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51856173876506756808947123 77784260814760135213420685)
            ·
              refine ⟨29169097805535050705032757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77784260814760135213420685 29169097805535050705032757)
              ·
                refine ⟨2734602919268911003596821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29169097805535050705032757 2734602919268911003596821)
                ·
                  refine ⟨128184511840730203293601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2734602919268911003596821 128184511840730203293601)
                  ·
                    rfl

theorem cell23_2246746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_2246746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246746 prefixEnd_2246746 := by exact prefixLift 2246746
  have htrace : WordTrace (prefixWord ++ tailWord_2246746) baseStart_2246746 baseEnd_2246746 := by
    simpa [prefixWord, tailWord_2246746, baseEnd_2246746] using wordTrace_append hprefix tailTrace_2246746
  have hstable : (prefixWord ++ tailWord_2246746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246746).length < 2 ^ (prefixWord ++ tailWord_2246746).sum := by decide
  have hdescent : baseEnd_2246746 < baseStart_2246746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246856 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2246856 : Nat := 118140960795 + 2246856 * 2 ^ 59
def prefixEnd_2246856 : Nat := 4983230072969 + 3 ^ 40 * 2246856 * 2
def baseEnd_2246856 : Nat := 1153717089438566399266903

theorem tailTrace_2246856 : CollatzResearch.WordTrace tailWord_2246856 prefixEnd_2246856 1153717089438566399266903 := by
  unfold tailWord_2246856
  simp only [CollatzResearch.WordTrace]
  refine ⟨40974785374015959649704211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54633047165354612866272281 40974785374015959649704211)
  ·
    refine ⟨61462178061023939474556317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40974785374015959649704211 61462178061023939474556317)
    ·
      refine ⟨23048316772883977302958619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61462178061023939474556317 23048316772883977302958619)
      ·
        refine ⟨34572475159325965954437929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23048316772883977302958619 34572475159325965954437929)
        ·
          refine ⟨25929356369494474465828447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34572475159325965954437929 25929356369494474465828447)
          ·
            refine ⟨38894034554241711698742671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25929356369494474465828447 38894034554241711698742671)
            ·
              refine ⟨58341051831362567548114007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38894034554241711698742671 58341051831362567548114007)
              ·
                refine ⟨87511577747043851322171011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58341051831362567548114007 87511577747043851322171011)
                ·
                  refine ⟨131267366620565776983256517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87511577747043851322171011 131267366620565776983256517)
                  ·
                    refine ⟨24612631241356083184360597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131267366620565776983256517 24612631241356083184360597)
                    ·
                      refine ⟨1153717089438566399266903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24612631241356083184360597 1153717089438566399266903)
                      ·
                        rfl

theorem cell23_2246856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2246856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246856 prefixEnd_2246856 := by exact prefixLift 2246856
  have htrace : WordTrace (prefixWord ++ tailWord_2246856) baseStart_2246856 baseEnd_2246856 := by
    simpa [prefixWord, tailWord_2246856, baseEnd_2246856] using wordTrace_append hprefix tailTrace_2246856
  have hstable : (prefixWord ++ tailWord_2246856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246856).length < 2 ^ (prefixWord ++ tailWord_2246856).sum := by decide
  have hdescent : baseEnd_2246856 < baseStart_2246856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246863 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 3]
def baseStart_2246863 : Nat := 118140960795 + 2246863 * 2 ^ 59
def prefixEnd_2246863 : Nat := 4983230072969 + 3 ^ 40 * 2246863 * 2
def baseEnd_2246863 : Nat := 1153720683803147871879371

theorem tailTrace_2246863 : CollatzResearch.WordTrace tailWord_2246863 prefixEnd_2246863 1153720683803147871879371 := by
  unfold tailWord_2246863
  simp only [CollatzResearch.WordTrace]
  refine ⟨81949826059006559494913243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54633217372671039663275495 81949826059006559494913243)
  ·
    refine ⟨122924739088509839242369865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81949826059006559494913243 122924739088509839242369865)
    ·
      refine ⟨92193554316382379431777399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122924739088509839242369865 92193554316382379431777399)
      ·
        refine ⟨138290331474573569147666099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92193554316382379431777399 138290331474573569147666099)
        ·
          refine ⟨207435497211860353721499149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138290331474573569147666099 207435497211860353721499149)
          ·
            refine ⟨77788311454447632645562181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207435497211860353721499149 77788311454447632645562181)
            ·
              refine ⟨14585308397708931121042909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77788311454447632645562181 14585308397708931121042909)
              ·
                refine ⟨5469490649140849170391091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14585308397708931121042909 5469490649140849170391091)
                ·
                  refine ⟨8204235973711273755586637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5469490649140849170391091 8204235973711273755586637)
                  ·
                    refine ⟨3076588490141727658344989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8204235973711273755586637 3076588490141727658344989)
                    ·
                      refine ⟨1153720683803147871879371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3076588490141727658344989 1153720683803147871879371)
                      ·
                        rfl

theorem cell23_2246863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_2246863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246863 prefixEnd_2246863 := by exact prefixLift 2246863
  have htrace : WordTrace (prefixWord ++ tailWord_2246863) baseStart_2246863 baseEnd_2246863 := by
    simpa [prefixWord, tailWord_2246863, baseEnd_2246863] using wordTrace_append hprefix tailTrace_2246863
  have hstable : (prefixWord ++ tailWord_2246863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246863).length < 2 ^ (prefixWord ++ tailWord_2246863).sum := by decide
  have hdescent : baseEnd_2246863 < baseStart_2246863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246870 : List Nat := [5, 2, 1, 2, 1, 1, 2, 9]
def baseStart_2246870 : Nat := 118140960795 + 2246870 * 2 ^ 59
def prefixEnd_2246870 : Nat := 4983230072969 + 3 ^ 40 * 2246870 * 2
def baseEnd_2246870 : Nat := 42730528821027012758957

theorem tailTrace_2246870 : CollatzResearch.WordTrace tailWord_2246870 prefixEnd_2246870 42730528821027012758957 := by
  unfold tailWord_2246870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121880085623824980651129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54633387579987466460278709 5121880085623824980651129)
  ·
    refine ⟨3841410064217868735488347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5121880085623824980651129 3841410064217868735488347)
    ·
      refine ⟨5762115096326803103232521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841410064217868735488347 5762115096326803103232521)
      ·
        refine ⟨4321586322245102327424391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5762115096326803103232521 4321586322245102327424391)
        ·
          refine ⟨6482379483367653491136587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321586322245102327424391 6482379483367653491136587)
          ·
            refine ⟨9723569225051480236704881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6482379483367653491136587 9723569225051480236704881)
            ·
              refine ⟨7292676918788610177528661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9723569225051480236704881 7292676918788610177528661)
              ·
                refine ⟨42730528821027012758957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7292676918788610177528661 42730528821027012758957)
                ·
                  rfl

theorem cell23_2246870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_2246870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246870 prefixEnd_2246870 := by exact prefixLift 2246870
  have htrace : WordTrace (prefixWord ++ tailWord_2246870) baseStart_2246870 baseEnd_2246870 := by
    simpa [prefixWord, tailWord_2246870, baseEnd_2246870] using wordTrace_append hprefix tailTrace_2246870
  have hstable : (prefixWord ++ tailWord_2246870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246870).length < 2 ^ (prefixWord ++ tailWord_2246870).sum := by decide
  have hdescent : baseEnd_2246870 < baseStart_2246870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246896 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 3, 8]
def baseStart_2246896 : Nat := 118140960795 + 2246896 * 2 ^ 59
def prefixEnd_2246896 : Nat := 4983230072969 + 3 ^ 40 * 2246896 * 2
def baseEnd_2246896 : Nat := 384579209554915414255573

theorem tailTrace_2246896 : CollatzResearch.WordTrace tailWord_2246896 prefixEnd_2246896 384579209554915414255573 := by
  unfold tailWord_2246896
  simp only [CollatzResearch.WordTrace]
  refine ⟨40975514833943503065432271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54634019778591337420576361 40975514833943503065432271)
  ·
    refine ⟨61463272250915254598148407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40975514833943503065432271 61463272250915254598148407)
    ·
      refine ⟨92194908376372881897222611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61463272250915254598148407 92194908376372881897222611)
      ·
        refine ⟨138292362564559322845833917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92194908376372881897222611 138292362564559322845833917)
        ·
          refine ⟨51859635961709746067187719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138292362564559322845833917 51859635961709746067187719)
          ·
            refine ⟨77789453942564619100781579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51859635961709746067187719 77789453942564619100781579)
            ·
              refine ⟨116684180913846928651172369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77789453942564619100781579 116684180913846928651172369)
              ·
                refine ⟨87513135685385196488379277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116684180913846928651172369 87513135685385196488379277)
                ·
                  refine ⟨32817425882019448683142229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87513135685385196488379277 32817425882019448683142229)
                  ·
                    refine ⟨384579209554915414255573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32817425882019448683142229 384579209554915414255573)
                    ·
                      rfl

theorem cell23_2246896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_2246896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246896 prefixEnd_2246896 := by exact prefixLift 2246896
  have htrace : WordTrace (prefixWord ++ tailWord_2246896) baseStart_2246896 baseEnd_2246896 := by
    simpa [prefixWord, tailWord_2246896, baseEnd_2246896] using wordTrace_append hprefix tailTrace_2246896
  have hstable : (prefixWord ++ tailWord_2246896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246896).length < 2 ^ (prefixWord ++ tailWord_2246896).sum := by decide
  have hdescent : baseEnd_2246896 < baseStart_2246896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246898 : List Nat := [3, 2, 1, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2246898 : Nat := 118140960795 + 2246898 * 2 ^ 59
def prefixEnd_2246898 : Nat := 4983230072969 + 3 ^ 40 * 2246898 * 2
def baseEnd_2246898 : Nat := 1153738655626055234941711

theorem tailTrace_2246898 : CollatzResearch.WordTrace tailWord_2246898 prefixEnd_2246898 1153738655626055234941711 := by
  unfold tailWord_2246898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20487775653469940118109337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54634068409253173648291565 20487775653469940118109337)
  ·
    refine ⟨15365831740102455088582003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20487775653469940118109337 15365831740102455088582003)
    ·
      refine ⟨23048747610153682632873005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15365831740102455088582003 23048747610153682632873005)
      ·
        refine ⟨8643280353807630987327377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23048747610153682632873005 8643280353807630987327377)
        ·
          refine ⟨6482460265355723240495533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8643280353807630987327377 6482460265355723240495533)
          ·
            refine ⟨2430922599508396215185825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6482460265355723240495533 2430922599508396215185825)
            ·
              refine ⟨1823191949631297161389369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430922599508396215185825 1823191949631297161389369)
              ·
                refine ⟨1367393962223472871042027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823191949631297161389369 1367393962223472871042027)
                ·
                  refine ⟨2051090943335209306563041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367393962223472871042027 2051090943335209306563041)
                  ·
                    refine ⟨1538318207501406979922281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2051090943335209306563041 1538318207501406979922281)
                    ·
                      refine ⟨1153738655626055234941711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538318207501406979922281 1153738655626055234941711)
                      ·
                        rfl

theorem cell23_2246898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2246898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246898 prefixEnd_2246898 := by exact prefixLift 2246898
  have htrace : WordTrace (prefixWord ++ tailWord_2246898) baseStart_2246898 baseEnd_2246898 := by
    simpa [prefixWord, tailWord_2246898, baseEnd_2246898] using wordTrace_append hprefix tailTrace_2246898
  have hstable : (prefixWord ++ tailWord_2246898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246898).length < 2 ^ (prefixWord ++ tailWord_2246898).sum := by decide
  have hdescent : baseEnd_2246898 < baseStart_2246898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246913 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2246913 : Nat := 118140960795 + 2246913 * 2 ^ 59
def prefixEnd_2246913 : Nat := 4983230072969 + 3 ^ 40 * 2246913 * 2
def baseEnd_2246913 : Nat := 384582119278624225418047

theorem tailTrace_2246913 : CollatzResearch.WordTrace tailWord_2246913 prefixEnd_2246913 384582119278624225418047 := by
  unfold tailWord_2246913
  simp only [CollatzResearch.WordTrace]
  refine ⟨81951649708825418034233393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54634433139216945356155595 81951649708825418034233393)
  ·
    refine ⟨61463737281619063525675045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81951649708825418034233393 61463737281619063525675045)
    ·
      refine ⟨11524450740303574411064071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61463737281619063525675045 11524450740303574411064071)
      ·
        refine ⟨17286676110455361616596107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11524450740303574411064071 17286676110455361616596107)
        ·
          refine ⟨25930014165683042424894161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17286676110455361616596107 25930014165683042424894161)
          ·
            refine ⟨19447510624262281818670621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25930014165683042424894161 19447510624262281818670621)
            ·
              refine ⟨7292816484098355682001483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19447510624262281818670621 7292816484098355682001483)
              ·
                refine ⟨10939224726147533523002225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7292816484098355682001483 10939224726147533523002225)
                ·
                  refine ⟨8204418544610650142251669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10939224726147533523002225 8204418544610650142251669)
                  ·
                    refine ⟨384582119278624225418047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8204418544610650142251669 384582119278624225418047)
                    ·
                      rfl

theorem cell23_2246913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2246913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246913 prefixEnd_2246913 := by exact prefixLift 2246913
  have htrace : WordTrace (prefixWord ++ tailWord_2246913) baseStart_2246913 baseEnd_2246913 := by
    simpa [prefixWord, tailWord_2246913, baseEnd_2246913] using wordTrace_append hprefix tailTrace_2246913
  have hstable : (prefixWord ++ tailWord_2246913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246913).length < 2 ^ (prefixWord ++ tailWord_2246913).sum := by decide
  have hdescent : baseEnd_2246913 < baseStart_2246913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246914 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2246914 : Nat := 118140960795 + 2246914 * 2 ^ 59
def prefixEnd_2246914 : Nat := 4983230072969 + 3 ^ 40 * 2246914 * 2
def baseEnd_2246914 : Nat := 1153746871316527172341637

theorem tailTrace_2246914 : CollatzResearch.WordTrace tailWord_2246914 prefixEnd_2246914 1153746871316527172341637 := by
  unfold tailWord_2246914
  simp only [CollatzResearch.WordTrace]
  refine ⟨20487921545455448801254949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54634457454547863470013197 20487921545455448801254949)
  ·
    refine ⟨3841485289772896650235303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20487921545455448801254949 3841485289772896650235303)
    ·
      refine ⟨5762227934659344975352955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841485289772896650235303 5762227934659344975352955)
      ·
        refine ⟨8643341901989017463029433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5762227934659344975352955 8643341901989017463029433)
        ·
          refine ⟨6482506426491763097272075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8643341901989017463029433 6482506426491763097272075)
          ·
            refine ⟨9723759639737644645908113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6482506426491763097272075 9723759639737644645908113)
            ·
              refine ⟨7292819729803233484431085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9723759639737644645908113 7292819729803233484431085)
              ·
                refine ⟨2734807398676212556661657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7292819729803233484431085 2734807398676212556661657)
                ·
                  refine ⟨2051105549007159417496243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2734807398676212556661657 2051105549007159417496243)
                  ·
                    refine ⟨3076658323510739126244365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2051105549007159417496243 3076658323510739126244365)
                    ·
                      refine ⟨1153746871316527172341637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3076658323510739126244365 1153746871316527172341637)
                      ·
                        rfl

theorem cell23_2246914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2246914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246914 prefixEnd_2246914 := by exact prefixLift 2246914
  have htrace : WordTrace (prefixWord ++ tailWord_2246914) baseStart_2246914 baseEnd_2246914 := by
    simpa [prefixWord, tailWord_2246914, baseEnd_2246914] using wordTrace_append hprefix tailTrace_2246914
  have hstable : (prefixWord ++ tailWord_2246914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246914).length < 2 ^ (prefixWord ++ tailWord_2246914).sum := by decide
  have hdescent : baseEnd_2246914 < baseStart_2246914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246923 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 3]
def baseStart_2246923 : Nat := 118140960795 + 2246923 * 2 ^ 59
def prefixEnd_2246923 : Nat := 4983230072969 + 3 ^ 40 * 2246923 * 2
def baseEnd_2246923 : Nat := 1153751492642417637129095

theorem tailTrace_2246923 : CollatzResearch.WordTrace tailWord_2246923 prefixEnd_2246923 1153751492642417637129095 := by
  unfold tailWord_2246923
  simp only [CollatzResearch.WordTrace]
  refine ⟨81952014438789189742097423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54634676292526126494731615 81952014438789189742097423)
  ·
    refine ⟨122928021658183784613146135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81952014438789189742097423 122928021658183784613146135)
    ·
      refine ⟨184392032487275676919719203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122928021658183784613146135 184392032487275676919719203)
      ·
        refine ⟨276588048730913515379578805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184392032487275676919719203 276588048730913515379578805)
        ·
          refine ⟨25930129568523142066835513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 276588048730913515379578805 25930129568523142066835513)
          ·
            refine ⟨19447597176392356550126635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25930129568523142066835513 19447597176392356550126635)
            ·
              refine ⟨29171395764588534825189953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19447597176392356550126635 29171395764588534825189953)
              ·
                refine ⟨21878546823441401118892465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29171395764588534825189953 21878546823441401118892465)
                ·
                  refine ⟨16408910117581050839169349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21878546823441401118892465 16408910117581050839169349)
                  ·
                    refine ⟨3076670647046447032344253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16408910117581050839169349 3076670647046447032344253)
                    ·
                      refine ⟨1153751492642417637129095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3076670647046447032344253 1153751492642417637129095)
                      ·
                        rfl

theorem cell23_2246923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 3].length) (baseStart_2246923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246923 prefixEnd_2246923 := by exact prefixLift 2246923
  have htrace : WordTrace (prefixWord ++ tailWord_2246923) baseStart_2246923 baseEnd_2246923 := by
    simpa [prefixWord, tailWord_2246923, baseEnd_2246923] using wordTrace_append hprefix tailTrace_2246923
  have hstable : (prefixWord ++ tailWord_2246923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246923).length < 2 ^ (prefixWord ++ tailWord_2246923).sum := by decide
  have hdescent : baseEnd_2246923 < baseStart_2246923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246970 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_2246970 : Nat := 118140960795 + 2246970 * 2 ^ 59
def prefixEnd_2246970 : Nat := 4983230072969 + 3 ^ 40 * 2246970 * 2
def baseEnd_2246970 : Nat := 1153775626233178953241379

theorem tailTrace_2246970 : CollatzResearch.WordTrace tailWord_2246970 prefixEnd_2246970 1153775626233178953241379 := by
  unfold tailWord_2246970
  simp only [CollatzResearch.WordTrace]
  refine ⟨20488432167404729192264591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54635819113079277846038909 20488432167404729192264591)
  ·
    refine ⟨30732648251107093788396887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20488432167404729192264591 30732648251107093788396887)
    ·
      refine ⟨46098972376660640682595331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30732648251107093788396887 46098972376660640682595331)
      ·
        refine ⟨69148458564990961023892997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46098972376660640682595331 69148458564990961023892997)
        ·
          refine ⟨12965335980935805191979937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69148458564990961023892997 12965335980935805191979937)
          ·
            refine ⟨9724001985701853893984953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12965335980935805191979937 9724001985701853893984953)
            ·
              refine ⟨7293001489276390420488715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9724001985701853893984953 7293001489276390420488715)
              ·
                refine ⟨10939502233914585630733073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7293001489276390420488715 10939502233914585630733073)
                ·
                  refine ⟨8204626675435939223049805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10939502233914585630733073 8204626675435939223049805)
                  ·
                    refine ⟨3076735003288477208643677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8204626675435939223049805 3076735003288477208643677)
                    ·
                      refine ⟨1153775626233178953241379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3076735003288477208643677 1153775626233178953241379)
                      ·
                        rfl

theorem cell23_2246970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_2246970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246970 prefixEnd_2246970 := by exact prefixLift 2246970
  have htrace : WordTrace (prefixWord ++ tailWord_2246970) baseStart_2246970 baseEnd_2246970 := by
    simpa [prefixWord, tailWord_2246970, baseEnd_2246970] using wordTrace_append hprefix tailTrace_2246970
  have hstable : (prefixWord ++ tailWord_2246970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246970).length < 2 ^ (prefixWord ++ tailWord_2246970).sum := by decide
  have hdescent : baseEnd_2246970 < baseStart_2246970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247023 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_2247023 : Nat := 118140960795 + 2247023 * 2 ^ 59
def prefixEnd_2247023 : Nat := 4983230072969 + 3 ^ 40 * 2247023 * 2
def baseEnd_2247023 : Nat := 1153802840707867245878635

theorem tailTrace_2247023 : CollatzResearch.WordTrace tailWord_2247023 prefixEnd_2247023 1153802840707867245878635 := by
  unfold tailWord_2247023
  simp only [CollatzResearch.WordTrace]
  refine ⟨81955661738426906820737723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54637107825617937880491815 81955661738426906820737723)
  ·
    refine ⟨122933492607640360231106585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81955661738426906820737723 122933492607640360231106585)
    ·
      refine ⟨92200119455730270173329939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122933492607640360231106585 92200119455730270173329939)
      ·
        refine ⟨138300179183595405259994909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92200119455730270173329939 138300179183595405259994909)
        ·
          refine ⟨51862567193848276972498091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138300179183595405259994909 51862567193848276972498091)
          ·
            refine ⟨77793850790772415458747137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51862567193848276972498091 77793850790772415458747137)
            ·
              refine ⟨58345388093079311594060353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77793850790772415458747137 58345388093079311594060353)
              ·
                refine ⟨43759041069809483695545265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58345388093079311594060353 43759041069809483695545265)
                ·
                  refine ⟨32819280802357112771658949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43759041069809483695545265 32819280802357112771658949)
                  ·
                    refine ⟨6153615150441958644686053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32819280802357112771658949 6153615150441958644686053)
                    ·
                      refine ⟨1153802840707867245878635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6153615150441958644686053 1153802840707867245878635)
                      ·
                        rfl

theorem cell23_2247023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_2247023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247023 prefixEnd_2247023 := by exact prefixLift 2247023
  have htrace : WordTrace (prefixWord ++ tailWord_2247023) baseStart_2247023 baseEnd_2247023 := by
    simpa [prefixWord, tailWord_2247023, baseEnd_2247023] using wordTrace_append hprefix tailTrace_2247023
  have hstable : (prefixWord ++ tailWord_2247023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247023).length < 2 ^ (prefixWord ++ tailWord_2247023).sum := by decide
  have hdescent : baseEnd_2247023 < baseStart_2247023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247047 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_2247047 : Nat := 118140960795 + 2247047 * 2 ^ 59
def prefixEnd_2247047 : Nat := 4983230072969 + 3 ^ 40 * 2247047 * 2
def baseEnd_2247047 : Nat := 1153815164243575151978525

theorem tailTrace_2247047 : CollatzResearch.WordTrace tailWord_2247047 prefixEnd_2247047 1153815164243575151978525 := by
  unfold tailWord_2247047
  simp only [CollatzResearch.WordTrace]
  refine ⟨81956537090339958919611395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54637691393559972613074263 81956537090339958919611395)
  ·
    refine ⟨122934805635509938379417093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81956537090339958919611395 122934805635509938379417093)
    ·
      refine ⟨23050276056658113446140705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122934805635509938379417093 23050276056658113446140705)
      ·
        refine ⟨17287707042493585084605529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23050276056658113446140705 17287707042493585084605529)
        ·
          refine ⟨12965780281870188813454147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17287707042493585084605529 12965780281870188813454147)
          ·
            refine ⟨19448670422805283220181221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12965780281870188813454147 19448670422805283220181221)
            ·
              refine ⟨3646625704275990603783979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19448670422805283220181221 3646625704275990603783979)
              ·
                refine ⟨5469938556413985905675969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646625704275990603783979 5469938556413985905675969)
                ·
                  refine ⟨4102453917310489429256977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5469938556413985905675969 4102453917310489429256977)
                  ·
                    refine ⟨3076840437982867071942733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4102453917310489429256977 3076840437982867071942733)
                    ·
                      refine ⟨1153815164243575151978525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3076840437982867071942733 1153815164243575151978525)
                      ·
                        rfl

theorem cell23_2247047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_2247047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247047 prefixEnd_2247047 := by exact prefixLift 2247047
  have htrace : WordTrace (prefixWord ++ tailWord_2247047) baseStart_2247047 baseEnd_2247047 := by
    simpa [prefixWord, tailWord_2247047, baseEnd_2247047] using wordTrace_append hprefix tailTrace_2247047
  have hstable : (prefixWord ++ tailWord_2247047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247047).length < 2 ^ (prefixWord ++ tailWord_2247047).sum := by decide
  have hdescent : baseEnd_2247047 < baseStart_2247047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247062 : List Nat := [5, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2247062 : Nat := 118140960795 + 2247062 * 2 ^ 59
def prefixEnd_2247062 : Nat := 4983230072969 + 3 ^ 40 * 2247062 * 2
def baseEnd_2247062 : Nat := 128202540717043621476773

theorem tailTrace_2247062 : CollatzResearch.WordTrace tailWord_2247062 prefixEnd_2247062 128202540717043621476773 := by
  unfold tailWord_2247062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122317761580351030087965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54638056123523744320938293 5122317761580351030087965)
  ·
    refine ⟨1920869160592631636282987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5122317761580351030087965 1920869160592631636282987)
    ·
      refine ⟨2881303740888947454424481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920869160592631636282987 2881303740888947454424481)
      ·
        refine ⟨2160977805666710590818361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2881303740888947454424481 2160977805666710590818361)
        ·
          refine ⟨1620733354250032943113771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160977805666710590818361 1620733354250032943113771)
          ·
            refine ⟨2431100031375049414670657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620733354250032943113771 2431100031375049414670657)
            ·
              refine ⟨1823325023531287061002993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431100031375049414670657 1823325023531287061002993)
              ·
                refine ⟨1367493767648465295752245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823325023531287061002993 1367493767648465295752245)
                ·
                  refine ⟨128202540717043621476773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1367493767648465295752245 128202540717043621476773)
                  ·
                    rfl

theorem cell23_2247062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2247062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247062 prefixEnd_2247062 := by exact prefixLift 2247062
  have htrace : WordTrace (prefixWord ++ tailWord_2247062) baseStart_2247062 baseEnd_2247062 := by
    simpa [prefixWord, tailWord_2247062, baseEnd_2247062] using wordTrace_append hprefix tailTrace_2247062
  have hstable : (prefixWord ++ tailWord_2247062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247062).length < 2 ^ (prefixWord ++ tailWord_2247062).sum := by decide
  have hdescent : baseEnd_2247062 < baseStart_2247062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247077 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_2247077 : Nat := 118140960795 + 2247077 * 2 ^ 59
def prefixEnd_2247077 : Nat := 4983230072969 + 3 ^ 40 * 2247077 * 2
def baseEnd_2247077 : Nat := 1153830568663210034603387

theorem tailTrace_2247077 : CollatzResearch.WordTrace tailWord_2247077 prefixEnd_2247077 1153830568663210034603387 := by
  unfold tailWord_2247077
  simp only [CollatzResearch.WordTrace]
  refine ⟨81957631280231274043203485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54638420853487516028802323 81957631280231274043203485)
  ·
    refine ⟨30734111730086727766201307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81957631280231274043203485 30734111730086727766201307)
    ·
      refine ⟨46101167595130091649301961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30734111730086727766201307 46101167595130091649301961)
      ·
        refine ⟨34575875696347568736976471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46101167595130091649301961 34575875696347568736976471)
        ·
          refine ⟨51863813544521353105464707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34575875696347568736976471 51863813544521353105464707)
          ·
            refine ⟨77795720316782029658197061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51863813544521353105464707 77795720316782029658197061)
            ·
              refine ⟨14586697559396630560911949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77795720316782029658197061 14586697559396630560911949)
              ·
                refine ⟨5470011584773736460341981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14586697559396630560911949 5470011584773736460341981)
                ·
                  refine ⟨2051254344290151172628243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5470011584773736460341981 2051254344290151172628243)
                  ·
                    refine ⟨3076881516435226758942365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2051254344290151172628243 3076881516435226758942365)
                    ·
                      refine ⟨1153830568663210034603387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3076881516435226758942365 1153830568663210034603387)
                      ·
                        rfl

theorem cell23_2247077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_2247077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247077 prefixEnd_2247077 := by exact prefixLift 2247077
  have htrace : WordTrace (prefixWord ++ tailWord_2247077) baseStart_2247077 baseEnd_2247077 := by
    simpa [prefixWord, tailWord_2247077, baseEnd_2247077] using wordTrace_append hprefix tailTrace_2247077
  have hstable : (prefixWord ++ tailWord_2247077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247077).length < 2 ^ (prefixWord ++ tailWord_2247077).sum := by decide
  have hdescent : baseEnd_2247077 < baseStart_2247077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247105 : List Nat := [1, 2, 7, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2247105 : Nat := 118140960795 + 2247105 * 2 ^ 59
def prefixEnd_2247105 : Nat := 4983230072969 + 3 ^ 40 * 2247105 * 2
def baseEnd_2247105 : Nat := 384614982040511975017753

theorem tailTrace_2247105 : CollatzResearch.WordTrace tailWord_2247105 prefixEnd_2247105 384614982040511975017753 := by
  unfold tailWord_2247105
  simp only [CollatzResearch.WordTrace]
  refine ⟨81958652524129834825222769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54639101682753223216815179 81958652524129834825222769)
  ·
    refine ⟨61468989393097376118917077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81958652524129834825222769 61468989393097376118917077)
    ·
      refine ⟨1440679438900719752787119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 61468989393097376118917077 1440679438900719752787119)
      ·
        refine ⟨2161019158351079629180679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440679438900719752787119 2161019158351079629180679)
        ·
          refine ⟨3241528737526619443771019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161019158351079629180679 3241528737526619443771019)
          ·
            refine ⟨4862293106289929165656529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241528737526619443771019 4862293106289929165656529)
            ·
              refine ⟨3646719829717446874242397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862293106289929165656529 3646719829717446874242397)
              ·
                refine ⟨1367519936144042577840899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3646719829717446874242397 1367519936144042577840899)
                ·
                  refine ⟨2051279904216063866761349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367519936144042577840899 2051279904216063866761349)
                  ·
                    refine ⟨384614982040511975017753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2051279904216063866761349 384614982040511975017753)
                    ·
                      rfl

theorem cell23_2247105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2247105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247105 prefixEnd_2247105 := by exact prefixLift 2247105
  have htrace : WordTrace (prefixWord ++ tailWord_2247105) baseStart_2247105 baseEnd_2247105 := by
    simpa [prefixWord, tailWord_2247105, baseEnd_2247105] using wordTrace_append hprefix tailTrace_2247105
  have hstable : (prefixWord ++ tailWord_2247105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247105).length < 2 ^ (prefixWord ++ tailWord_2247105).sum := by decide
  have hdescent : baseEnd_2247105 < baseStart_2247105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247111 : List Nat := [1, 1, 4, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_2247111 : Nat := 118140960795 + 2247111 * 2 ^ 59
def prefixEnd_2247111 : Nat := 4983230072969 + 3 ^ 40 * 2247111 * 2
def baseEnd_2247111 : Nat := 1153848027005462901578231

theorem tailTrace_2247111 : CollatzResearch.WordTrace tailWord_2247111 prefixEnd_2247111 1153848027005462901578231 := by
  unfold tailWord_2247111
  simp only [CollatzResearch.WordTrace]
  refine ⟨81958871362108097849941187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54639247574738731899960791 81958871362108097849941187)
  ·
    refine ⟨122938307043162146774911781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81958871362108097849941187 122938307043162146774911781)
    ·
      refine ⟨23050932570592902520295959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122938307043162146774911781 23050932570592902520295959)
      ·
        refine ⟨34576398855889353780443939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23050932570592902520295959 34576398855889353780443939)
        ·
          refine ⟨51864598283834030670665909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34576398855889353780443939 51864598283834030670665909)
          ·
            refine ⟨4862306089109440375374929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51864598283834030670665909 4862306089109440375374929)
            ·
              refine ⟨3646729566832080281531197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862306089109440375374929 3646729566832080281531197)
              ·
                refine ⟨1367523587562030105574199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3646729566832080281531197 1367523587562030105574199)
                ·
                  refine ⟨2051285381343045158361299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367523587562030105574199 2051285381343045158361299)
                  ·
                    refine ⟨3076928072014567737541949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2051285381343045158361299 3076928072014567737541949)
                    ·
                      refine ⟨1153848027005462901578231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3076928072014567737541949 1153848027005462901578231)
                      ·
                        rfl

theorem cell23_2247111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_2247111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247111 prefixEnd_2247111 := by exact prefixLift 2247111
  have htrace : WordTrace (prefixWord ++ tailWord_2247111) baseStart_2247111 baseEnd_2247111 := by
    simpa [prefixWord, tailWord_2247111, baseEnd_2247111] using wordTrace_append hprefix tailTrace_2247111
  have hstable : (prefixWord ++ tailWord_2247111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247111).length < 2 ^ (prefixWord ++ tailWord_2247111).sum := by decide
  have hdescent : baseEnd_2247111 < baseStart_2247111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247130 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_2247130 : Nat := 118140960795 + 2247130 * 2 ^ 59
def prefixEnd_2247130 : Nat := 4983230072969 + 3 ^ 40 * 2247130 * 2
def baseEnd_2247130 : Nat := 1153857783137898327240643

theorem tailTrace_2247130 : CollatzResearch.WordTrace tailWord_2247130 prefixEnd_2247130 1153857783137898327240643 := by
  unfold tailWord_2247130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20489891087259816023720711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54639709566026176063255229 20489891087259816023720711)
  ·
    refine ⟨30734836630889724035581067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20489891087259816023720711 30734836630889724035581067)
    ·
      refine ⟨46102254946334586053371601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30734836630889724035581067 46102254946334586053371601)
      ·
        refine ⟨34576691209750939540028701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46102254946334586053371601 34576691209750939540028701)
        ·
          refine ⟨12966259203656602327510763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34576691209750939540028701 12966259203656602327510763)
          ·
            refine ⟨19449388805484903491266145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12966259203656602327510763 19449388805484903491266145)
            ·
              refine ⟨14587041604113677618449609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19449388805484903491266145 14587041604113677618449609)
              ·
                refine ⟨10940281203085258213837207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14587041604113677618449609 10940281203085258213837207)
                ·
                  refine ⟨16410421804627887320755811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10940281203085258213837207 16410421804627887320755811)
                  ·
                    refine ⟨24615632706941830981133717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16410421804627887320755811 24615632706941830981133717)
                    ·
                      refine ⟨1153857783137898327240643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24615632706941830981133717 1153857783137898327240643)
                      ·
                        rfl

theorem cell23_2247130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_2247130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247130 prefixEnd_2247130 := by exact prefixLift 2247130
  have htrace : WordTrace (prefixWord ++ tailWord_2247130) baseStart_2247130 baseEnd_2247130 := by
    simpa [prefixWord, tailWord_2247130, baseEnd_2247130] using wordTrace_append hprefix tailTrace_2247130
  have hstable : (prefixWord ++ tailWord_2247130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247130).length < 2 ^ (prefixWord ++ tailWord_2247130).sum := by decide
  have hdescent : baseEnd_2247130 < baseStart_2247130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247167 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 3]
def baseStart_2247167 : Nat := 118140960795 + 2247167 * 2 ^ 59
def prefixEnd_2247167 : Nat := 4983230072969 + 3 ^ 40 * 2247167 * 2
def baseEnd_2247167 : Nat := 1153876781922114682477973

theorem tailTrace_2247167 : CollatzResearch.WordTrace tailWord_2247167 prefixEnd_2247167 1153876781922114682477973 := by
  unfold tailWord_2247167
  simp only [CollatzResearch.WordTrace]
  refine ⟨81960913849905219413979755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54640609233270146275986503 81960913849905219413979755)
  ·
    refine ⟨122941370774857829120969633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81960913849905219413979755 122941370774857829120969633)
    ·
      refine ⟨92206028081143371840727225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122941370774857829120969633 92206028081143371840727225)
      ·
        refine ⟨69154521060857528880545419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92206028081143371840727225 69154521060857528880545419)
        ·
          refine ⟨103731781591286293320818129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69154521060857528880545419 103731781591286293320818129)
          ·
            refine ⟨77798836193464719990613597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103731781591286293320818129 77798836193464719990613597)
            ·
              refine ⟨29174563572549269996480099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77798836193464719990613597 29174563572549269996480099)
              ·
                refine ⟨43761845358823904994720149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29174563572549269996480099 43761845358823904994720149)
                ·
                  refine ⟨2051336501194870546627507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43761845358823904994720149 2051336501194870546627507)
                  ·
                    refine ⟨3077004751792305819941261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2051336501194870546627507 3077004751792305819941261)
                    ·
                      refine ⟨1153876781922114682477973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3077004751792305819941261 1153876781922114682477973)
                      ·
                        rfl

theorem cell23_2247167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_2247167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247167 prefixEnd_2247167 := by exact prefixLift 2247167
  have htrace : WordTrace (prefixWord ++ tailWord_2247167) baseStart_2247167 baseEnd_2247167 := by
    simpa [prefixWord, tailWord_2247167, baseEnd_2247167] using wordTrace_append hprefix tailTrace_2247167
  have hstable : (prefixWord ++ tailWord_2247167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247167).length < 2 ^ (prefixWord ++ tailWord_2247167).sum := by decide
  have hdescent : baseEnd_2247167 < baseStart_2247167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247224 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 1, 4, 2]
def baseStart_2247224 : Nat := 118140960795 + 2247224 * 2 ^ 59
def prefixEnd_2247224 : Nat := 4983230072969 + 3 ^ 40 * 2247224 * 2
def baseEnd_2247224 : Nat := 1153906050319420959465211

theorem tailTrace_2247224 : CollatzResearch.WordTrace tailWord_2247224 prefixEnd_2247224 1153906050319420959465211 := by
  unfold tailWord_2247224
  simp only [CollatzResearch.WordTrace]
  refine ⟨40981496405349359074402363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54641995207132478765869817 40981496405349359074402363)
  ·
    refine ⟨61472244608024038611603545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40981496405349359074402363 61472244608024038611603545)
    ·
      refine ⟨46104183456018028958702659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61472244608024038611603545 46104183456018028958702659)
      ·
        refine ⟨69156275184027043438053989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46104183456018028958702659 69156275184027043438053989)
        ·
          refine ⟨12966801597005070644635123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69156275184027043438053989 12966801597005070644635123)
          ·
            refine ⟨19450202395507605966952685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12966801597005070644635123 19450202395507605966952685)
            ·
              refine ⟨7293825898315352237607257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19450202395507605966952685 7293825898315352237607257)
              ·
                refine ⟨5470369423736514178205443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7293825898315352237607257 5470369423736514178205443)
                ·
                  refine ⟨8205554135604771267308165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5470369423736514178205443 8205554135604771267308165)
                  ·
                    refine ⟨1538541400425894612620281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8205554135604771267308165 1538541400425894612620281)
                    ·
                      refine ⟨1153906050319420959465211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538541400425894612620281 1153906050319420959465211)
                      ·
                        rfl

theorem cell23_2247224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_2247224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247224 prefixEnd_2247224 := by exact prefixLift 2247224
  have htrace : WordTrace (prefixWord ++ tailWord_2247224) baseStart_2247224 baseEnd_2247224 := by
    simpa [prefixWord, tailWord_2247224, baseEnd_2247224] using wordTrace_append hprefix tailTrace_2247224
  have hstable : (prefixWord ++ tailWord_2247224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247224).length < 2 ^ (prefixWord ++ tailWord_2247224).sum := by decide
  have hdescent : baseEnd_2247224 < baseStart_2247224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247228 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_2247228 : Nat := 118140960795 + 2247228 * 2 ^ 59
def prefixEnd_2247228 : Nat := 4983230072969 + 3 ^ 40 * 2247228 * 2
def baseEnd_2247228 : Nat := 1153908104242038943815193

theorem tailTrace_2247228 : CollatzResearch.WordTrace tailWord_2247228 prefixEnd_2247228 1153908104242038943815193 := by
  unfold tailWord_2247228
  simp only [CollatzResearch.WordTrace]
  refine ⟨40981569351342113415975169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54642092468456151221300225 40981569351342113415975169)
  ·
    refine ⟨30736177013506585061981377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40981569351342113415975169 30736177013506585061981377)
    ·
      refine ⟨23052132760129938796486033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30736177013506585061981377 23052132760129938796486033)
      ·
        refine ⟨17289099570097454097364525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23052132760129938796486033 17289099570097454097364525)
        ·
          refine ⟨6483412338786545286511697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17289099570097454097364525 6483412338786545286511697)
          ·
            refine ⟨4862559254089908964883773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6483412338786545286511697 4862559254089908964883773)
            ·
              refine ⟨1823459720283715861831415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4862559254089908964883773 1823459720283715861831415)
              ·
                refine ⟨2735189580425573792747123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823459720283715861831415 2735189580425573792747123)
                ·
                  refine ⟨4102784370638360689120685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735189580425573792747123 4102784370638360689120685)
                  ·
                    refine ⟨1538544138989385258420257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4102784370638360689120685 1538544138989385258420257)
                    ·
                      refine ⟨1153908104242038943815193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538544138989385258420257 1153908104242038943815193)
                      ·
                        rfl

theorem cell23_2247228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_2247228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247228 prefixEnd_2247228 := by exact prefixLift 2247228
  have htrace : WordTrace (prefixWord ++ tailWord_2247228) baseStart_2247228 baseEnd_2247228 := by
    simpa [prefixWord, tailWord_2247228, baseEnd_2247228] using wordTrace_append hprefix tailTrace_2247228
  have hstable : (prefixWord ++ tailWord_2247228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247228).length < 2 ^ (prefixWord ++ tailWord_2247228).sum := by decide
  have hdescent : baseEnd_2247228 < baseStart_2247228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247236 : List Nat := [2, 3, 5, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2247236 : Nat := 118140960795 + 2247236 * 2 ^ 59
def prefixEnd_2247236 : Nat := 4983230072969 + 3 ^ 40 * 2247236 * 2
def baseEnd_2247236 : Nat := 1153912212087274912515157

theorem tailTrace_2247236 : CollatzResearch.WordTrace tailWord_2247236 prefixEnd_2247236 1153912212087274912515157 := by
  unfold tailWord_2247236
  simp only [CollatzResearch.WordTrace]
  refine ⟨40981715243327622099120781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54642286991103496132161041 40981715243327622099120781)
  ·
    refine ⟨15368143216247858287170293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40981715243327622099120781 15368143216247858287170293)
    ·
      refine ⟨1440763426523236714422215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15368143216247858287170293 1440763426523236714422215)
      ·
        refine ⟨2161145139784855071633323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440763426523236714422215 2161145139784855071633323)
        ·
          refine ⟨3241717709677282607449985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161145139784855071633323 3241717709677282607449985)
          ·
            refine ⟨2431288282257961955587489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241717709677282607449985 2431288282257961955587489)
            ·
              refine ⟨1823466211693471466690617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431288282257961955587489 1823466211693471466690617)
              ·
                refine ⟨1367599658770103600017963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823466211693471466690617 1367599658770103600017963)
                ·
                  refine ⟨2051399488155155400026945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367599658770103600017963 2051399488155155400026945)
                  ·
                    refine ⟨1538549616116366550020209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2051399488155155400026945 1538549616116366550020209)
                    ·
                      refine ⟨1153912212087274912515157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538549616116366550020209 1153912212087274912515157)
                      ·
                        rfl

theorem cell23_2247236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2247236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247236 prefixEnd_2247236 := by exact prefixLift 2247236
  have htrace : WordTrace (prefixWord ++ tailWord_2247236) baseStart_2247236 baseEnd_2247236 := by
    simpa [prefixWord, tailWord_2247236, baseEnd_2247236] using wordTrace_append hprefix tailTrace_2247236
  have hstable : (prefixWord ++ tailWord_2247236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247236).length < 2 ^ (prefixWord ++ tailWord_2247236).sum := by decide
  have hdescent : baseEnd_2247236 < baseStart_2247236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247240 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2247240 : Nat := 118140960795 + 2247240 * 2 ^ 59
def prefixEnd_2247240 : Nat := 4983230072969 + 3 ^ 40 * 2247240 * 2
def baseEnd_2247240 : Nat := 1153914266009892896865137

theorem tailTrace_2247240 : CollatzResearch.WordTrace tailWord_2247240 prefixEnd_2247240 1153914266009892896865137 := by
  unfold tailWord_2247240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40981788189320376440693587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54642384252427168587591449 40981788189320376440693587)
  ·
    refine ⟨61472682283980564661040381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40981788189320376440693587 61472682283980564661040381)
    ·
      refine ⟨23052255856492711747890143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61472682283980564661040381 23052255856492711747890143)
      ·
        refine ⟨34578383784739067621835215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23052255856492711747890143 34578383784739067621835215)
        ·
          refine ⟨51867575677108601432752823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34578383784739067621835215 51867575677108601432752823)
          ·
            refine ⟨77801363515662902149129235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51867575677108601432752823 77801363515662902149129235)
            ·
              refine ⟨116702045273494353223693853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77801363515662902149129235 116702045273494353223693853)
              ·
                refine ⟨43763266977560382458885195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116702045273494353223693853 43763266977560382458885195)
                ·
                  refine ⟨65644900466340573688327793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43763266977560382458885195 65644900466340573688327793)
                  ·
                    refine ⟨49233675349755430266245845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65644900466340573688327793 49233675349755430266245845)
                    ·
                      refine ⟨1153914266009892896865137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49233675349755430266245845 1153914266009892896865137)
                      ·
                        rfl

theorem cell23_2247240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2247240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247240 prefixEnd_2247240 := by exact prefixLift 2247240
  have htrace : WordTrace (prefixWord ++ tailWord_2247240) baseStart_2247240 baseEnd_2247240 := by
    simpa [prefixWord, tailWord_2247240, baseEnd_2247240] using wordTrace_append hprefix tailTrace_2247240
  have hstable : (prefixWord ++ tailWord_2247240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247240).length < 2 ^ (prefixWord ++ tailWord_2247240).sum := by decide
  have hdescent : baseEnd_2247240 < baseStart_2247240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247314 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2247314 : Nat := 118140960795 + 2247314 * 2 ^ 59
def prefixEnd_2247314 : Nat := 4983230072969 + 3 ^ 40 * 2247314 * 2
def baseEnd_2247314 : Nat := 1153952263578325607339797

theorem tailTrace_2247314 : CollatzResearch.WordTrace tailWord_2247314 prefixEnd_2247314 1153952263578325607339797 := by
  unfold tailWord_2247314
  simp only [CollatzResearch.WordTrace]
  refine ⟨20491568845093165879895249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54644183586915109013053997 20491568845093165879895249)
  ·
    refine ⟨15368676633819874409921437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20491568845093165879895249 15368676633819874409921437)
    ·
      refine ⟨5763253737682452903720539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15368676633819874409921437 5763253737682452903720539)
      ·
        refine ⟨8644880606523679355580809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5763253737682452903720539 8644880606523679355580809)
        ·
          refine ⟨6483660454892759516685607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8644880606523679355580809 6483660454892759516685607)
          ·
            refine ⟨9725490682339139275028411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6483660454892759516685607 9725490682339139275028411)
            ·
              refine ⟨14588236023508708912542617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9725490682339139275028411 14588236023508708912542617)
              ·
                refine ⟨10941177017631531684406963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14588236023508708912542617 10941177017631531684406963)
                ·
                  refine ⟨16411765526447297526610445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10941177017631531684406963 16411765526447297526610445)
                  ·
                    refine ⟨6154412072417736572478917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16411765526447297526610445 6154412072417736572478917)
                    ·
                      refine ⟨1153952263578325607339797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6154412072417736572478917 1153952263578325607339797)
                      ·
                        rfl

theorem cell23_2247314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2247314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247314 prefixEnd_2247314 := by exact prefixLift 2247314
  have htrace : WordTrace (prefixWord ++ tailWord_2247314) baseStart_2247314 baseEnd_2247314 := by
    simpa [prefixWord, tailWord_2247314, baseEnd_2247314] using wordTrace_append hprefix tailTrace_2247314
  have hstable : (prefixWord ++ tailWord_2247314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247314).length < 2 ^ (prefixWord ++ tailWord_2247314).sum := by decide
  have hdescent : baseEnd_2247314 < baseStart_2247314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247351 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_2247351 : Nat := 118140960795 + 2247351 * 2 ^ 59
def prefixEnd_2247351 : Nat := 4983230072969 + 3 ^ 40 * 2247351 * 2
def baseEnd_2247351 : Nat := 1153971262362541962577127

theorem tailTrace_2247351 : CollatzResearch.WordTrace tailWord_2247351 prefixEnd_2247351 1153971262362541962577127 := by
  unfold tailWord_2247351
  simp only [CollatzResearch.WordTrace]
  refine ⟨81967624881238618838677907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54645083254159079225785271 81967624881238618838677907)
  ·
    refine ⟨122951437321857928258016861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81967624881238618838677907 122951437321857928258016861)
    ·
      refine ⟨46106788995696723096756323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122951437321857928258016861 46106788995696723096756323)
      ·
        refine ⟨69160183493545084645134485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46106788995696723096756323 69160183493545084645134485)
        ·
          refine ⟨3241883601259925842740679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69160183493545084645134485 3241883601259925842740679)
          ·
            refine ⟨4862825401889888764111019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241883601259925842740679 4862825401889888764111019)
            ·
              refine ⟨7294238102834833146166529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862825401889888764111019 7294238102834833146166529)
              ·
                refine ⟨5470678577126124859624897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7294238102834833146166529 5470678577126124859624897)
                ·
                  refine ⟨4103008932844593644718673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5470678577126124859624897 4103008932844593644718673)
                  ·
                    refine ⟨3077256699633445233539005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4103008932844593644718673 3077256699633445233539005)
                    ·
                      refine ⟨1153971262362541962577127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3077256699633445233539005 1153971262362541962577127)
                      ·
                        rfl

theorem cell23_2247351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_2247351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247351 prefixEnd_2247351 := by exact prefixLift 2247351
  have htrace : WordTrace (prefixWord ++ tailWord_2247351) baseStart_2247351 baseEnd_2247351 := by
    simpa [prefixWord, tailWord_2247351, baseEnd_2247351] using wordTrace_append hprefix tailTrace_2247351
  have hstable : (prefixWord ++ tailWord_2247351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247351).length < 2 ^ (prefixWord ++ tailWord_2247351).sum := by decide
  have hdescent : baseEnd_2247351 < baseStart_2247351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247384 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 3, 5]
def baseStart_2247384 : Nat := 118140960795 + 2247384 * 2 ^ 59
def prefixEnd_2247384 : Nat := 4983230072969 + 3 ^ 40 * 2247384 * 2
def baseEnd_2247384 : Nat := 384662735741380111154825

theorem tailTrace_2247384 : CollatzResearch.WordTrace tailWord_2247384 prefixEnd_2247384 384662735741380111154825 := by
  unfold tailWord_2247384
  simp only [CollatzResearch.WordTrace]
  refine ⟨40984414245059532737314603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54645885660079376983086137 40984414245059532737314603)
  ·
    refine ⟨61476621367589299105971905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40984414245059532737314603 61476621367589299105971905)
    ·
      refine ⟨46107466025691974329478929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61476621367589299105971905 46107466025691974329478929)
      ·
        refine ⟨34580599519268980747109197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46107466025691974329478929 34580599519268980747109197)
        ·
          refine ⟨12967724819725867780165949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34580599519268980747109197 12967724819725867780165949)
          ·
            refine ⟨4862896807397200417562231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12967724819725867780165949 4862896807397200417562231)
            ·
              refine ⟨7294345211095800626343347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862896807397200417562231 7294345211095800626343347)
              ·
                refine ⟨10941517816643700939515021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7294345211095800626343347 10941517816643700939515021)
                ·
                  refine ⟨4103069181241387852318133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10941517816643700939515021 4103069181241387852318133)
                  ·
                    refine ⟨384662735741380111154825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4103069181241387852318133 384662735741380111154825)
                    ·
                      rfl

theorem cell23_2247384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_2247384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247384 prefixEnd_2247384 := by exact prefixLift 2247384
  have htrace : WordTrace (prefixWord ++ tailWord_2247384) baseStart_2247384 baseEnd_2247384 := by
    simpa [prefixWord, tailWord_2247384, baseEnd_2247384] using wordTrace_append hprefix tailTrace_2247384
  have hstable : (prefixWord ++ tailWord_2247384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247384).length < 2 ^ (prefixWord ++ tailWord_2247384).sum := by decide
  have hdescent : baseEnd_2247384 < baseStart_2247384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247391 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 2, 3, 2]
def baseStart_2247391 : Nat := 118140960795 + 2247391 * 2 ^ 59
def prefixEnd_2247391 : Nat := 4983230072969 + 3 ^ 40 * 2247391 * 2
def baseEnd_2247391 : Nat := 1153991801588721806076943

theorem tailTrace_2247391 : CollatzResearch.WordTrace tailWord_2247391 prefixEnd_2247391 1153991801588721806076943 := by
  unfold tailWord_2247391
  simp only [CollatzResearch.WordTrace]
  refine ⟨81969083801093705670134027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54646055867395803780089351 81969083801093705670134027)
  ·
    refine ⟨122953625701640558505201041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81969083801093705670134027 122953625701640558505201041)
    ·
      refine ⟨92215219276230418878900781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122953625701640558505201041 92215219276230418878900781)
      ·
        refine ⟨34580707228586407079587793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92215219276230418878900781 34580707228586407079587793)
        ·
          refine ⟨25935530421439805309690845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34580707228586407079587793 25935530421439805309690845)
          ·
            refine ⟨9725823908039926991134067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25935530421439805309690845 9725823908039926991134067)
            ·
              refine ⟨14588735862059890486701101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9725823908039926991134067 14588735862059890486701101)
              ·
                refine ⟨5470775948272458932512913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14588735862059890486701101 5470775948272458932512913)
                ·
                  refine ⟨4103081961204344199384685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5470775948272458932512913 4103081961204344199384685)
                  ·
                    refine ⟨1538655735451629074769257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4103081961204344199384685 1538655735451629074769257)
                    ·
                      refine ⟨1153991801588721806076943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538655735451629074769257 1153991801588721806076943)
                      ·
                        rfl

theorem cell23_2247391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_2247391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247391 prefixEnd_2247391 := by exact prefixLift 2247391
  have htrace : WordTrace (prefixWord ++ tailWord_2247391) baseStart_2247391 baseEnd_2247391 := by
    simpa [prefixWord, tailWord_2247391, baseEnd_2247391] using wordTrace_append hprefix tailTrace_2247391
  have hstable : (prefixWord ++ tailWord_2247391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247391).length < 2 ^ (prefixWord ++ tailWord_2247391).sum := by decide
  have hdescent : baseEnd_2247391 < baseStart_2247391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247414 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2247414 : Nat := 118140960795 + 2247414 * 2 ^ 59
def prefixEnd_2247414 : Nat := 4983230072969 + 3 ^ 40 * 2247414 * 2
def baseEnd_2247414 : Nat := 384667870547925072029779

theorem tailTrace_2247414 : CollatzResearch.WordTrace tailWord_2247414 prefixEnd_2247414 384667870547925072029779 := by
  unfold tailWord_2247414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123120167500648787388831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54646615120006920398814197 5123120167500648787388831)
  ·
    refine ⟨7684680251250973181083247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5123120167500648787388831 7684680251250973181083247)
    ·
      refine ⟨11527020376876459771624871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7684680251250973181083247 11527020376876459771624871)
      ·
        refine ⟨17290530565314689657437307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11527020376876459771624871 17290530565314689657437307)
        ·
          refine ⟨25935795847972034486155961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17290530565314689657437307 25935795847972034486155961)
          ·
            refine ⟨19451846885979025864616971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25935795847972034486155961 19451846885979025864616971)
            ·
              refine ⟨29177770328968538796925457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19451846885979025864616971 29177770328968538796925457)
              ·
                refine ⟨21883327746726404097694093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29177770328968538796925457 21883327746726404097694093)
                ·
                  refine ⟨8206247905022401536635285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21883327746726404097694093 8206247905022401536635285)
                  ·
                    refine ⟨384667870547925072029779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8206247905022401536635285 384667870547925072029779)
                    ·
                      rfl

theorem cell23_2247414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2247414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247414 prefixEnd_2247414 := by exact prefixLift 2247414
  have htrace : WordTrace (prefixWord ++ tailWord_2247414) baseStart_2247414 baseEnd_2247414 := by
    simpa [prefixWord, tailWord_2247414, baseEnd_2247414] using wordTrace_append hprefix tailTrace_2247414
  have hstable : (prefixWord ++ tailWord_2247414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247414).length < 2 ^ (prefixWord ++ tailWord_2247414).sum := by decide
  have hdescent : baseEnd_2247414 < baseStart_2247414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247417 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2247417 : Nat := 118140960795 + 2247417 * 2 ^ 59
def prefixEnd_2247417 : Nat := 4983230072969 + 3 ^ 40 * 2247417 * 2
def baseEnd_2247417 : Nat := 1154005152085738704351823

theorem tailTrace_2247417 : CollatzResearch.WordTrace tailWord_2247417 prefixEnd_2247417 1154005152085738704351823 := by
  unfold tailWord_2247417
  simp only [CollatzResearch.WordTrace]
  refine ⟨81970032098999512110580505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54646688065999674740387003 81970032098999512110580505)
  ·
    refine ⟨61477524074249634082935379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81970032098999512110580505 61477524074249634082935379)
    ·
      refine ⟨92216286111374451124403069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61477524074249634082935379 92216286111374451124403069)
      ·
        refine ⟨34581107291765419171651151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92216286111374451124403069 34581107291765419171651151)
        ·
          refine ⟨51871660937648128757476727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34581107291765419171651151 51871660937648128757476727)
          ·
            refine ⟨77807491406472193136215091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51871660937648128757476727 77807491406472193136215091)
            ·
              refine ⟨116711237109708289704322637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77807491406472193136215091 116711237109708289704322637)
              ·
                refine ⟨43766713916140608639120989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116711237109708289704322637 43766713916140608639120989)
                ·
                  refine ⟨16412517718552728239670371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43766713916140608639120989 16412517718552728239670371)
                  ·
                    refine ⟨24618776577829092359505557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16412517718552728239670371 24618776577829092359505557)
                    ·
                      refine ⟨1154005152085738704351823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24618776577829092359505557 1154005152085738704351823)
                      ·
                        rfl

theorem cell23_2247417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2247417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247417 prefixEnd_2247417 := by exact prefixLift 2247417
  have htrace : WordTrace (prefixWord ++ tailWord_2247417) baseStart_2247417 baseEnd_2247417 := by
    simpa [prefixWord, tailWord_2247417, baseEnd_2247417] using wordTrace_append hprefix tailTrace_2247417
  have hstable : (prefixWord ++ tailWord_2247417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247417).length < 2 ^ (prefixWord ++ tailWord_2247417).sum := by decide
  have hdescent : baseEnd_2247417 < baseStart_2247417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247431 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 1, 6]
def baseStart_2247431 : Nat := 118140960795 + 2247431 * 2 ^ 59
def prefixEnd_2247431 : Nat := 4983230072969 + 3 ^ 40 * 2247431 * 2
def baseEnd_2247431 : Nat := 384670780271633883192253

theorem tailTrace_2247431 : CollatzResearch.WordTrace tailWord_2247431 prefixEnd_2247431 384670780271633883192253 := by
  unfold tailWord_2247431
  simp only [CollatzResearch.WordTrace]
  refine ⟨81970542720948792501590147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54647028480632528334393431 81970542720948792501590147)
  ·
    refine ⟨122955814081423188752385221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81970542720948792501590147 122955814081423188752385221)
    ·
      refine ⟨23054215140266847891072229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122955814081423188752385221 23054215140266847891072229)
      ·
        refine ⟨4322665338800033979576043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23054215140266847891072229 4322665338800033979576043)
        ·
          refine ⟨6483998008200050969364065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322665338800033979576043 6483998008200050969364065)
          ·
            refine ⟨4862998506150038227023049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6483998008200050969364065 4862998506150038227023049)
            ·
              refine ⟨3647248879612528670267287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862998506150038227023049 3647248879612528670267287)
              ·
                refine ⟨5470873319418793005400931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647248879612528670267287 5470873319418793005400931)
                ·
                  refine ⟨8206309979128189508101397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5470873319418793005400931 8206309979128189508101397)
                  ·
                    refine ⟨384670780271633883192253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8206309979128189508101397 384670780271633883192253)
                    ·
                      rfl

theorem cell23_2247431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_2247431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247431 prefixEnd_2247431 := by exact prefixLift 2247431
  have htrace : WordTrace (prefixWord ++ tailWord_2247431) baseStart_2247431 baseEnd_2247431 := by
    simpa [prefixWord, tailWord_2247431, baseEnd_2247431] using wordTrace_append hprefix tailTrace_2247431
  have hstable : (prefixWord ++ tailWord_2247431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247431).length < 2 ^ (prefixWord ++ tailWord_2247431).sum := by decide
  have hdescent : baseEnd_2247431 < baseStart_2247431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247442 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2247442 : Nat := 118140960795 + 2247442 * 2 ^ 59
def prefixEnd_2247442 : Nat := 4983230072969 + 3 ^ 40 * 2247442 * 2
def baseEnd_2247442 : Nat := 1154017989102101106539209

theorem tailTrace_2247442 : CollatzResearch.WordTrace tailWord_2247442 prefixEnd_2247442 1154017989102101106539209 := by
  unfold tailWord_2247442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20492735980977235345060145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54647295949272627586827053 20492735980977235345060145)
  ·
    refine ⟨15369551985732926508795109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20492735980977235345060145 15369551985732926508795109)
    ·
      refine ⟨2881790997324923720399083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15369551985732926508795109 2881790997324923720399083)
      ·
        refine ⟨4322686495987385580598625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881790997324923720399083 4322686495987385580598625)
        ·
          refine ⟨3242014871990539185448969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4322686495987385580598625 3242014871990539185448969)
          ·
            refine ⟨2431511153992904389086727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3242014871990539185448969 2431511153992904389086727)
            ·
              refine ⟨3647266730989356583630091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431511153992904389086727 3647266730989356583630091)
              ·
                refine ⟨5470900096484034875445137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647266730989356583630091 5470900096484034875445137)
                ·
                  refine ⟨4103175072363026156583853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5470900096484034875445137 4103175072363026156583853)
                  ·
                    refine ⟨1538690652136134808718945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4103175072363026156583853 1538690652136134808718945)
                    ·
                      refine ⟨1154017989102101106539209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538690652136134808718945 1154017989102101106539209)
                      ·
                        rfl

theorem cell23_2247442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2247442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247442 prefixEnd_2247442 := by exact prefixLift 2247442
  have htrace : WordTrace (prefixWord ++ tailWord_2247442) baseStart_2247442 baseEnd_2247442 := by
    simpa [prefixWord, tailWord_2247442, baseEnd_2247442] using wordTrace_append hprefix tailTrace_2247442
  have hstable : (prefixWord ++ tailWord_2247442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247442).length < 2 ^ (prefixWord ++ tailWord_2247442).sum := by decide
  have hdescent : baseEnd_2247442 < baseStart_2247442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247455 : List Nat := [1, 1, 2, 4, 2, 2, 1, 5, 1, 2, 2]
def baseStart_2247455 : Nat := 118140960795 + 2247455 * 2 ^ 59
def prefixEnd_2247455 : Nat := 4983230072969 + 3 ^ 40 * 2247455 * 2
def baseEnd_2247455 : Nat := 1154024664350609555676649

theorem tailTrace_2247455 : CollatzResearch.WordTrace tailWord_2247455 prefixEnd_2247455 1154024664350609555676649 := by
  unfold tailWord_2247455
  simp only [CollatzResearch.WordTrace]
  refine ⟨81971418072861844600463819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54647612048574563066975879 81971418072861844600463819)
  ·
    refine ⟨122957127109292766900695729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81971418072861844600463819 122957127109292766900695729)
    ·
      refine ⟨92217845331969575175521797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122957127109292766900695729 92217845331969575175521797)
      ·
        refine ⟨17290845999744295345410337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92217845331969575175521797 17290845999744295345410337)
        ·
          refine ⟨12968134499808221509057753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17290845999744295345410337 12968134499808221509057753)
          ·
            refine ⟨9726100874856166131793315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12968134499808221509057753 9726100874856166131793315)
            ·
              refine ⟨14589151312284249197689973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9726100874856166131793315 14589151312284249197689973)
              ·
                refine ⟨1367732935526648362283435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14589151312284249197689973 1367732935526648362283435)
                ·
                  refine ⟨2051599403289972543425153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367732935526648362283435 2051599403289972543425153)
                  ·
                    refine ⟨1538699552467479407568865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2051599403289972543425153 1538699552467479407568865)
                    ·
                      refine ⟨1154024664350609555676649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538699552467479407568865 1154024664350609555676649)
                      ·
                        rfl

theorem cell23_2247455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_2247455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247455 prefixEnd_2247455 := by exact prefixLift 2247455
  have htrace : WordTrace (prefixWord ++ tailWord_2247455) baseStart_2247455 baseEnd_2247455 := by
    simpa [prefixWord, tailWord_2247455, baseEnd_2247455] using wordTrace_append hprefix tailTrace_2247455
  have hstable : (prefixWord ++ tailWord_2247455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247455).length < 2 ^ (prefixWord ++ tailWord_2247455).sum := by decide
  have hdescent : baseEnd_2247455 < baseStart_2247455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247458 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2247458 : Nat := 118140960795 + 2247458 * 2 ^ 59
def prefixEnd_2247458 : Nat := 4983230072969 + 3 ^ 40 * 2247458 * 2
def baseEnd_2247458 : Nat := 1154026204792573043939135

theorem tailTrace_2247458 : CollatzResearch.WordTrace tailWord_2247458 prefixEnd_2247458 1154026204792573043939135 := by
  unfold tailWord_2247458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20492881872962744028205757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54647684994567317408548685 20492881872962744028205757)
  ·
    refine ⟨7684830702361029010577159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20492881872962744028205757 7684830702361029010577159)
    ·
      refine ⟨11527246053541543515865739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7684830702361029010577159 11527246053541543515865739)
      ·
        refine ⟨17290869080312315273798609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11527246053541543515865739 17290869080312315273798609)
        ·
          refine ⟨12968151810234236455348957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17290869080312315273798609 12968151810234236455348957)
          ·
            refine ⟨4863056928837838670755859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12968151810234236455348957 4863056928837838670755859)
            ·
              refine ⟨7294585393256758006133789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863056928837838670755859 7294585393256758006133789)
              ·
                refine ⟨2735469522471284252300171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7294585393256758006133789 2735469522471284252300171)
                ·
                  refine ⟨4103204283706926378450257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735469522471284252300171 4103204283706926378450257)
                  ·
                    refine ⟨3077403212780194783837693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4103204283706926378450257 3077403212780194783837693)
                    ·
                      refine ⟨1154026204792573043939135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3077403212780194783837693 1154026204792573043939135)
                      ·
                        rfl

theorem cell23_2247458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2247458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247458 prefixEnd_2247458 := by exact prefixLift 2247458
  have htrace : WordTrace (prefixWord ++ tailWord_2247458) baseStart_2247458 baseEnd_2247458 := by
    simpa [prefixWord, tailWord_2247458, baseEnd_2247458] using wordTrace_append hprefix tailTrace_2247458
  have hstable : (prefixWord ++ tailWord_2247458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247458).length < 2 ^ (prefixWord ++ tailWord_2247458).sum := by decide
  have hdescent : baseEnd_2247458 < baseStart_2247458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247485 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_2247485 : Nat := 118140960795 + 2247485 * 2 ^ 59
def prefixEnd_2247485 : Nat := 4983230072969 + 3 ^ 40 * 2247485 * 2
def baseEnd_2247485 : Nat := 1154040068770244438301511

theorem tailTrace_2247485 : CollatzResearch.WordTrace tailWord_2247485 prefixEnd_2247485 1154040068770244438301511 := by
  unfold tailWord_2247485
  simp only [CollatzResearch.WordTrace]
  refine ⟨81972512262753159724055909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54648341508502106482703939 81972512262753159724055909)
  ·
    refine ⟨15369846049266217448260483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81972512262753159724055909 15369846049266217448260483)
    ·
      refine ⟨23054769073899326172390725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15369846049266217448260483 23054769073899326172390725)
      ·
        refine ⟨4322769201356123657323261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23054769073899326172390725 4322769201356123657323261)
        ·
          refine ⟨1621038450508546371496223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4322769201356123657323261 1621038450508546371496223)
          ·
            refine ⟨2431557675762819557244335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621038450508546371496223 2431557675762819557244335)
            ·
              refine ⟨3647336513644229335866503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431557675762819557244335 3647336513644229335866503)
              ·
                refine ⟨5471004770466344003799755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647336513644229335866503 5471004770466344003799755)
                ·
                  refine ⟨8206507155699516005699633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471004770466344003799755 8206507155699516005699633)
                  ·
                    refine ⟨6154880366774637004274725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8206507155699516005699633 6154880366774637004274725)
                    ·
                      refine ⟨1154040068770244438301511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6154880366774637004274725 1154040068770244438301511)
                      ·
                        rfl

theorem cell23_2247485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_2247485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247485 prefixEnd_2247485 := by exact prefixLift 2247485
  have htrace : WordTrace (prefixWord ++ tailWord_2247485) baseStart_2247485 baseEnd_2247485 := by
    simpa [prefixWord, tailWord_2247485, baseEnd_2247485] using wordTrace_append hprefix tailTrace_2247485
  have hstable : (prefixWord ++ tailWord_2247485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247485).length < 2 ^ (prefixWord ++ tailWord_2247485).sum := by decide
  have hdescent : baseEnd_2247485 < baseStart_2247485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247492 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2247492 : Nat := 118140960795 + 2247492 * 2 ^ 59
def prefixEnd_2247492 : Nat := 4983230072969 + 3 ^ 40 * 2247492 * 2
def baseEnd_2247492 : Nat := 1154043663134825910913979

theorem tailTrace_2247492 : CollatzResearch.WordTrace tailWord_2247492 prefixEnd_2247492 1154043663134825910913979 := by
  unfold tailWord_2247492
  simp only [CollatzResearch.WordTrace]
  refine ⟨40986383786863899959780365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54648511715818533279707153 40986383786863899959780365)
  ·
    refine ⟨15369893920073962484917637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40986383786863899959780365 15369893920073962484917637)
    ·
      refine ⟨2881855110013867965922057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15369893920073962484917637 2881855110013867965922057)
      ·
        refine ⟨2161391332510400974441543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2881855110013867965922057 2161391332510400974441543)
        ·
          refine ⟨3242086998765601461662315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161391332510400974441543 3242086998765601461662315)
          ·
            refine ⟨4863130498148402192493473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3242086998765601461662315 4863130498148402192493473)
            ·
              refine ⟨3647347873611301644370105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4863130498148402192493473 3647347873611301644370105)
              ·
                refine ⟨2735510905208476233277579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3647347873611301644370105 2735510905208476233277579)
                ·
                  refine ⟨4103266357812714349916369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735510905208476233277579 4103266357812714349916369)
                  ·
                    refine ⟨3077449768359535762437277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4103266357812714349916369 3077449768359535762437277)
                    ·
                      refine ⟨1154043663134825910913979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3077449768359535762437277 1154043663134825910913979)
                      ·
                        rfl

theorem cell23_2247492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2247492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247492 prefixEnd_2247492 := by exact prefixLift 2247492
  have htrace : WordTrace (prefixWord ++ tailWord_2247492) baseStart_2247492 baseEnd_2247492 := by
    simpa [prefixWord, tailWord_2247492, baseEnd_2247492] using wordTrace_append hprefix tailTrace_2247492
  have hstable : (prefixWord ++ tailWord_2247492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247492).length < 2 ^ (prefixWord ++ tailWord_2247492).sum := by decide
  have hdescent : baseEnd_2247492 < baseStart_2247492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247514 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_2247514 : Nat := 118140960795 + 2247514 * 2 ^ 59
def prefixEnd_2247514 : Nat := 4983230072969 + 3 ^ 40 * 2247514 * 2
def baseEnd_2247514 : Nat := 1154054959709224824838877

theorem tailTrace_2247514 : CollatzResearch.WordTrace tailWord_2247514 prefixEnd_2247514 1154054959709224824838877 := by
  unfold tailWord_2247514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20493392494912024419215399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54649046653098731784574397 20493392494912024419215399)
  ·
    refine ⟨30740088742368036628823099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20493392494912024419215399 30740088742368036628823099)
    ·
      refine ⟨46110133113552054943234649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30740088742368036628823099 46110133113552054943234649)
      ·
        refine ⟨34582599835164041207425987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46110133113552054943234649 34582599835164041207425987)
        ·
          refine ⟨51873899752746061811138981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34582599835164041207425987 51873899752746061811138981)
          ·
            refine ⟨9726356203639886589588559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51873899752746061811138981 9726356203639886589588559)
            ·
              refine ⟨14589534305459829884382839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9726356203639886589588559 14589534305459829884382839)
              ·
                refine ⟨21884301458189744826574259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14589534305459829884382839 21884301458189744826574259)
                ·
                  refine ⟨32826452187284617239861389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21884301458189744826574259 32826452187284617239861389)
                  ·
                    refine ⟨12309919570231731464948021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32826452187284617239861389 12309919570231731464948021)
                    ·
                      refine ⟨1154054959709224824838877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12309919570231731464948021 1154054959709224824838877)
                      ·
                        rfl

theorem cell23_2247514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_2247514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247514 prefixEnd_2247514 := by exact prefixLift 2247514
  have htrace : WordTrace (prefixWord ++ tailWord_2247514) baseStart_2247514 baseEnd_2247514 := by
    simpa [prefixWord, tailWord_2247514, baseEnd_2247514] using wordTrace_append hprefix tailTrace_2247514
  have hstable : (prefixWord ++ tailWord_2247514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247514).length < 2 ^ (prefixWord ++ tailWord_2247514).sum := by decide
  have hdescent : baseEnd_2247514 < baseStart_2247514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247545 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 2, 2, 2]
def baseStart_2247545 : Nat := 118140960795 + 2247545 * 2 ^ 59
def prefixEnd_2247545 : Nat := 4983230072969 + 3 ^ 40 * 2247545 * 2
def baseEnd_2247545 : Nat := 1154070877609514203551235

theorem tailTrace_2247545 : CollatzResearch.WordTrace tailWord_2247545 prefixEnd_2247545 1154070877609514203551235 := by
  unfold tailWord_2247545
  simp only [CollatzResearch.WordTrace]
  refine ⟨81974700642535789971240089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54649800428357193314160059 81974700642535789971240089)
  ·
    refine ⟨61481025481901842478430067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81974700642535789971240089 61481025481901842478430067)
    ·
      refine ⟨92221538222852763717645101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61481025481901842478430067 92221538222852763717645101)
      ·
        refine ⟨34583076833569786394116913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92221538222852763717645101 34583076833569786394116913)
        ·
          refine ⟨25937307625177339795587685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34583076833569786394116913 25937307625177339795587685)
          ·
            refine ⟨4863245179720751211672691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25937307625177339795587685 4863245179720751211672691)
            ·
              refine ⟨7294867769581126817509037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863245179720751211672691 7294867769581126817509037)
              ·
                refine ⟨2735575413592922556565889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7294867769581126817509037 2735575413592922556565889)
                ·
                  refine ⟨2051681560194691917424417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735575413592922556565889 2051681560194691917424417)
                  ·
                    refine ⟨1538761170146018938068313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2051681560194691917424417 1538761170146018938068313)
                    ·
                      refine ⟨1154070877609514203551235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538761170146018938068313 1154070877609514203551235)
                      ·
                        rfl

theorem cell23_2247545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_2247545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247545 prefixEnd_2247545 := by exact prefixLift 2247545
  have htrace : WordTrace (prefixWord ++ tailWord_2247545) baseStart_2247545 baseEnd_2247545 := by
    simpa [prefixWord, tailWord_2247545, baseEnd_2247545] using wordTrace_append hprefix tailTrace_2247545
  have hstable : (prefixWord ++ tailWord_2247545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247545).length < 2 ^ (prefixWord ++ tailWord_2247545).sum := by decide
  have hdescent : baseEnd_2247545 < baseStart_2247545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247564 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_2247564 : Nat := 118140960795 + 2247564 * 2 ^ 59
def prefixEnd_2247564 : Nat := 4983230072969 + 3 ^ 40 * 2247564 * 2
def baseEnd_2247564 : Nat := 384693544580649876404549

theorem tailTrace_2247564 : CollatzResearch.WordTrace tailWord_2247564 prefixEnd_2247564 384693544580649876404549 := by
  unfold tailWord_2247564
  simp only [CollatzResearch.WordTrace]
  refine ⟨40987696814733478108090873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54650262419644637477454497 40987696814733478108090873)
  ·
    refine ⟨30740772611050108581068155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40987696814733478108090873 30740772611050108581068155)
    ·
      refine ⟨46111158916575162871602233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30740772611050108581068155 46111158916575162871602233)
      ·
        refine ⟨34583369187431372153701675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46111158916575162871602233 34583369187431372153701675)
        ·
          refine ⟨51875053781147058230552513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34583369187431372153701675 51875053781147058230552513)
          ·
            refine ⟨38906290335860293672914385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51875053781147058230552513 38906290335860293672914385)
            ·
              refine ⟨29179717751895220254685789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38906290335860293672914385 29179717751895220254685789)
              ·
                refine ⟨10942394156960707595507171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29179717751895220254685789 10942394156960707595507171)
                ·
                  refine ⟨16413591235441061393260757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10942394156960707595507171 16413591235441061393260757)
                  ·
                    refine ⟨384693544580649876404549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16413591235441061393260757 384693544580649876404549)
                    ·
                      rfl

theorem cell23_2247564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_2247564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247564 prefixEnd_2247564 := by exact prefixLift 2247564
  have htrace : WordTrace (prefixWord ++ tailWord_2247564) baseStart_2247564 baseEnd_2247564 := by
    simpa [prefixWord, tailWord_2247564, baseEnd_2247564] using wordTrace_append hprefix tailTrace_2247564
  have hstable : (prefixWord ++ tailWord_2247564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247564).length < 2 ^ (prefixWord ++ tailWord_2247564).sum := by decide
  have hdescent : baseEnd_2247564 < baseStart_2247564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247581 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2247581 : Nat := 118140960795 + 2247581 * 2 ^ 59
def prefixEnd_2247581 : Nat := 4983230072969 + 3 ^ 40 * 2247581 * 2
def baseEnd_2247581 : Nat := 384696454304358687567023

theorem tailTrace_2247581 : CollatzResearch.WordTrace tailWord_2247581 prefixEnd_2247581 384696454304358687567023 := by
  unfold tailWord_2247581
  simp only [CollatzResearch.WordTrace]
  refine ⟨81976013670405368119550597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54650675780270245413033731 81976013670405368119550597)
  ·
    refine ⟨15370502563201006522415737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81976013670405368119550597 15370502563201006522415737)
    ·
      refine ⟨11527876922400754891811803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15370502563201006522415737 11527876922400754891811803)
      ·
        refine ⟨17291815383601132337717705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11527876922400754891811803 17291815383601132337717705)
        ·
          refine ⟨12968861537700849253288279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17291815383601132337717705 12968861537700849253288279)
          ·
            refine ⟨19453292306551273879932419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12968861537700849253288279 19453292306551273879932419)
            ·
              refine ⟨29179938459826910819898629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19453292306551273879932419 29179938459826910819898629)
              ·
                refine ⟨5471238461217545778730993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29179938459826910819898629 5471238461217545778730993)
                ·
                  refine ⟨4103428845913159334048245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5471238461217545778730993 4103428845913159334048245)
                  ·
                    refine ⟨384696454304358687567023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4103428845913159334048245 384696454304358687567023)
                    ·
                      rfl

theorem cell23_2247581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2247581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247581 prefixEnd_2247581 := by exact prefixLift 2247581
  have htrace : WordTrace (prefixWord ++ tailWord_2247581) baseStart_2247581 baseEnd_2247581 := by
    simpa [prefixWord, tailWord_2247581, baseEnd_2247581] using wordTrace_append hprefix tailTrace_2247581
  have hstable : (prefixWord ++ tailWord_2247581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247581).length < 2 ^ (prefixWord ++ tailWord_2247581).sum := by decide
  have hdescent : baseEnd_2247581 < baseStart_2247581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247585 : List Nat := [1, 2, 3, 4, 1, 1, 4, 2, 5]
def baseStart_2247585 : Nat := 118140960795 + 2247585 * 2 ^ 59
def prefixEnd_2247585 : Nat := 4983230072969 + 3 ^ 40 * 2247585 * 2
def baseEnd_2247585 : Nat := 128232379648410449672339

theorem tailTrace_2247585 : CollatzResearch.WordTrace tailWord_2247585 prefixEnd_2247585 128232379648410449672339 := by
  unfold tailWord_2247585
  simp only [CollatzResearch.WordTrace]
  refine ⟨81976159562390876802696209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54650773041593917868464139 81976159562390876802696209)
  ·
    refine ⟨61482119671793157602022157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81976159562390876802696209 61482119671793157602022157)
    ·
      refine ⟨23055794876922434100758309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61482119671793157602022157 23055794876922434100758309)
      ·
        refine ⟨4322961539422956393892183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23055794876922434100758309 4322961539422956393892183)
        ·
          refine ⟨6484442309134434590838275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322961539422956393892183 6484442309134434590838275)
          ·
            refine ⟨9726663463701651886257413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6484442309134434590838275 9726663463701651886257413)
            ·
              refine ⟨1823749399444059728673265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9726663463701651886257413 1823749399444059728673265)
              ·
                refine ⟨1367812049583044796504949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823749399444059728673265 1367812049583044796504949)
                ·
                  refine ⟨128232379648410449672339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1367812049583044796504949 128232379648410449672339)
                  ·
                    rfl

theorem cell23_2247585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 5].length) (baseStart_2247585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247585 prefixEnd_2247585 := by exact prefixLift 2247585
  have htrace : WordTrace (prefixWord ++ tailWord_2247585) baseStart_2247585 baseEnd_2247585 := by
    simpa [prefixWord, tailWord_2247585, baseEnd_2247585] using wordTrace_append hprefix tailTrace_2247585
  have hstable : (prefixWord ++ tailWord_2247585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247585).length < 2 ^ (prefixWord ++ tailWord_2247585).sum := by decide
  have hdescent : baseEnd_2247585 < baseStart_2247585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247641 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 8]
def baseStart_2247641 : Nat := 118140960795 + 2247641 * 2 ^ 59
def prefixEnd_2247641 : Nat := 4983230072969 + 3 ^ 40 * 2247641 * 2
def baseEnd_2247641 : Nat := 128235574639149536438977

theorem tailTrace_2247641 : CollatzResearch.WordTrace tailWord_2247641 prefixEnd_2247641 128235574639149536438977 := by
  unfold tailWord_2247641
  simp only [CollatzResearch.WordTrace]
  refine ⟨81978202050187998366734777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54652134700125332244489851 81978202050187998366734777)
  ·
    refine ⟨61483651537640998775051083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81978202050187998366734777 61483651537640998775051083)
    ·
      refine ⟨92225477306461498162576625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61483651537640998775051083 92225477306461498162576625)
      ·
        refine ⟨69169107979846123621932469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92225477306461498162576625 69169107979846123621932469)
        ·
          refine ⟨6484603873110574089556169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69169107979846123621932469 6484603873110574089556169)
          ·
            refine ⟨4863452904832930567167127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6484603873110574089556169 4863452904832930567167127)
            ·
              refine ⟨7295179357249395850750691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863452904832930567167127 7295179357249395850750691)
              ·
                refine ⟨10942769035874093776126037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295179357249395850750691 10942769035874093776126037)
                ·
                  refine ⟨128235574639149536438977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10942769035874093776126037 128235574639149536438977)
                  ·
                    rfl

theorem cell23_2247641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_2247641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247641 prefixEnd_2247641 := by exact prefixLift 2247641
  have htrace : WordTrace (prefixWord ++ tailWord_2247641) baseStart_2247641 baseEnd_2247641 := by
    simpa [prefixWord, tailWord_2247641, baseEnd_2247641] using wordTrace_append hprefix tailTrace_2247641
  have hstable : (prefixWord ++ tailWord_2247641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247641).length < 2 ^ (prefixWord ++ tailWord_2247641).sum := by decide
  have hdescent : baseEnd_2247641 < baseStart_2247641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247645 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2247645 : Nat := 118140960795 + 2247645 * 2 ^ 59
def prefixEnd_2247645 : Nat := 4983230072969 + 3 ^ 40 * 2247645 * 2
def baseEnd_2247645 : Nat := 384707408558321270766925

theorem tailTrace_2247645 : CollatzResearch.WordTrace tailWord_2247645 prefixEnd_2247645 384707408558321270766925 := by
  unfold tailWord_2247645
  simp only [CollatzResearch.WordTrace]
  refine ⟨81978347942173507049880389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54652231961449004699920259 81978347942173507049880389)
  ·
    refine ⟨15370940239157532571852573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81978347942173507049880389 15370940239157532571852573)
    ·
      refine ⟨5764102589684074714444715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15370940239157532571852573 5764102589684074714444715)
      ·
        refine ⟨8646153884526112071667073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5764102589684074714444715 8646153884526112071667073)
        ·
          refine ⟨6484615413394584053750305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8646153884526112071667073 6484615413394584053750305)
          ·
            refine ⟨4863461560045938040312729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6484615413394584053750305 4863461560045938040312729)
            ·
              refine ⟨3647596170034453530234547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4863461560045938040312729 3647596170034453530234547)
              ·
                refine ⟨5471394255051680295351821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647596170034453530234547 5471394255051680295351821)
                ·
                  refine ⟨2051772845644380110756933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5471394255051680295351821 2051772845644380110756933)
                  ·
                    refine ⟨384707408558321270766925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2051772845644380110756933 384707408558321270766925)
                    ·
                      rfl

theorem cell23_2247645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2247645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247645 prefixEnd_2247645 := by exact prefixLift 2247645
  have htrace : WordTrace (prefixWord ++ tailWord_2247645) baseStart_2247645 baseEnd_2247645 := by
    simpa [prefixWord, tailWord_2247645, baseEnd_2247645] using wordTrace_append hprefix tailTrace_2247645
  have hstable : (prefixWord ++ tailWord_2247645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247645).length < 2 ^ (prefixWord ++ tailWord_2247645).sum := by decide
  have hdescent : baseEnd_2247645 < baseStart_2247645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247688 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 1, 5]
def baseStart_2247688 : Nat := 118140960795 + 2247688 * 2 ^ 59
def prefixEnd_2247688 : Nat := 4983230072969 + 3 ^ 40 * 2247688 * 2
def baseEnd_2247688 : Nat := 384714768447702381354359

theorem tailTrace_2247688 : CollatzResearch.WordTrace tailWord_2247688 prefixEnd_2247688 384714768447702381354359 := by
  unfold tailWord_2247688
  simp only [CollatzResearch.WordTrace]
  refine ⟨40989958140508862696847859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54653277520678483595797145 40989958140508862696847859)
  ·
    refine ⟨61484937210763294045271789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40989958140508862696847859 61484937210763294045271789)
    ·
      refine ⟨23056851454036235266976921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61484937210763294045271789 23056851454036235266976921)
      ·
        refine ⟨17292638590527176450232691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23056851454036235266976921 17292638590527176450232691)
        ·
          refine ⟨25938957885790764675349037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17292638590527176450232691 25938957885790764675349037)
          ·
            refine ⟨9727109207171536753255889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25938957885790764675349037 9727109207171536753255889)
            ·
              refine ⟨7295331905378652564941917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9727109207171536753255889 7295331905378652564941917)
              ·
                refine ⟨2735749464516994711853219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7295331905378652564941917 2735749464516994711853219)
                ·
                  refine ⟨4103624196775492067779829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735749464516994711853219 4103624196775492067779829)
                  ·
                    refine ⟨384714768447702381354359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4103624196775492067779829 384714768447702381354359)
                    ·
                      rfl

theorem cell23_2247688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_2247688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247688 prefixEnd_2247688 := by exact prefixLift 2247688
  have htrace : WordTrace (prefixWord ++ tailWord_2247688) baseStart_2247688 baseEnd_2247688 := by
    simpa [prefixWord, tailWord_2247688, baseEnd_2247688] using wordTrace_append hprefix tailTrace_2247688
  have hstable : (prefixWord ++ tailWord_2247688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247688).length < 2 ^ (prefixWord ++ tailWord_2247688).sum := by decide
  have hdescent : baseEnd_2247688 < baseStart_2247688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247722 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2247722 : Nat := 118140960795 + 2247722 * 2 ^ 59
def prefixEnd_2247722 : Nat := 4983230072969 + 3 ^ 40 * 2247722 * 2
def baseEnd_2247722 : Nat := 384720587895120003679307

theorem tailTrace_2247722 : CollatzResearch.WordTrace tailWord_2247722 prefixEnd_2247722 384720587895120003679307 := by
  unfold tailWord_2247722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20495289090723637300108355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54654104241929699466955613 20495289090723637300108355)
  ·
    refine ⟨30742933636085455950162533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20495289090723637300108355 30742933636085455950162533)
    ·
      refine ⟨5764300056766022990655475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30742933636085455950162533 5764300056766022990655475)
      ·
        refine ⟨8646450085149034485983213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5764300056766022990655475 8646450085149034485983213)
        ·
          refine ⟨3242418781930887932243705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8646450085149034485983213 3242418781930887932243705)
          ·
            refine ⟨2431814086448165949182779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3242418781930887932243705 2431814086448165949182779)
            ·
              refine ⟨3647721129672248923774169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431814086448165949182779 3647721129672248923774169)
              ·
                refine ⟨2735790847254186692830627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3647721129672248923774169 2735790847254186692830627)
                ·
                  refine ⟨4103686270881280039245941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735790847254186692830627 4103686270881280039245941)
                  ·
                    refine ⟨384720587895120003679307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4103686270881280039245941 384720587895120003679307)
                    ·
                      rfl

theorem cell23_2247722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2247722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247722 prefixEnd_2247722 := by exact prefixLift 2247722
  have htrace : WordTrace (prefixWord ++ tailWord_2247722) baseStart_2247722 baseEnd_2247722 := by
    simpa [prefixWord, tailWord_2247722, baseEnd_2247722] using wordTrace_append hprefix tailTrace_2247722
  have hstable : (prefixWord ++ tailWord_2247722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247722).length < 2 ^ (prefixWord ++ tailWord_2247722).sum := by decide
  have hdescent : baseEnd_2247722 < baseStart_2247722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247728 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3]
def baseStart_2247728 : Nat := 118140960795 + 2247728 * 2 ^ 59
def prefixEnd_2247728 : Nat := 4983230072969 + 3 ^ 40 * 2247728 * 2
def baseEnd_2247728 : Nat := 1154164844569286987562893

theorem tailTrace_2247728 : CollatzResearch.WordTrace tailWord_2247728 prefixEnd_2247728 1154164844569286987562893 := by
  unfold tailWord_2247728
  simp only [CollatzResearch.WordTrace]
  refine ⟨40990687600436406112575919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54654250133915208150101225 40990687600436406112575919)
  ·
    refine ⟨61486031400654609168863879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40990687600436406112575919 61486031400654609168863879)
    ·
      refine ⟨92229047100981913753295819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61486031400654609168863879 92229047100981913753295819)
      ·
        refine ⟨138343570651472870629943729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92229047100981913753295819 138343570651472870629943729)
        ·
          refine ⟨103757677988604652972457797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138343570651472870629943729 103757677988604652972457797)
          ·
            refine ⟨19454564622863372432335837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103757677988604652972457797 19454564622863372432335837)
            ·
              refine ⟨7295461733573764662125939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19454564622863372432335837 7295461733573764662125939)
              ·
                refine ⟨10943192600360646993188909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295461733573764662125939 10943192600360646993188909)
                ·
                  refine ⟨4103697225135242622445841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10943192600360646993188909 4103697225135242622445841)
                  ·
                    refine ⟨3077772918851431966834381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4103697225135242622445841 3077772918851431966834381)
                    ·
                      refine ⟨1154164844569286987562893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3077772918851431966834381 1154164844569286987562893)
                      ·
                        rfl

theorem cell23_2247728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_2247728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247728 prefixEnd_2247728 := by exact prefixLift 2247728
  have htrace : WordTrace (prefixWord ++ tailWord_2247728) baseStart_2247728 baseEnd_2247728 := by
    simpa [prefixWord, tailWord_2247728, baseEnd_2247728] using wordTrace_append hprefix tailTrace_2247728
  have hstable : (prefixWord ++ tailWord_2247728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247728).length < 2 ^ (prefixWord ++ tailWord_2247728).sum := by decide
  have hdescent : baseEnd_2247728 < baseStart_2247728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247758 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_2247758 : Nat := 118140960795 + 2247758 * 2 ^ 59
def prefixEnd_2247758 : Nat := 4983230072969 + 3 ^ 40 * 2247758 * 2
def baseEnd_2247758 : Nat := 1154180248988921870187755

theorem tailTrace_2247758 : CollatzResearch.WordTrace tailWord_2247758 prefixEnd_2247758 1154180248988921870187755 := by
  unfold tailWord_2247758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10247808673845515918592991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54654979593842751565829285 10247808673845515918592991)
  ·
    refine ⟨15371713010768273877889487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10247808673845515918592991 15371713010768273877889487)
    ·
      refine ⟨23057569516152410816834231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15371713010768273877889487 23057569516152410816834231)
      ·
        refine ⟨34586354274228616225251347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23057569516152410816834231 34586354274228616225251347)
        ·
          refine ⟨51879531411342924337877021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34586354274228616225251347 51879531411342924337877021)
          ·
            refine ⟨19454824279253596626703883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51879531411342924337877021 19454824279253596626703883)
            ·
              refine ⟨29182236418880394940055825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19454824279253596626703883 29182236418880394940055825)
              ·
                refine ⟨21886677314160296205041869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29182236418880394940055825 21886677314160296205041869)
                ·
                  refine ⟨8207503992810111076890701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21886677314160296205041869 8207503992810111076890701)
                  ·
                    refine ⟨3077813997303791653834013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8207503992810111076890701 3077813997303791653834013)
                    ·
                      refine ⟨1154180248988921870187755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3077813997303791653834013 1154180248988921870187755)
                      ·
                        rfl

theorem cell23_2247758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_2247758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247758 prefixEnd_2247758 := by exact prefixLift 2247758
  have htrace : WordTrace (prefixWord ++ tailWord_2247758) baseStart_2247758 baseEnd_2247758 := by
    simpa [prefixWord, tailWord_2247758, baseEnd_2247758] using wordTrace_append hprefix tailTrace_2247758
  have hstable : (prefixWord ++ tailWord_2247758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247758).length < 2 ^ (prefixWord ++ tailWord_2247758).sum := by decide
  have hdescent : baseEnd_2247758 < baseStart_2247758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247761 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 2, 7]
def baseStart_2247761 : Nat := 118140960795 + 2247761 * 2 ^ 59
def prefixEnd_2247761 : Nat := 4983230072969 + 3 ^ 40 * 2247761 * 2
def baseEnd_2247761 : Nat := 384727263143628452816747

theorem tailTrace_2247761 : CollatzResearch.WordTrace tailWord_2247761 prefixEnd_2247761 384727263143628452816747 := by
  unfold tailWord_2247761
  simp only [CollatzResearch.WordTrace]
  refine ⟨81982578809753258861103137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54655052539835505907402091 81982578809753258861103137)
  ·
    refine ⟨61486934107314944145827353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81982578809753258861103137 61486934107314944145827353)
    ·
      refine ⟨46115200580486208109370515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61486934107314944145827353 46115200580486208109370515)
      ·
        refine ⟨69172800870729312164055773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46115200580486208109370515 69172800870729312164055773)
        ·
          refine ⟨25939800326523492061520915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69172800870729312164055773 25939800326523492061520915)
          ·
            refine ⟨38909700489785238092281373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25939800326523492061520915 38909700489785238092281373)
            ·
              refine ⟨14591137683669464284605515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38909700489785238092281373 14591137683669464284605515)
              ·
                refine ⟨21886706525504196426908273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14591137683669464284605515 21886706525504196426908273)
                ·
                  refine ⟨16415029894128147320181205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21886706525504196426908273 16415029894128147320181205)
                  ·
                    refine ⟨384727263143628452816747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16415029894128147320181205 384727263143628452816747)
                    ·
                      rfl

theorem cell23_2247761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_2247761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247761 prefixEnd_2247761 := by exact prefixLift 2247761
  have htrace : WordTrace (prefixWord ++ tailWord_2247761) baseStart_2247761 baseEnd_2247761 := by
    simpa [prefixWord, tailWord_2247761, baseEnd_2247761] using wordTrace_append hprefix tailTrace_2247761
  have hstable : (prefixWord ++ tailWord_2247761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247761).length < 2 ^ (prefixWord ++ tailWord_2247761).sum := by decide
  have hdescent : baseEnd_2247761 < baseStart_2247761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247775 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 3]
def baseStart_2247775 : Nat := 118140960795 + 2247775 * 2 ^ 59
def prefixEnd_2247775 : Nat := 4983230072969 + 3 ^ 40 * 2247775 * 2
def baseEnd_2247775 : Nat := 1154188978160048303675177

theorem tailTrace_2247775 : CollatzResearch.WordTrace tailWord_2247775 prefixEnd_2247775 1154188978160048303675177 := by
  unfold tailWord_2247775
  simp only [CollatzResearch.WordTrace]
  refine ⟨81983089431702539252112779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54655392954468359501408519 81983089431702539252112779)
  ·
    refine ⟨122974634147553808878169169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81983089431702539252112779 122974634147553808878169169)
    ·
      refine ⟨92230975610665356658626877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122974634147553808878169169 92230975610665356658626877)
      ·
        refine ⟨34586615853999508746985079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92230975610665356658626877 34586615853999508746985079)
        ·
          refine ⟨51879923780999263120477619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34586615853999508746985079 51879923780999263120477619)
          ·
            refine ⟨77819885671498894680716429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51879923780999263120477619 77819885671498894680716429)
            ·
              refine ⟨29182457126812085505268661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77819885671498894680716429 29182457126812085505268661)
              ·
                refine ⟨2735855355638633016118937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29182457126812085505268661 2735855355638633016118937)
                ·
                  refine ⟨2051891516728974762089203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735855355638633016118937 2051891516728974762089203)
                  ·
                    refine ⟨3077837275093462143133805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2051891516728974762089203 3077837275093462143133805)
                    ·
                      refine ⟨1154188978160048303675177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3077837275093462143133805 1154188978160048303675177)
                      ·
                        rfl

theorem cell23_2247775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_2247775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247775 prefixEnd_2247775 := by exact prefixLift 2247775
  have htrace : WordTrace (prefixWord ++ tailWord_2247775) baseStart_2247775 baseEnd_2247775 := by
    simpa [prefixWord, tailWord_2247775, baseEnd_2247775] using wordTrace_append hprefix tailTrace_2247775
  have hstable : (prefixWord ++ tailWord_2247775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247775).length < 2 ^ (prefixWord ++ tailWord_2247775).sum := by decide
  have hdescent : baseEnd_2247775 < baseStart_2247775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247785 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 3, 3, 2]
def baseStart_2247785 : Nat := 118140960795 + 2247785 * 2 ^ 59
def prefixEnd_2247785 : Nat := 4983230072969 + 3 ^ 40 * 2247785 * 2
def baseEnd_2247785 : Nat := 1154194112966593264550131

theorem tailTrace_2247785 : CollatzResearch.WordTrace tailWord_2247785 prefixEnd_2247785 1154194112966593264550131 := by
  unfold tailWord_2247785
  simp only [CollatzResearch.WordTrace]
  refine ⟨81983454161666310959976809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54655636107777540639984539 81983454161666310959976809)
  ·
    refine ⟨61487590621249733219982607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81983454161666310959976809 61487590621249733219982607)
    ·
      refine ⟨92231385931874599829973911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61487590621249733219982607 92231385931874599829973911)
      ·
        refine ⟨138347078897811899744960867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92231385931874599829973911 138347078897811899744960867)
        ·
          refine ⟨207520618346717849617441301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138347078897811899744960867 207520618346717849617441301)
          ·
            refine ⟨9727528985002399200817561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 207520618346717849617441301 9727528985002399200817561)
            ·
              refine ⟨7295646738751799400613171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9727528985002399200817561 7295646738751799400613171)
              ·
                refine ⟨10943470108127699100919757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295646738751799400613171 10943470108127699100919757)
                ·
                  refine ⟨4103801290547887162844909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10943470108127699100919757 4103801290547887162844909)
                  ·
                    refine ⟨1538925483955457686066841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4103801290547887162844909 1538925483955457686066841)
                    ·
                      refine ⟨1154194112966593264550131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538925483955457686066841 1154194112966593264550131)
                      ·
                        rfl

theorem cell23_2247785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 3, 2].length) (baseStart_2247785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247785 prefixEnd_2247785 := by exact prefixLift 2247785
  have htrace : WordTrace (prefixWord ++ tailWord_2247785) baseStart_2247785 baseEnd_2247785 := by
    simpa [prefixWord, tailWord_2247785, baseEnd_2247785] using wordTrace_append hprefix tailTrace_2247785
  have hstable : (prefixWord ++ tailWord_2247785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247785).length < 2 ^ (prefixWord ++ tailWord_2247785).sum := by decide
  have hdescent : baseEnd_2247785 < baseStart_2247785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247791 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 1, 8]
def baseStart_2247791 : Nat := 118140960795 + 2247791 * 2 ^ 59
def prefixEnd_2247791 : Nat := 4983230072969 + 3 ^ 40 * 2247791 * 2
def baseEnd_2247791 : Nat := 384732397950173413691701

theorem tailTrace_2247791 : CollatzResearch.WordTrace tailWord_2247791 prefixEnd_2247791 384732397950173413691701 := by
  unfold tailWord_2247791
  simp only [CollatzResearch.WordTrace]
  refine ⟨81983672999644573984695227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54655781999763049323130151 81983672999644573984695227)
  ·
    refine ⟨122975509499466860977042841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81983672999644573984695227 122975509499466860977042841)
    ·
      refine ⟨92231632124600145732782131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122975509499466860977042841 92231632124600145732782131)
      ·
        refine ⟨138347448186900218599173197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92231632124600145732782131 138347448186900218599173197)
        ·
          refine ⟨51880293070087581974689949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138347448186900218599173197 51880293070087581974689949)
          ·
            refine ⟨19455109901282843240508731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51880293070087581974689949 19455109901282843240508731)
            ·
              refine ⟨29182664851924264860763097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19455109901282843240508731 29182664851924264860763097)
              ·
                refine ⟨21886998638943198645572323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29182664851924264860763097 21886998638943198645572323)
                ·
                  refine ⟨32830497958414797968358485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21886998638943198645572323 32830497958414797968358485)
                  ·
                    refine ⟨384732397950173413691701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32830497958414797968358485 384732397950173413691701)
                    ·
                      rfl

theorem cell23_2247791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_2247791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247791 prefixEnd_2247791 := by exact prefixLift 2247791
  have htrace : WordTrace (prefixWord ++ tailWord_2247791) baseStart_2247791 baseEnd_2247791 := by
    simpa [prefixWord, tailWord_2247791, baseEnd_2247791] using wordTrace_append hprefix tailTrace_2247791
  have hstable : (prefixWord ++ tailWord_2247791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247791).length < 2 ^ (prefixWord ++ tailWord_2247791).sum := by decide
  have hdescent : baseEnd_2247791 < baseStart_2247791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247809 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2247809 : Nat := 118140960795 + 2247809 * 2 ^ 59
def prefixEnd_2247809 : Nat := 4983230072969 + 3 ^ 40 * 2247809 * 2
def baseEnd_2247809 : Nat := 1154206436502301170650021

theorem tailTrace_2247809 : CollatzResearch.WordTrace tailWord_2247809 prefixEnd_2247809 1154206436502301170650021 := by
  unfold tailWord_2247809
  simp only [CollatzResearch.WordTrace]
  refine ⟨81984329513579363058850481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54656219675719575372566987 81984329513579363058850481)
  ·
    refine ⟨61488247135184522294137861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81984329513579363058850481 61488247135184522294137861)
    ·
      refine ⟨11529046337847097930150849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61488247135184522294137861 11529046337847097930150849)
      ·
        refine ⟨8646784753385323447613137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11529046337847097930150849 8646784753385323447613137)
        ·
          refine ⟨6485088565038992585709853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8646784753385323447613137 6485088565038992585709853)
          ·
            refine ⟨2431908211889622219641195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6485088565038992585709853 2431908211889622219641195)
            ·
              refine ⟨3647862317834433329461793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431908211889622219641195 3647862317834433329461793)
              ·
                refine ⟨2735896738375824997096345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3647862317834433329461793 2735896738375824997096345)
                ·
                  refine ⟨2051922553781868747822259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735896738375824997096345 2051922553781868747822259)
                  ·
                    refine ⟨3077883830672803121733389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2051922553781868747822259 3077883830672803121733389)
                    ·
                      refine ⟨1154206436502301170650021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3077883830672803121733389 1154206436502301170650021)
                      ·
                        rfl

theorem cell23_2247809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2247809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247809 prefixEnd_2247809 := by exact prefixLift 2247809
  have htrace : WordTrace (prefixWord ++ tailWord_2247809) baseStart_2247809 baseEnd_2247809 := by
    simpa [prefixWord, tailWord_2247809, baseEnd_2247809] using wordTrace_append hprefix tailTrace_2247809
  have hstable : (prefixWord ++ tailWord_2247809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247809).length < 2 ^ (prefixWord ++ tailWord_2247809).sum := by decide
  have hdescent : baseEnd_2247809 < baseStart_2247809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247832 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 1, 4, 2]
def baseStart_2247832 : Nat := 118140960795 + 2247832 * 2 ^ 59
def prefixEnd_2247832 : Nat := 4983230072969 + 3 ^ 40 * 2247832 * 2
def baseEnd_2247832 : Nat := 1154218246557354580662415

theorem tailTrace_2247832 : CollatzResearch.WordTrace tailWord_2247832 prefixEnd_2247832 1154218246557354580662415 := by
  unfold tailWord_2247832
  simp only [CollatzResearch.WordTrace]
  refine ⟨40992584196248018993468875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54656778928330691991291833 40992584196248018993468875)
  ·
    refine ⟨61488876294372028490203313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40992584196248018993468875 61488876294372028490203313)
    ·
      refine ⟨46116657220779021367652485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61488876294372028490203313 46116657220779021367652485)
      ·
        refine ⟨8646873228896066506434841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46116657220779021367652485 8646873228896066506434841)
        ·
          refine ⟨6485154921672049879826131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8646873228896066506434841 6485154921672049879826131)
          ·
            refine ⟨9727732382508074819739197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6485154921672049879826131 9727732382508074819739197)
            ·
              refine ⟨3647899643440528057402199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9727732382508074819739197 3647899643440528057402199)
              ·
                refine ⟨5471849465160792086103299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647899643440528057402199 5471849465160792086103299)
                ·
                  refine ⟨8207774197741188129154949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471849465160792086103299 8207774197741188129154949)
                  ·
                    refine ⟨1538957662076472774216553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8207774197741188129154949 1538957662076472774216553)
                    ·
                      refine ⟨1154218246557354580662415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1538957662076472774216553 1154218246557354580662415)
                      ·
                        rfl

theorem cell23_2247832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_2247832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247832 prefixEnd_2247832 := by exact prefixLift 2247832
  have htrace : WordTrace (prefixWord ++ tailWord_2247832) baseStart_2247832 baseEnd_2247832 := by
    simpa [prefixWord, tailWord_2247832, baseEnd_2247832] using wordTrace_append hprefix tailTrace_2247832
  have hstable : (prefixWord ++ tailWord_2247832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247832).length < 2 ^ (prefixWord ++ tailWord_2247832).sum := by decide
  have hdescent : baseEnd_2247832 < baseStart_2247832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247855 : List Nat := [1, 1, 2, 1, 2, 3, 5, 3, 5]
def baseStart_2247855 : Nat := 118140960795 + 2247855 * 2 ^ 59
def prefixEnd_2247855 : Nat := 4983230072969 + 3 ^ 40 * 2247855 * 2
def baseEnd_2247855 : Nat := 128247784068045332297201

theorem tailTrace_2247855 : CollatzResearch.WordTrace tailWord_2247855 prefixEnd_2247855 128247784068045332297201 := by
  unfold tailWord_2247855
  simp only [CollatzResearch.WordTrace]
  refine ⟨81986007271412712915025019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54657338180941808610016679 81986007271412712915025019)
  ·
    refine ⟨122979010907119069372537529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81986007271412712915025019 122979010907119069372537529)
    ·
      refine ⟨92234258180339302029403147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122979010907119069372537529 92234258180339302029403147)
      ·
        refine ⟨138351387270508953044104721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92234258180339302029403147 138351387270508953044104721)
        ·
          refine ⟨103763540452881714783078541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138351387270508953044104721 103763540452881714783078541)
          ·
            refine ⟨38911327669830643043654453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103763540452881714783078541 38911327669830643043654453)
            ·
              refine ⟨3647936969046622785342605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38911327669830643043654453 3647936969046622785342605)
              ·
                refine ⟨1367976363392483544503477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3647936969046622785342605 1367976363392483544503477)
                ·
                  refine ⟨128247784068045332297201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1367976363392483544503477 128247784068045332297201)
                  ·
                    rfl

theorem cell23_2247855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 5].length) (baseStart_2247855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247855 prefixEnd_2247855 := by exact prefixLift 2247855
  have htrace : WordTrace (prefixWord ++ tailWord_2247855) baseStart_2247855 baseEnd_2247855 := by
    simpa [prefixWord, tailWord_2247855, baseEnd_2247855] using wordTrace_append hprefix tailTrace_2247855
  have hstable : (prefixWord ++ tailWord_2247855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247855).length < 2 ^ (prefixWord ++ tailWord_2247855).sum := by decide
  have hdescent : baseEnd_2247855 < baseStart_2247855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247872 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 7]
def baseStart_2247872 : Nat := 118140960795 + 2247872 * 2 ^ 59
def prefixEnd_2247872 : Nat := 4983230072969 + 3 ^ 40 * 2247872 * 2
def baseEnd_2247872 : Nat := 128248753975948269351359

theorem tailTrace_2247872 : CollatzResearch.WordTrace tailWord_2247872 prefixEnd_2247872 128248753975948269351359 := by
  unfold tailWord_2247872
  simp only [CollatzResearch.WordTrace]
  refine ⟨40993313656175562409196935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54657751541567416545595913 40993313656175562409196935)
  ·
    refine ⟨61489970484263343613795403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40993313656175562409196935 61489970484263343613795403)
    ·
      refine ⟨92234955726395015420693105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61489970484263343613795403 92234955726395015420693105)
      ·
        refine ⟨69176216794796261565519829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92234955726395015420693105 69176216794796261565519829)
        ·
          refine ⟨1621317581128037380441871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 69176216794796261565519829 1621317581128037380441871)
          ·
            refine ⟨2431976371692056070662807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621317581128037380441871 2431976371692056070662807)
            ·
              refine ⟨3647964557538084105994211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431976371692056070662807 3647964557538084105994211)
              ·
                refine ⟨5471946836307126158991317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647964557538084105994211 5471946836307126158991317)
                ·
                  refine ⟨128248753975948269351359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5471946836307126158991317 128248753975948269351359)
                  ·
                    rfl

theorem cell23_2247872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 7].length) (baseStart_2247872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247872 prefixEnd_2247872 := by exact prefixLift 2247872
  have htrace : WordTrace (prefixWord ++ tailWord_2247872) baseStart_2247872 baseEnd_2247872 := by
    simpa [prefixWord, tailWord_2247872, baseEnd_2247872] using wordTrace_append hprefix tailTrace_2247872
  have hstable : (prefixWord ++ tailWord_2247872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247872).length < 2 ^ (prefixWord ++ tailWord_2247872).sum := by decide
  have hdescent : baseEnd_2247872 < baseStart_2247872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247905 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_2247905 : Nat := 118140960795 + 2247905 * 2 ^ 59
def prefixEnd_2247905 : Nat := 4983230072969 + 3 ^ 40 * 2247905 * 2
def baseEnd_2247905 : Nat := 1154255730645132795049579

theorem tailTrace_2247905 : CollatzResearch.WordTrace tailWord_2247905 prefixEnd_2247905 1154255730645132795049579 := by
  unfold tailWord_2247905
  simp only [CollatzResearch.WordTrace]
  refine ⟨81987830921231571454345169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54658553947487714302896779 81987830921231571454345169)
  ·
    refine ⟨61490873190923678590758877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81987830921231571454345169 61490873190923678590758877)
    ·
      refine ⟨23059077446596379471534579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61490873190923678590758877 23059077446596379471534579)
      ·
        refine ⟨34588616169894569207301869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23059077446596379471534579 34588616169894569207301869)
        ·
          refine ⟨12970731063710463452738201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34588616169894569207301869 12970731063710463452738201)
          ·
            refine ⟨9728048297782847589553651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12970731063710463452738201 9728048297782847589553651)
            ·
              refine ⟨14592072446674271384330477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9728048297782847589553651 14592072446674271384330477)
              ·
                refine ⟨5472027167502851769123929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14592072446674271384330477 5472027167502851769123929)
                ·
                  refine ⟨4104020375627138826842947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5472027167502851769123929 4104020375627138826842947)
                  ·
                    refine ⟨6156030563440708240264421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4104020375627138826842947 6156030563440708240264421)
                    ·
                      refine ⟨1154255730645132795049579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6156030563440708240264421 1154255730645132795049579)
                      ·
                        rfl

theorem cell23_2247905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_2247905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247905 prefixEnd_2247905 := by exact prefixLift 2247905
  have htrace : WordTrace (prefixWord ++ tailWord_2247905) baseStart_2247905 baseEnd_2247905 := by
    simpa [prefixWord, tailWord_2247905, baseEnd_2247905] using wordTrace_append hprefix tailTrace_2247905
  have hstable : (prefixWord ++ tailWord_2247905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247905).length < 2 ^ (prefixWord ++ tailWord_2247905).sum := by decide
  have hdescent : baseEnd_2247905 < baseStart_2247905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247972 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2247972 : Nat := 118140960795 + 2247972 * 2 ^ 59
def prefixEnd_2247972 : Nat := 4983230072969 + 3 ^ 40 * 2247972 * 2
def baseEnd_2247972 : Nat := 1154290133848984032911771

theorem tailTrace_2247972 : CollatzResearch.WordTrace tailWord_2247972 prefixEnd_2247972 1154290133848984032911771 := by
  unfold tailWord_2247972
  simp only [CollatzResearch.WordTrace]
  refine ⟨40995137305994420948517085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54660183074659227931356113 40995137305994420948517085)
  ·
    refine ⟨15373176489747907855693907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40995137305994420948517085 15373176489747907855693907)
    ·
      refine ⟨23059764734621861783540861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15373176489747907855693907 23059764734621861783540861)
      ·
        refine ⟨8647411775483198168827823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23059764734621861783540861 8647411775483198168827823)
        ·
          refine ⟨12971117663224797253241735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8647411775483198168827823 12971117663224797253241735)
          ·
            refine ⟨19456676494837195879862603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12971117663224797253241735 19456676494837195879862603)
            ·
              refine ⟨29185014742255793819793905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19456676494837195879862603 29185014742255793819793905)
              ·
                refine ⟨21888761056691845364845429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29185014742255793819793905 21888761056691845364845429)
                ·
                  refine ⟨2052071349064860502954259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21888761056691845364845429 2052071349064860502954259)
                  ·
                    refine ⟨3078107023597290754431389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052071349064860502954259 3078107023597290754431389)
                    ·
                      refine ⟨1154290133848984032911771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078107023597290754431389 1154290133848984032911771)
                      ·
                        rfl

theorem cell23_2247972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2247972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247972 prefixEnd_2247972 := by exact prefixLift 2247972
  have htrace : WordTrace (prefixWord ++ tailWord_2247972) baseStart_2247972 baseEnd_2247972 := by
    simpa [prefixWord, tailWord_2247972, baseEnd_2247972] using wordTrace_append hprefix tailTrace_2247972
  have hstable : (prefixWord ++ tailWord_2247972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247972).length < 2 ^ (prefixWord ++ tailWord_2247972).sum := by decide
  have hdescent : baseEnd_2247972 < baseStart_2247972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2247989 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2247989 : Nat := 118140960795 + 2247989 * 2 ^ 59
def prefixEnd_2247989 : Nat := 4983230072969 + 3 ^ 40 * 2247989 * 2
def baseEnd_2247989 : Nat := 1154298863020110466399193

theorem tailTrace_2247989 : CollatzResearch.WordTrace tailWord_2247989 prefixEnd_2247989 1154298863020110466399193 := by
  unfold tailWord_2247989
  simp only [CollatzResearch.WordTrace]
  refine ⟨81990894652927253800403021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54660596435284835866935347 81990894652927253800403021)
  ·
    refine ⟨30746585494847720175151133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81990894652927253800403021 30746585494847720175151133)
    ·
      refine ⟨11529969560567895065681675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30746585494847720175151133 11529969560567895065681675)
      ·
        refine ⟨17294954340851842598522513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11529969560567895065681675 17294954340851842598522513)
        ·
          refine ⟨12971215755638881948891885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17294954340851842598522513 12971215755638881948891885)
          ·
            refine ⟨4864205908364580730834457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12971215755638881948891885 4864205908364580730834457)
            ·
              refine ⟨3648154431273435548125843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4864205908364580730834457 3648154431273435548125843)
              ·
                refine ⟨5472231646910153322188765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648154431273435548125843 5472231646910153322188765)
                ·
                  refine ⟨2052086867591307495820787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5472231646910153322188765 2052086867591307495820787)
                  ·
                    refine ⟨3078130301386961243731181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052086867591307495820787 3078130301386961243731181)
                    ·
                      refine ⟨1154298863020110466399193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078130301386961243731181 1154298863020110466399193)
                      ·
                        rfl

theorem cell23_2247989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2247989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2247989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2247989 prefixEnd_2247989 := by exact prefixLift 2247989
  have htrace : WordTrace (prefixWord ++ tailWord_2247989) baseStart_2247989 baseEnd_2247989 := by
    simpa [prefixWord, tailWord_2247989, baseEnd_2247989] using wordTrace_append hprefix tailTrace_2247989
  have hstable : (prefixWord ++ tailWord_2247989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2247989).length < 2 ^ (prefixWord ++ tailWord_2247989).sum := by decide
  have hdescent : baseEnd_2247989 < baseStart_2247989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2247989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248012 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2248012 : Nat := 118140960795 + 2248012 * 2 ^ 59
def prefixEnd_2248012 : Nat := 4983230072969 + 3 ^ 40 * 2248012 * 2
def baseEnd_2248012 : Nat := 1154310673075163876411587

theorem tailTrace_2248012 : CollatzResearch.WordTrace tailWord_2248012 prefixEnd_2248012 1154310673075163876411587 := by
  unfold tailWord_2248012
  simp only [CollatzResearch.WordTrace]
  refine ⟨40995866765921964364245145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54661155687895952485660193 40995866765921964364245145)
  ·
    refine ⟨30746900074441473273183859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40995866765921964364245145 30746900074441473273183859)
    ·
      refine ⟨46120350111662209909775789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30746900074441473273183859 46120350111662209909775789)
      ·
        refine ⟨17295131291873328716165921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46120350111662209909775789 17295131291873328716165921)
        ·
          refine ⟨12971348468904996537124441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17295131291873328716165921 12971348468904996537124441)
          ·
            refine ⟨9728511351678747402843331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12971348468904996537124441 9728511351678747402843331)
            ·
              refine ⟨14592767027518121104264997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9728511351678747402843331 14592767027518121104264997)
              ·
                refine ⟨2736143817659647707049687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14592767027518121104264997 2736143817659647707049687)
                ·
                  refine ⟨4104215726489471560574531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736143817659647707049687 4104215726489471560574531)
                  ·
                    refine ⟨6156323589734207340861797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4104215726489471560574531 6156323589734207340861797)
                    ·
                      refine ⟨1154310673075163876411587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6156323589734207340861797 1154310673075163876411587)
                      ·
                        rfl

theorem cell23_2248012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2248012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248012 prefixEnd_2248012 := by exact prefixLift 2248012
  have htrace : WordTrace (prefixWord ++ tailWord_2248012) baseStart_2248012 baseEnd_2248012 := by
    simpa [prefixWord, tailWord_2248012, baseEnd_2248012] using wordTrace_append hprefix tailTrace_2248012
  have hstable : (prefixWord ++ tailWord_2248012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248012).length < 2 ^ (prefixWord ++ tailWord_2248012).sum := by decide
  have hdescent : baseEnd_2248012 < baseStart_2248012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248015 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 3]
def baseStart_2248015 : Nat := 118140960795 + 2248015 * 2 ^ 59
def prefixEnd_2248015 : Nat := 4983230072969 + 3 ^ 40 * 2248015 * 2
def baseEnd_2248015 : Nat := 1154312213517127364674073

theorem tailTrace_2248015 : CollatzResearch.WordTrace tailWord_2248015 prefixEnd_2248015 1154312213517127364674073 := by
  unfold tailWord_2248015
  simp only [CollatzResearch.WordTrace]
  refine ⟨81991842950833060240849499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54661228633888706827232999 81991842950833060240849499)
  ·
    refine ⟨122987764426249590361274249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81991842950833060240849499 122987764426249590361274249)
    ·
      refine ⟨92240823319687192770955687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122987764426249590361274249 92240823319687192770955687)
      ·
        refine ⟨138361234979530789156433531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92240823319687192770955687 138361234979530789156433531)
        ·
          refine ⟨207541852469296183734650297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138361234979530789156433531 207541852469296183734650297)
          ·
            refine ⟨155656389351972137800987723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207541852469296183734650297 155656389351972137800987723)
            ·
              refine ⟨233484584027958206701481585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155656389351972137800987723 233484584027958206701481585)
              ·
                refine ⟨175113438020968655026111189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233484584027958206701481585 175113438020968655026111189)
                ·
                  refine ⟨4104221203616452852174481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 175113438020968655026111189 4104221203616452852174481)
                  ·
                    refine ⟨3078165902712339639130861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104221203616452852174481 3078165902712339639130861)
                    ·
                      refine ⟨1154312213517127364674073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078165902712339639130861 1154312213517127364674073)
                      ·
                        rfl

theorem cell23_2248015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_2248015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248015 prefixEnd_2248015 := by exact prefixLift 2248015
  have htrace : WordTrace (prefixWord ++ tailWord_2248015) baseStart_2248015 baseEnd_2248015 := by
    simpa [prefixWord, tailWord_2248015, baseEnd_2248015] using wordTrace_append hprefix tailTrace_2248015
  have hstable : (prefixWord ++ tailWord_2248015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248015).length < 2 ^ (prefixWord ++ tailWord_2248015).sum := by decide
  have hdescent : baseEnd_2248015 < baseStart_2248015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248025 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_2248025 : Nat := 118140960795 + 2248025 * 2 ^ 59
def prefixEnd_2248025 : Nat := 4983230072969 + 3 ^ 40 * 2248025 * 2
def baseEnd_2248025 : Nat := 1154317348323672325549027

theorem tailTrace_2248025 : CollatzResearch.WordTrace tailWord_2248025 prefixEnd_2248025 1154317348323672325549027 := by
  unfold tailWord_2248025
  simp only [CollatzResearch.WordTrace]
  refine ⟨81992207680796831948713529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54661471787197887965809019 81992207680796831948713529)
  ·
    refine ⟨61494155760597623961535147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81992207680796831948713529 61494155760597623961535147)
    ·
      refine ⟨92241233640896435942302721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61494155760597623961535147 92241233640896435942302721)
      ·
        refine ⟨69180925230672326956727041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92241233640896435942302721 69180925230672326956727041)
        ·
          refine ⟨51885693923004245217545281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69180925230672326956727041 51885693923004245217545281)
          ·
            refine ⟨38914270442253183913158961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51885693923004245217545281 38914270442253183913158961)
            ·
              refine ⟨29185702831689887934869221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38914270442253183913158961 29185702831689887934869221)
              ·
                refine ⟨5472319280941853987787979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29185702831689887934869221 5472319280941853987787979)
                ·
                  refine ⟨8208478921412780981681969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5472319280941853987787979 8208478921412780981681969)
                  ·
                    refine ⟨6156359191059585736261477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8208478921412780981681969 6156359191059585736261477)
                    ·
                      refine ⟨1154317348323672325549027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6156359191059585736261477 1154317348323672325549027)
                      ·
                        rfl

theorem cell23_2248025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_2248025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248025 prefixEnd_2248025 := by exact prefixLift 2248025
  have htrace : WordTrace (prefixWord ++ tailWord_2248025) baseStart_2248025 baseEnd_2248025 := by
    simpa [prefixWord, tailWord_2248025, baseEnd_2248025] using wordTrace_append hprefix tailTrace_2248025
  have hstable : (prefixWord ++ tailWord_2248025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248025).length < 2 ^ (prefixWord ++ tailWord_2248025).sum := by decide
  have hdescent : baseEnd_2248025 < baseStart_2248025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248032 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5]
def baseStart_2248032 : Nat := 118140960795 + 2248032 * 2 ^ 59
def prefixEnd_2248032 : Nat := 4983230072969 + 3 ^ 40 * 2248032 * 2
def baseEnd_2248032 : Nat := 1154320942688253798161495

theorem tailTrace_2248032 : CollatzResearch.WordTrace tailWord_2248032 prefixEnd_2248032 1154320942688253798161495 := by
  unfold tailWord_2248032
  simp only [CollatzResearch.WordTrace]
  refine ⟨40996231495885736072109175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54661641994514314762812233 40996231495885736072109175)
  ·
    refine ⟨61494347243828604108163763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40996231495885736072109175 61494347243828604108163763)
    ·
      refine ⟨92241520865742906162245645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61494347243828604108163763 92241520865742906162245645)
      ·
        refine ⟨34590570324653589810842117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92241520865742906162245645 34590570324653589810842117)
        ·
          refine ⟨6485731935872548089532897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34590570324653589810842117 6485731935872548089532897)
          ·
            refine ⟨4864298951904411067149673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6485731935872548089532897 4864298951904411067149673)
            ·
              refine ⟨3648224213928308300362255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4864298951904411067149673 3648224213928308300362255)
              ·
                refine ⟨5472336320892462450543383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648224213928308300362255 5472336320892462450543383)
                ·
                  refine ⟨8208504481338693675815075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5472336320892462450543383 8208504481338693675815075)
                  ·
                    refine ⟨12312756722008040513722613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8208504481338693675815075 12312756722008040513722613)
                    ·
                      refine ⟨1154320942688253798161495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12312756722008040513722613 1154320942688253798161495)
                      ·
                        rfl

theorem cell23_2248032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_2248032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248032 prefixEnd_2248032 := by exact prefixLift 2248032
  have htrace : WordTrace (prefixWord ++ tailWord_2248032) baseStart_2248032 baseEnd_2248032 := by
    simpa [prefixWord, tailWord_2248032, baseEnd_2248032] using wordTrace_append hprefix tailTrace_2248032
  have hstable : (prefixWord ++ tailWord_2248032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248032).length < 2 ^ (prefixWord ++ tailWord_2248032).sum := by decide
  have hdescent : baseEnd_2248032 < baseStart_2248032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248035 : List Nat := [1, 1, 1, 5, 2, 4, 9]
def baseStart_2248035 : Nat := 118140960795 + 2248035 * 2 ^ 59
def prefixEnd_2248035 : Nat := 4983230072969 + 3 ^ 40 * 2248035 * 2
def baseEnd_2248035 : Nat := 14250894853459472671901

theorem tailTrace_2248035 : CollatzResearch.WordTrace tailWord_2248035 prefixEnd_2248035 14250894853459472671901 := by
  unfold tailWord_2248035
  simp only [CollatzResearch.WordTrace]
  refine ⟨81992572410760603656577559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54661714940507069104385039 81992572410760603656577559)
  ·
    refine ⟨122988858616140905484866339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81992572410760603656577559 122988858616140905484866339)
    ·
      refine ⟨184483287924211358227299509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122988858616140905484866339 184483287924211358227299509)
      ·
        refine ⟨17295308242894814833809329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 184483287924211358227299509 17295308242894814833809329)
        ·
          refine ⟨12971481182171111125356997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17295308242894814833809329 12971481182171111125356997)
          ·
            refine ⟨2432152721657083336004437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12971481182171111125356997 2432152721657083336004437)
            ·
              refine ⟨14250894853459472671901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2432152721657083336004437 14250894853459472671901)
              ·
                rfl

theorem cell23_2248035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 9].length) (baseStart_2248035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248035 prefixEnd_2248035 := by exact prefixLift 2248035
  have htrace : WordTrace (prefixWord ++ tailWord_2248035) baseStart_2248035 baseEnd_2248035 := by
    simpa [prefixWord, tailWord_2248035, baseEnd_2248035] using wordTrace_append hprefix tailTrace_2248035
  have hstable : (prefixWord ++ tailWord_2248035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248035).length < 2 ^ (prefixWord ++ tailWord_2248035).sum := by decide
  have hdescent : baseEnd_2248035 < baseStart_2248035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248066 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2248066 : Nat := 118140960795 + 2248066 * 2 ^ 59
def prefixEnd_2248066 : Nat := 4983230072969 + 3 ^ 40 * 2248066 * 2
def baseEnd_2248066 : Nat := 1154338401030506665136339

theorem tailTrace_2248066 : CollatzResearch.WordTrace tailWord_2248066 prefixEnd_2248066 1154338401030506665136339 := by
  unfold tailWord_2248066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20498425768412073987739013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54662468715765530633970701 20498425768412073987739013)
  ·
    refine ⟨3843454831577263872701065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20498425768412073987739013 3843454831577263872701065)
    ·
      refine ⟨2882591123682947904525799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3843454831577263872701065 2882591123682947904525799)
      ·
        refine ⟨4323886685524421856788699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882591123682947904525799 4323886685524421856788699)
        ·
          refine ⟨6485830028286632785183049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323886685524421856788699 6485830028286632785183049)
          ·
            refine ⟨4864372521214974588887287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6485830028286632785183049 4864372521214974588887287)
            ·
              refine ⟨7296558781822461883330931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4864372521214974588887287 7296558781822461883330931)
              ·
                refine ⟨10944838172733692824996397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7296558781822461883330931 10944838172733692824996397)
                ·
                  refine ⟨4104314314775134809373649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10944838172733692824996397 4104314314775134809373649)
                  ·
                    refine ⟨3078235736081351107030237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104314314775134809373649 3078235736081351107030237)
                    ·
                      refine ⟨1154338401030506665136339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078235736081351107030237 1154338401030506665136339)
                      ·
                        rfl

theorem cell23_2248066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2248066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248066 prefixEnd_2248066 := by exact prefixLift 2248066
  have htrace : WordTrace (prefixWord ++ tailWord_2248066) baseStart_2248066 baseEnd_2248066 := by
    simpa [prefixWord, tailWord_2248066, baseEnd_2248066] using wordTrace_append hprefix tailTrace_2248066
  have hstable : (prefixWord ++ tailWord_2248066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248066).length < 2 ^ (prefixWord ++ tailWord_2248066).sum := by decide
  have hdescent : baseEnd_2248066 < baseStart_2248066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248119 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 1, 4, 2]
def baseStart_2248119 : Nat := 118140960795 + 2248119 * 2 ^ 59
def prefixEnd_2248119 : Nat := 4983230072969 + 3 ^ 40 * 2248119 * 2
def baseEnd_2248119 : Nat := 1154365615505194957773595

theorem tailTrace_2248119 : CollatzResearch.WordTrace tailWord_2248119 prefixEnd_2248119 1154365615505194957773595 := by
  unfold tailWord_2248119
  simp only [CollatzResearch.WordTrace]
  refine ⟨81995636142456286002635411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54663757428304190668423607 81995636142456286002635411)
  ·
    refine ⟨122993454213684429003953117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81995636142456286002635411 122993454213684429003953117)
    ·
      refine ⟨46122545330131660876482419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122993454213684429003953117 46122545330131660876482419)
      ·
        refine ⟨69183817995197491314723629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46122545330131660876482419 69183817995197491314723629)
        ·
          refine ⟨25943931748199059243021361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69183817995197491314723629 25943931748199059243021361)
          ·
            refine ⟨19457948811149294432266021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25943931748199059243021361 19457948811149294432266021)
            ·
              refine ⟨3648365402090492706049879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19457948811149294432266021 3648365402090492706049879)
              ·
                refine ⟨5472548103135739059074819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648365402090492706049879 5472548103135739059074819)
                ·
                  refine ⟨8208822154703608588612229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5472548103135739059074819 8208822154703608588612229)
                  ·
                    refine ⟨1539154154006926610364793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8208822154703608588612229 1539154154006926610364793)
                    ·
                      refine ⟨1154365615505194957773595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539154154006926610364793 1154365615505194957773595)
                      ·
                        rfl

theorem cell23_2248119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_2248119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248119 prefixEnd_2248119 := by exact prefixLift 2248119
  have htrace : WordTrace (prefixWord ++ tailWord_2248119) baseStart_2248119 baseEnd_2248119 := by
    simpa [prefixWord, tailWord_2248119, baseEnd_2248119] using wordTrace_append hprefix tailTrace_2248119
  have hstable : (prefixWord ++ tailWord_2248119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248119).length < 2 ^ (prefixWord ++ tailWord_2248119).sum := by decide
  have hdescent : baseEnd_2248119 < baseStart_2248119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248152 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2248152 : Nat := 118140960795 + 2248152 * 2 ^ 59
def prefixEnd_2248152 : Nat := 4983230072969 + 3 ^ 40 * 2248152 * 2
def baseEnd_2248152 : Nat := 1154382560366793328660943

theorem tailTrace_2248152 : CollatzResearch.WordTrace tailWord_2248152 prefixEnd_2248152 1154382560366793328660943 := by
  unfold tailWord_2248152
  simp only [CollatzResearch.WordTrace]
  refine ⟨40998419875668366319293355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54664559834224488425724473 40998419875668366319293355)
  ·
    refine ⟨61497629813502549478940033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40998419875668366319293355 61497629813502549478940033)
    ·
      refine ⟨46123222360126912109205025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61497629813502549478940033 46123222360126912109205025)
      ·
        refine ⟨34592416770095184081903769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46123222360126912109205025 34592416770095184081903769)
        ·
          refine ⟨25944312577571388061427827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34592416770095184081903769 25944312577571388061427827)
          ·
            refine ⟨38916468866357082092141741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25944312577571388061427827 38916468866357082092141741)
            ·
              refine ⟨14593675824883905784553153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38916468866357082092141741 14593675824883905784553153)
              ·
                refine ⟨10945256868662929338414865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14593675824883905784553153 10945256868662929338414865)
                ·
                  refine ⟨8208942651497197003811149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10945256868662929338414865 8208942651497197003811149)
                  ·
                    refine ⟨3078353494311448876429181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8208942651497197003811149 3078353494311448876429181)
                    ·
                      refine ⟨1154382560366793328660943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078353494311448876429181 1154382560366793328660943)
                      ·
                        rfl

theorem cell23_2248152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2248152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248152 prefixEnd_2248152 := by exact prefixLift 2248152
  have htrace : WordTrace (prefixWord ++ tailWord_2248152) baseStart_2248152 baseEnd_2248152 := by
    simpa [prefixWord, tailWord_2248152, baseEnd_2248152] using wordTrace_append hprefix tailTrace_2248152
  have hstable : (prefixWord ++ tailWord_2248152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248152).length < 2 ^ (prefixWord ++ tailWord_2248152).sum := by decide
  have hdescent : baseEnd_2248152 < baseStart_2248152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248153 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 2, 2, 2]
def baseStart_2248153 : Nat := 118140960795 + 2248153 * 2 ^ 59
def prefixEnd_2248153 : Nat := 4983230072969 + 3 ^ 40 * 2248153 * 2
def baseEnd_2248153 : Nat := 1154383073847447824748439

theorem tailTrace_2248153 : CollatzResearch.WordTrace tailWord_2248153 prefixEnd_2248153 1154383073847447824748439 := by
  unfold tailWord_2248153
  simp only [CollatzResearch.WordTrace]
  refine ⟨81996876224333109809373113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54664584149555406539582075 81996876224333109809373113)
  ·
    refine ⟨61497657168249832357029835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81996876224333109809373113 61497657168249832357029835)
    ·
      refine ⟨92246485752374748535544753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61497657168249832357029835 92246485752374748535544753)
      ·
        refine ⟨69184864314281061401658565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92246485752374748535544753 69184864314281061401658565)
        ·
          refine ⟨12972162058927699012810981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69184864314281061401658565 12972162058927699012810981)
          ·
            refine ⟨2432280386048943564902059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12972162058927699012810981 2432280386048943564902059)
            ·
              refine ⟨3648420579073415347353089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432280386048943564902059 3648420579073415347353089)
              ·
                refine ⟨2736315434305061510514817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648420579073415347353089 2736315434305061510514817)
                ·
                  refine ⟨2052236575728796132886113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2736315434305061510514817 2052236575728796132886113)
                  ·
                    refine ⟨1539177431796597099664585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052236575728796132886113 1539177431796597099664585)
                    ·
                      refine ⟨1154383073847447824748439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539177431796597099664585 1154383073847447824748439)
                      ·
                        rfl

theorem cell23_2248153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_2248153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248153 prefixEnd_2248153 := by exact prefixLift 2248153
  have htrace : WordTrace (prefixWord ++ tailWord_2248153) baseStart_2248153 baseEnd_2248153 := by
    simpa [prefixWord, tailWord_2248153, baseEnd_2248153] using wordTrace_append hprefix tailTrace_2248153
  have hstable : (prefixWord ++ tailWord_2248153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248153).length < 2 ^ (prefixWord ++ tailWord_2248153).sum := by decide
  have hdescent : baseEnd_2248153 < baseStart_2248153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248170 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_2248170 : Nat := 118140960795 + 2248170 * 2 ^ 59
def prefixEnd_2248170 : Nat := 4983230072969 + 3 ^ 40 * 2248170 * 2
def baseEnd_2248170 : Nat := 1154391803018574258235861

theorem tailTrace_2248170 : CollatzResearch.WordTrace tailWord_2248170 prefixEnd_2248170 1154391803018574258235861 := by
  unfold tailWord_2248170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20499374066317880428185491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54664997510181014475161309 20499374066317880428185491)
  ·
    refine ⟨30749061099476820642278237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20499374066317880428185491 30749061099476820642278237)
    ·
      refine ⟨11530897912303807740854339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30749061099476820642278237 11530897912303807740854339)
      ·
        refine ⟨17296346868455711611281509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11530897912303807740854339 17296346868455711611281509)
        ·
          refine ⟨3243065037835445927115283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17296346868455711611281509 3243065037835445927115283)
          ·
            refine ⟨4864597556753168890672925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243065037835445927115283 4864597556753168890672925)
            ·
              refine ⟨1824224083782438334002347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4864597556753168890672925 1824224083782438334002347)
              ·
                refine ⟨2736336125673657501003521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824224083782438334002347 2736336125673657501003521)
                ·
                  refine ⟨2052252094255243125752641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2736336125673657501003521 2052252094255243125752641)
                  ·
                    refine ⟨1539189070691432344314481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052252094255243125752641 1539189070691432344314481)
                    ·
                      refine ⟨1154391803018574258235861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539189070691432344314481 1154391803018574258235861)
                      ·
                        rfl

theorem cell23_2248170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_2248170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248170 prefixEnd_2248170 := by exact prefixLift 2248170
  have htrace : WordTrace (prefixWord ++ tailWord_2248170) baseStart_2248170 baseEnd_2248170 := by
    simpa [prefixWord, tailWord_2248170, baseEnd_2248170] using wordTrace_append hprefix tailTrace_2248170
  have hstable : (prefixWord ++ tailWord_2248170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248170).length < 2 ^ (prefixWord ++ tailWord_2248170).sum := by decide
  have hdescent : baseEnd_2248170 < baseStart_2248170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248185 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 10]
def baseStart_2248185 : Nat := 118140960795 + 2248185 * 2 ^ 59
def prefixEnd_2248185 : Nat := 4983230072969 + 3 ^ 40 * 2248185 * 2
def baseEnd_2248185 : Nat := 384799835076130566516097

theorem tailTrace_2248185 : CollatzResearch.WordTrace tailWord_2248185 prefixEnd_2248185 384799835076130566516097 := by
  unfold tailWord_2248185
  simp only [CollatzResearch.WordTrace]
  refine ⟨81998043360217179274538009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54665362240144786183025339 81998043360217179274538009)
  ·
    refine ⟨61498532520162884455903507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81998043360217179274538009 61498532520162884455903507)
    ·
      refine ⟨92247798780244326683855261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61498532520162884455903507 92247798780244326683855261)
      ·
        refine ⟨34592924542591622506445723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92247798780244326683855261 34592924542591622506445723)
        ·
          refine ⟨51889386813887433759668585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34592924542591622506445723 51889386813887433759668585)
          ·
            refine ⟨38917040110415575319751439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51889386813887433759668585 38917040110415575319751439)
            ·
              refine ⟨58375560165623362979627159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38917040110415575319751439 58375560165623362979627159)
              ·
                refine ⟨87563340248435044469440739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58375560165623362979627159 87563340248435044469440739)
                ·
                  refine ⟨131345010372652566704161109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87563340248435044469440739 131345010372652566704161109)
                  ·
                    refine ⟨384799835076130566516097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 131345010372652566704161109 384799835076130566516097)
                    ·
                      rfl

theorem cell23_2248185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_2248185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248185 prefixEnd_2248185 := by exact prefixLift 2248185
  have htrace : WordTrace (prefixWord ++ tailWord_2248185) baseStart_2248185 baseEnd_2248185 := by
    simpa [prefixWord, tailWord_2248185, baseEnd_2248185] using wordTrace_append hprefix tailTrace_2248185
  have hstable : (prefixWord ++ tailWord_2248185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248185).length < 2 ^ (prefixWord ++ tailWord_2248185).sum := by decide
  have hdescent : baseEnd_2248185 < baseStart_2248185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248193 : List Nat := [1, 2, 4, 1, 5, 1, 1, 3, 5]
def baseStart_2248193 : Nat := 118140960795 + 2248193 * 2 ^ 59
def prefixEnd_2248193 : Nat := 4983230072969 + 3 ^ 40 * 2248193 * 2
def baseEnd_2248193 : Nat := 128267068119291963138695

theorem tailTrace_2248193 : CollatzResearch.WordTrace tailWord_2248193 prefixEnd_2248193 128267068119291963138695 := by
  unfold tailWord_2248193
  simp only [CollatzResearch.WordTrace]
  refine ⟨81998335144188196640829233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54665556762792131093886155 81998335144188196640829233)
  ·
    refine ⟨61498751358141147480621925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81998335144188196640829233 61498751358141147480621925)
    ·
      refine ⟨11531015879651465152616611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61498751358141147480621925 11531015879651465152616611)
      ·
        refine ⟨17296523819477197728924917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11531015879651465152616611 17296523819477197728924917)
        ·
          refine ⟨1621549108075987287086711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17296523819477197728924917 1621549108075987287086711)
          ·
            refine ⟨2432323662113980930630067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621549108075987287086711 2432323662113980930630067)
            ·
              refine ⟨3648485493170971395945101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432323662113980930630067 3648485493170971395945101)
              ·
                refine ⟨1368182059939114273479413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3648485493170971395945101 1368182059939114273479413)
                ·
                  refine ⟨128267068119291963138695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1368182059939114273479413 128267068119291963138695)
                  ·
                    rfl

theorem cell23_2248193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 5].length) (baseStart_2248193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248193 prefixEnd_2248193 := by exact prefixLift 2248193
  have htrace : WordTrace (prefixWord ++ tailWord_2248193) baseStart_2248193 baseEnd_2248193 := by
    simpa [prefixWord, tailWord_2248193, baseEnd_2248193] using wordTrace_append hprefix tailTrace_2248193
  have hstable : (prefixWord ++ tailWord_2248193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248193).length < 2 ^ (prefixWord ++ tailWord_2248193).sum := by decide
  have hdescent : baseEnd_2248193 < baseStart_2248193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248276 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2248276 : Nat := 118140960795 + 2248276 * 2 ^ 59
def prefixEnd_2248276 : Nat := 4983230072969 + 3 ^ 40 * 2248276 * 2
def baseEnd_2248276 : Nat := 1154446231967950843510373

theorem tailTrace_2248276 : CollatzResearch.WordTrace tailWord_2248276 prefixEnd_2248276 1154446231967950843510373 := by
  unfold tailWord_2248276
  simp only [CollatzResearch.WordTrace]
  refine ⟨41000681201443750908050341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54667574935258334544067121 41000681201443750908050341)
  ·
    refine ⟨7687627725270703295259439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41000681201443750908050341 7687627725270703295259439)
    ·
      refine ⟨11531441587906054942889159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7687627725270703295259439 11531441587906054942889159)
      ·
        refine ⟨17297162381859082414333739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11531441587906054942889159 17297162381859082414333739)
        ·
          refine ⟨25945743572788623621500609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17297162381859082414333739 25945743572788623621500609)
          ·
            refine ⟨19459307679591467716125457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25945743572788623621500609 19459307679591467716125457)
            ·
              refine ⟨14594480759693600787094093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19459307679591467716125457 14594480759693600787094093)
              ·
                refine ⟨5472930284885100295160285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14594480759693600787094093 5472930284885100295160285)
                ·
                  refine ⟨2052348856831912610685107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5472930284885100295160285 2052348856831912610685107)
                  ·
                    refine ⟨3078523285247868916027661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052348856831912610685107 3078523285247868916027661)
                    ·
                      refine ⟨1154446231967950843510373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078523285247868916027661 1154446231967950843510373)
                      ·
                        rfl

theorem cell23_2248276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2248276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248276 prefixEnd_2248276 := by exact prefixLift 2248276
  have htrace : WordTrace (prefixWord ++ tailWord_2248276) baseStart_2248276 baseEnd_2248276 := by
    simpa [prefixWord, tailWord_2248276, baseEnd_2248276] using wordTrace_append hprefix tailTrace_2248276
  have hstable : (prefixWord ++ tailWord_2248276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248276).length < 2 ^ (prefixWord ++ tailWord_2248276).sum := by decide
  have hdescent : baseEnd_2248276 < baseStart_2248276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248310 : List Nat := [5, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2248310 : Nat := 118140960795 + 2248310 * 2 ^ 59
def prefixEnd_2248310 : Nat := 4983230072969 + 3 ^ 40 * 2248310 * 2
def baseEnd_2248310 : Nat := 1154463690310203710485217

theorem tailTrace_2248310 : CollatzResearch.WordTrace tailWord_2248310 prefixEnd_2248310 1154463690310203710485217 := by
  unfold tailWord_2248310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5125162655297770351427399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54668401656509550415225589 5125162655297770351427399)
  ·
    refine ⟨7687743982946655527141099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5125162655297770351427399 7687743982946655527141099)
    ·
      refine ⟨11531615974419983290711649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7687743982946655527141099 11531615974419983290711649)
      ·
        refine ⟨8648711980814987468033737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11531615974419983290711649 8648711980814987468033737)
        ·
          refine ⟨6486533985611240601025303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8648711980814987468033737 6486533985611240601025303)
          ·
            refine ⟨9729800978416860901537955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6486533985611240601025303 9729800978416860901537955)
            ·
              refine ⟨14594701467625291352306933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9729800978416860901537955 14594701467625291352306933)
              ·
                refine ⟨1368253262589871064278775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14594701467625291352306933 1368253262589871064278775)
                ·
                  refine ⟨2052379893884806596418163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368253262589871064278775 2052379893884806596418163)
                  ·
                    refine ⟨3078569840827209894627245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052379893884806596418163 3078569840827209894627245)
                    ·
                      refine ⟨1154463690310203710485217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078569840827209894627245 1154463690310203710485217)
                      ·
                        rfl

theorem cell23_2248310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2248310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248310 prefixEnd_2248310 := by exact prefixLift 2248310
  have htrace : WordTrace (prefixWord ++ tailWord_2248310) baseStart_2248310 baseEnd_2248310 := by
    simpa [prefixWord, tailWord_2248310, baseEnd_2248310] using wordTrace_append hprefix tailTrace_2248310
  have hstable : (prefixWord ++ tailWord_2248310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248310).length < 2 ^ (prefixWord ++ tailWord_2248310).sum := by decide
  have hdescent : baseEnd_2248310 < baseStart_2248310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248316 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_2248316 : Nat := 118140960795 + 2248316 * 2 ^ 59
def prefixEnd_2248316 : Nat := 4983230072969 + 3 ^ 40 * 2248316 * 2
def baseEnd_2248316 : Nat := 1154466771194130687010189

theorem tailTrace_2248316 : CollatzResearch.WordTrace tailWord_2248316 prefixEnd_2248316 1154466771194130687010189 := by
  unfold tailWord_2248316
  simp only [CollatzResearch.WordTrace]
  refine ⟨41001410661371294323778401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54668547548495059098371201 41001410661371294323778401)
  ·
    refine ⟨30751057996028470742833801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41001410661371294323778401 30751057996028470742833801)
    ·
      refine ⟨23063293497021353057125351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30751057996028470742833801 23063293497021353057125351)
      ·
        refine ⟨34594940245532029585688027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23063293497021353057125351 34594940245532029585688027)
        ·
          refine ⟨51892410368298044378532041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34594940245532029585688027 51892410368298044378532041)
          ·
            refine ⟨38919307776223533283899031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51892410368298044378532041 38919307776223533283899031)
            ·
              refine ⟨58378961664335299925848547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38919307776223533283899031 58378961664335299925848547)
              ·
                refine ⟨87568442496502949888772821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58378961664335299925848547 87568442496502949888772821)
                ·
                  refine ⟨2052385371011787888018113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 87568442496502949888772821 2052385371011787888018113)
                  ·
                    refine ⟨1539289028258840916013585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052385371011787888018113 1539289028258840916013585)
                    ·
                      refine ⟨1154466771194130687010189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539289028258840916013585 1154466771194130687010189)
                      ·
                        rfl

theorem cell23_2248316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_2248316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248316 prefixEnd_2248316 := by exact prefixLift 2248316
  have htrace : WordTrace (prefixWord ++ tailWord_2248316) baseStart_2248316 baseEnd_2248316 := by
    simpa [prefixWord, tailWord_2248316, baseEnd_2248316] using wordTrace_append hprefix tailTrace_2248316
  have hstable : (prefixWord ++ tailWord_2248316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248316).length < 2 ^ (prefixWord ++ tailWord_2248316).sum := by decide
  have hdescent : baseEnd_2248316 < baseStart_2248316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248343 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 2, 4]
def baseStart_2248343 : Nat := 118140960795 + 2248343 * 2 ^ 59
def prefixEnd_2248343 : Nat := 4983230072969 + 3 ^ 40 * 2248343 * 2
def baseEnd_2248343 : Nat := 384826878390600693790855

theorem tailTrace_2248343 : CollatzResearch.WordTrace tailWord_2248343 prefixEnd_2248343 384826878390600693790855 := by
  unfold tailWord_2248343
  simp only [CollatzResearch.WordTrace]
  refine ⟨82003806093644772258789683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54669204062429848172526455 82003806093644772258789683)
  ·
    refine ⟨123005709140467158388184525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82003806093644772258789683 123005709140467158388184525)
    ·
      refine ⟨46127140927675184395569197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123005709140467158388184525 46127140927675184395569197)
      ·
        refine ⟨17297677847878194148338449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46127140927675184395569197 17297677847878194148338449)
        ·
          refine ⟨12973258385908645611253837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17297677847878194148338449 12973258385908645611253837)
          ·
            refine ⟨4864971894715742104220189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12973258385908645611253837 4864971894715742104220189)
            ·
              refine ⟨1824364460518403289082571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4864971894715742104220189 1824364460518403289082571)
              ·
                refine ⟨2736546690777604933623857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824364460518403289082571 2736546690777604933623857)
                ·
                  refine ⟨2052410018083203700217893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2736546690777604933623857 2052410018083203700217893)
                  ·
                    refine ⟨384826878390600693790855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2052410018083203700217893 384826878390600693790855)
                    ·
                      rfl

theorem cell23_2248343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_2248343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248343 prefixEnd_2248343 := by exact prefixLift 2248343
  have htrace : WordTrace (prefixWord ++ tailWord_2248343) baseStart_2248343 baseEnd_2248343 := by
    simpa [prefixWord, tailWord_2248343, baseEnd_2248343] using wordTrace_append hprefix tailTrace_2248343
  have hstable : (prefixWord ++ tailWord_2248343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248343).length < 2 ^ (prefixWord ++ tailWord_2248343).sum := by decide
  have hdescent : baseEnd_2248343 < baseStart_2248343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248350 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_2248350 : Nat := 118140960795 + 2248350 * 2 ^ 59
def prefixEnd_2248350 : Nat := 4983230072969 + 3 ^ 40 * 2248350 * 2
def baseEnd_2248350 : Nat := 1154484229536383553985033

theorem tailTrace_2248350 : CollatzResearch.WordTrace tailWord_2248350 prefixEnd_2248350 1154484229536383553985033 := by
  unfold tailWord_2248350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10250507675577426556786813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54669374269746274969529669 10250507675577426556786813)
  ·
    refine ⟨3843940378341534958795055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10250507675577426556786813 3843940378341534958795055)
    ·
      refine ⟨5765910567512302438192583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3843940378341534958795055 5765910567512302438192583)
      ·
        refine ⟨8648865851268453657288875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5765910567512302438192583 8648865851268453657288875)
        ·
          refine ⟨12973298776902680485933313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8648865851268453657288875 12973298776902680485933313)
          ·
            refine ⟨9729974082677010364449985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12973298776902680485933313 9729974082677010364449985)
            ·
              refine ⟨7297480562007757773337489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9729974082677010364449985 7297480562007757773337489)
              ·
                refine ⟨5473110421505818330003117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7297480562007757773337489 5473110421505818330003117)
                ·
                  refine ⟨2052416408064681873751169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5473110421505818330003117 2052416408064681873751169)
                  ·
                    refine ⟨1539312306048511405313377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052416408064681873751169 1539312306048511405313377)
                    ·
                      refine ⟨1154484229536383553985033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539312306048511405313377 1154484229536383553985033)
                      ·
                        rfl

theorem cell23_2248350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_2248350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248350 prefixEnd_2248350 := by exact prefixLift 2248350
  have htrace : WordTrace (prefixWord ++ tailWord_2248350) baseStart_2248350 baseEnd_2248350 := by
    simpa [prefixWord, tailWord_2248350, baseEnd_2248350] using wordTrace_append hprefix tailTrace_2248350
  have hstable : (prefixWord ++ tailWord_2248350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248350).length < 2 ^ (prefixWord ++ tailWord_2248350).sum := by decide
  have hdescent : baseEnd_2248350 < baseStart_2248350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248353 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2248353 : Nat := 118140960795 + 2248353 * 2 ^ 59
def prefixEnd_2248353 : Nat := 4983230072969 + 3 ^ 40 * 2248353 * 2
def baseEnd_2248353 : Nat := 1154485769978347042247519

theorem tailTrace_2248353 : CollatzResearch.WordTrace tailWord_2248353 prefixEnd_2248353 1154485769978347042247519 := by
  unfold tailWord_2248353
  simp only [CollatzResearch.WordTrace]
  refine ⟨82004170823608543966653713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54669447215739029311102475 82004170823608543966653713)
  ·
    refine ⟨61503128117706407974990285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82004170823608543966653713 61503128117706407974990285)
    ·
      refine ⟨23063673044139902990621357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61503128117706407974990285 23063673044139902990621357)
      ·
        refine ⟨8648877391552463621483009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23063673044139902990621357 8648877391552463621483009)
        ·
          refine ⟨6486658043664347716112257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8648877391552463621483009 6486658043664347716112257)
          ·
            refine ⟨4864993532748260787084193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6486658043664347716112257 4864993532748260787084193)
            ·
              refine ⟨3648745149561195590313145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4864993532748260787084193 3648745149561195590313145)
              ·
                refine ⟨2736558862170896692734859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648745149561195590313145 2736558862170896692734859)
                ·
                  refine ⟨4104838293256345039102289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736558862170896692734859 4104838293256345039102289)
                  ·
                    refine ⟨3078628719942258779326717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104838293256345039102289 3078628719942258779326717)
                    ·
                      refine ⟨1154485769978347042247519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078628719942258779326717 1154485769978347042247519)
                      ·
                        rfl

theorem cell23_2248353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2248353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248353 prefixEnd_2248353 := by exact prefixLift 2248353
  have htrace : WordTrace (prefixWord ++ tailWord_2248353) baseStart_2248353 baseEnd_2248353 := by
    simpa [prefixWord, tailWord_2248353, baseEnd_2248353] using wordTrace_append hprefix tailTrace_2248353
  have hstable : (prefixWord ++ tailWord_2248353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248353).length < 2 ^ (prefixWord ++ tailWord_2248353).sum := by decide
  have hdescent : baseEnd_2248353 < baseStart_2248353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248356 : List Nat := [2, 3, 1, 2, 2, 4, 2, 7]
def baseStart_2248356 : Nat := 118140960795 + 2248356 * 2 ^ 59
def prefixEnd_2248356 : Nat := 4983230072969 + 3 ^ 40 * 2248356 * 2
def baseEnd_2248356 : Nat := 42758789274826315944815

theorem tailTrace_2248356 : CollatzResearch.WordTrace tailWord_2248356 prefixEnd_2248356 42758789274826315944815 := by
  unfold tailWord_2248356
  simp only [CollatzResearch.WordTrace]
  refine ⟨41002140121298837739506461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54669520161731783652675281 41002140121298837739506461)
  ·
    refine ⟨15375802545487064152314923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41002140121298837739506461 15375802545487064152314923)
    ·
      refine ⟨23063703818230596228472385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15375802545487064152314923 23063703818230596228472385)
      ·
        refine ⟨17297777863672947171354289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23063703818230596228472385 17297777863672947171354289)
        ·
          refine ⟨12973333397754710378515717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17297777863672947171354289 12973333397754710378515717)
          ·
            refine ⟨2432500012079008195971697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12973333397754710378515717 2432500012079008195971697)
            ·
              refine ⟨1824375009059256146978773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2432500012079008195971697 1824375009059256146978773)
              ·
                refine ⟨42758789274826315944815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1824375009059256146978773 42758789274826315944815)
                ·
                  rfl

theorem cell23_2248356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 7].length) (baseStart_2248356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248356 prefixEnd_2248356 := by exact prefixLift 2248356
  have htrace : WordTrace (prefixWord ++ tailWord_2248356) baseStart_2248356 baseEnd_2248356 := by
    simpa [prefixWord, tailWord_2248356, baseEnd_2248356] using wordTrace_append hprefix tailTrace_2248356
  have hstable : (prefixWord ++ tailWord_2248356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248356).length < 2 ^ (prefixWord ++ tailWord_2248356).sum := by decide
  have hdescent : baseEnd_2248356 < baseStart_2248356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248409 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_2248409 : Nat := 118140960795 + 2248409 * 2 ^ 59
def prefixEnd_2248409 : Nat := 4983230072969 + 3 ^ 40 * 2248409 * 2
def baseEnd_2248409 : Nat := 1154514524894998823147261

theorem tailTrace_2248409 : CollatzResearch.WordTrace tailWord_2248409 prefixEnd_2248409 1154514524894998823147261 := by
  unfold tailWord_2248409
  simp only [CollatzResearch.WordTrace]
  refine ⟨82006213311405665530692281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54670808874270443687128187 82006213311405665530692281)
  ·
    refine ⟨61504659983554249148019211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82006213311405665530692281 61504659983554249148019211)
    ·
      refine ⟨92256989975331373722028817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61504659983554249148019211 92256989975331373722028817)
      ·
        refine ⟨69192742481498530291521613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92256989975331373722028817 69192742481498530291521613)
        ·
          refine ⟨25947278430561948859320605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69192742481498530291521613 25947278430561948859320605)
          ·
            refine ⟨9730229411460730822245227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25947278430561948859320605 9730229411460730822245227)
            ·
              refine ⟨14595344117191096233367841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9730229411460730822245227 14595344117191096233367841)
              ·
                refine ⟨10946508087893322175025881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14595344117191096233367841 10946508087893322175025881)
                ·
                  refine ⟨8209881065919991631269411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10946508087893322175025881 8209881065919991631269411)
                  ·
                    refine ⟨12314821598879987446904117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8209881065919991631269411 12314821598879987446904117)
                    ·
                      refine ⟨1154514524894998823147261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12314821598879987446904117 1154514524894998823147261)
                      ·
                        rfl

theorem cell23_2248409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_2248409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248409 prefixEnd_2248409 := by exact prefixLift 2248409
  have htrace : WordTrace (prefixWord ++ tailWord_2248409) baseStart_2248409 baseEnd_2248409 := by
    simpa [prefixWord, tailWord_2248409, baseEnd_2248409] using wordTrace_append hprefix tailTrace_2248409
  have hstable : (prefixWord ++ tailWord_2248409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248409).length < 2 ^ (prefixWord ++ tailWord_2248409).sum := by decide
  have hdescent : baseEnd_2248409 < baseStart_2248409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248410 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2]
def baseStart_2248410 : Nat := 118140960795 + 2248410 * 2 ^ 59
def prefixEnd_2248410 : Nat := 4983230072969 + 3 ^ 40 * 2248410 * 2
def baseEnd_2248410 : Nat := 1154515038375653319234757

theorem tailTrace_2248410 : CollatzResearch.WordTrace tailWord_2248410 prefixEnd_2248410 1154515038375653319234757 := by
  unfold tailWord_2248410
  simp only [CollatzResearch.WordTrace]
  refine ⟨20501562446100510675369671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54670833189601361800985789 20501562446100510675369671)
  ·
    refine ⟨30752343669150766013054507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20501562446100510675369671 30752343669150766013054507)
    ·
      refine ⟨46128515503726149019581761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30752343669150766013054507 46128515503726149019581761)
      ·
        refine ⟨34596386627794611764686321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46128515503726149019581761 34596386627794611764686321)
        ·
          refine ⟨25947289970845958823514741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34596386627794611764686321 25947289970845958823514741)
          ·
            refine ⟨2432558434766808639704507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25947289970845958823514741 2432558434766808639704507)
            ·
              refine ⟨3648837652150212959556761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432558434766808639704507 3648837652150212959556761)
              ·
                refine ⟨2736628239112659719667571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648837652150212959556761 2736628239112659719667571)
                ·
                  refine ⟨4104942358668989579501357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736628239112659719667571 4104942358668989579501357)
                  ·
                    refine ⟨1539353384500871092313009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4104942358668989579501357 1539353384500871092313009)
                    ·
                      refine ⟨1154515038375653319234757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539353384500871092313009 1154515038375653319234757)
                      ·
                        rfl

theorem cell23_2248410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_2248410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248410 prefixEnd_2248410 := by exact prefixLift 2248410
  have htrace : WordTrace (prefixWord ++ tailWord_2248410) baseStart_2248410 baseEnd_2248410 := by
    simpa [prefixWord, tailWord_2248410, baseEnd_2248410] using wordTrace_append hprefix tailTrace_2248410
  have hstable : (prefixWord ++ tailWord_2248410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248410).length < 2 ^ (prefixWord ++ tailWord_2248410).sum := by decide
  have hdescent : baseEnd_2248410 < baseStart_2248410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248456 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_2248456 : Nat := 118140960795 + 2248456 * 2 ^ 59
def prefixEnd_2248456 : Nat := 4983230072969 + 3 ^ 40 * 2248456 * 2
def baseEnd_2248456 : Nat := 1154538658485760139259545

theorem tailTrace_2248456 : CollatzResearch.WordTrace tailWord_2248456 prefixEnd_2248456 1154538658485760139259545 := by
  unfold tailWord_2248456
  simp only [CollatzResearch.WordTrace]
  refine ⟨41003963771117696278826611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54671951694823595038435481 41003963771117696278826611)
  ·
    refine ⟨61505945656676544418239917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41003963771117696278826611 61505945656676544418239917)
    ·
      refine ⟨23064729621253704156839969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61505945656676544418239917 23064729621253704156839969)
      ·
        refine ⟨17298547215940278117629977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23064729621253704156839969 17298547215940278117629977)
        ·
          refine ⟨12973910411955208588222483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17298547215940278117629977 12973910411955208588222483)
          ·
            refine ⟨19460865617932812882333725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12973910411955208588222483 19460865617932812882333725)
            ·
              refine ⟨7297824606724804830875147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19460865617932812882333725 7297824606724804830875147)
              ·
                refine ⟨10946736910087207246312721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7297824606724804830875147 10946736910087207246312721)
                ·
                  refine ⟨8210052682565405434734541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10946736910087207246312721 8210052682565405434734541)
                  ·
                    refine ⟨3078769755962027038025453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8210052682565405434734541 3078769755962027038025453)
                    ·
                      refine ⟨1154538658485760139259545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3078769755962027038025453 1154538658485760139259545)
                      ·
                        rfl

theorem cell23_2248456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_2248456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248456 prefixEnd_2248456 := by exact prefixLift 2248456
  have htrace : WordTrace (prefixWord ++ tailWord_2248456) baseStart_2248456 baseEnd_2248456 := by
    simpa [prefixWord, tailWord_2248456, baseEnd_2248456] using wordTrace_append hprefix tailTrace_2248456
  have hstable : (prefixWord ++ tailWord_2248456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248456).length < 2 ^ (prefixWord ++ tailWord_2248456).sum := by decide
  have hdescent : baseEnd_2248456 < baseStart_2248456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248459 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 4, 5]
def baseStart_2248459 : Nat := 118140960795 + 2248459 * 2 ^ 59
def prefixEnd_2248459 : Nat := 4983230072969 + 3 ^ 40 * 2248459 * 2
def baseEnd_2248459 : Nat := 384846732975907875840677

theorem tailTrace_2248459 : CollatzResearch.WordTrace tailWord_2248459 prefixEnd_2248459 384846732975907875840677 := by
  unfold tailWord_2248459
  simp only [CollatzResearch.WordTrace]
  refine ⟨82008036961224524070012431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54672024640816349380008287 82008036961224524070012431)
  ·
    refine ⟨123012055441836786105018647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82008036961224524070012431 123012055441836786105018647)
    ·
      refine ⟨184518083162755179157527971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123012055441836786105018647 184518083162755179157527971)
      ·
        refine ⟨276777124744132768736291957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184518083162755179157527971 276777124744132768736291957)
        ·
          refine ⟨25947855444762447069027371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 276777124744132768736291957 25947855444762447069027371)
          ·
            refine ⟨38921783167143670603541057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25947855444762447069027371 38921783167143670603541057)
            ·
              refine ⟨29191337375357752952655793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38921783167143670603541057 29191337375357752952655793)
              ·
                refine ⟨21893503031518314714491845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29191337375357752952655793 21893503031518314714491845)
                ·
                  refine ⟨4105031818409684008967221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21893503031518314714491845 4105031818409684008967221)
                  ·
                    refine ⟨384846732975907875840677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4105031818409684008967221 384846732975907875840677)
                    ·
                      rfl

theorem cell23_2248459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 5].length) (baseStart_2248459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248459 prefixEnd_2248459 := by exact prefixLift 2248459
  have htrace : WordTrace (prefixWord ++ tailWord_2248459) baseStart_2248459 baseEnd_2248459 := by
    simpa [prefixWord, tailWord_2248459, baseEnd_2248459] using wordTrace_append hprefix tailTrace_2248459
  have hstable : (prefixWord ++ tailWord_2248459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248459).length < 2 ^ (prefixWord ++ tailWord_2248459).sum := by decide
  have hdescent : baseEnd_2248459 < baseStart_2248459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248478 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2248478 : Nat := 118140960795 + 2248478 * 2 ^ 59
def prefixEnd_2248478 : Nat := 4983230072969 + 3 ^ 40 * 2248478 * 2
def baseEnd_2248478 : Nat := 1154549955060159053184445

theorem tailTrace_2248478 : CollatzResearch.WordTrace tailWord_2248478 prefixEnd_2248478 1154549955060159053184445 := by
  unfold tailWord_2248478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251091243519461289369261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54672486632103793543302725 10251091243519461289369261)
  ·
    refine ⟨3844159216319797983513473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10251091243519461289369261 3844159216319797983513473)
    ·
      refine ⟨2883119412239848487635105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3844159216319797983513473 2883119412239848487635105)
      ·
        refine ⟨2162339559179886365726329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2883119412239848487635105 2162339559179886365726329)
        ·
          refine ⟨1621754669384914774294747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2162339559179886365726329 1621754669384914774294747)
          ·
            refine ⟨2432632004077372161442121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621754669384914774294747 2432632004077372161442121)
            ·
              refine ⟨1824474003058029121081591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2432632004077372161442121 1824474003058029121081591)
              ·
                refine ⟨2736711004587043681622387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824474003058029121081591 2736711004587043681622387)
                ·
                  refine ⟨4105066506880565522433581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736711004587043681622387 4105066506880565522433581)
                  ·
                    refine ⟨1539399940080212070912593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4105066506880565522433581 1539399940080212070912593)
                    ·
                      refine ⟨1154549955060159053184445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539399940080212070912593 1154549955060159053184445)
                      ·
                        rfl

theorem cell23_2248478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2248478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248478 prefixEnd_2248478 := by exact prefixLift 2248478
  have htrace : WordTrace (prefixWord ++ tailWord_2248478) baseStart_2248478 baseEnd_2248478 := by
    simpa [prefixWord, tailWord_2248478, baseEnd_2248478] using wordTrace_append hprefix tailTrace_2248478
  have hstable : (prefixWord ++ tailWord_2248478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248478).length < 2 ^ (prefixWord ++ tailWord_2248478).sum := by decide
  have hdescent : baseEnd_2248478 < baseStart_2248478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248559 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_2248559 : Nat := 118140960795 + 2248559 * 2 ^ 59
def prefixEnd_2248559 : Nat := 4983230072969 + 3 ^ 40 * 2248559 * 2
def baseEnd_2248559 : Nat := 1154591546993173236271571

theorem tailTrace_2248559 : CollatzResearch.WordTrace tailWord_2248559 prefixEnd_2248559 1154591546993173236271571 := by
  unfold tailWord_2248559
  simp only [CollatzResearch.WordTrace]
  refine ⟨82011684260862241148652731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54674456173908160765768487 82011684260862241148652731)
  ·
    refine ⟨123017526391293361722979097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82011684260862241148652731 123017526391293361722979097)
    ·
      refine ⟨92263144793470021292234323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123017526391293361722979097 92263144793470021292234323)
      ·
        refine ⟨138394717190205031938351485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92263144793470021292234323 138394717190205031938351485)
        ·
          refine ⟨51898018946326886976881807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138394717190205031938351485 51898018946326886976881807)
          ·
            refine ⟨77847028419490330465322711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51898018946326886976881807 77847028419490330465322711)
            ·
              refine ⟨116770542629235495697984067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77847028419490330465322711 116770542629235495697984067)
              ·
                refine ⟨175155813943853243546976101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116770542629235495697984067 175155813943853243546976101)
                ·
                  refine ⟨32841715114472483165058019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175155813943853243546976101 32841715114472483165058019)
                  ·
                    refine ⟨49262572671708724747587029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32841715114472483165058019 49262572671708724747587029)
                    ·
                      refine ⟨1154591546993173236271571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49262572671708724747587029 1154591546993173236271571)
                      ·
                        rfl

theorem cell23_2248559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_2248559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248559 prefixEnd_2248559 := by exact prefixLift 2248559
  have htrace : WordTrace (prefixWord ++ tailWord_2248559) baseStart_2248559 baseEnd_2248559 := by
    simpa [prefixWord, tailWord_2248559, baseEnd_2248559] using wordTrace_append hprefix tailTrace_2248559
  have hstable : (prefixWord ++ tailWord_2248559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248559).length < 2 ^ (prefixWord ++ tailWord_2248559).sum := by decide
  have hdescent : baseEnd_2248559 < baseStart_2248559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248573 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_2248573 : Nat := 118140960795 + 2248573 * 2 ^ 59
def prefixEnd_2248573 : Nat := 4983230072969 + 3 ^ 40 * 2248573 * 2
def baseEnd_2248573 : Nat := 1154598735722336181496507

theorem tailTrace_2248573 : CollatzResearch.WordTrace tailWord_2248573 prefixEnd_2248573 1154598735722336181496507 := by
  unfold tailWord_2248573
  simp only [CollatzResearch.WordTrace]
  refine ⟨82012194882811521539662373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54674796588541014359774915 82012194882811521539662373)
  ·
    refine ⟨15377286540527160288686695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82012194882811521539662373 15377286540527160288686695)
    ·
      refine ⟨23065929810790740433030043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15377286540527160288686695 23065929810790740433030043)
      ·
        refine ⟨34598894716186110649545065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23065929810790740433030043 34598894716186110649545065)
        ·
          refine ⟨25949171037139582987158799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34598894716186110649545065 25949171037139582987158799)
          ·
            refine ⟨38923756555709374480738199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25949171037139582987158799 38923756555709374480738199)
            ·
              refine ⟨58385634833564061721107299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38923756555709374480738199 58385634833564061721107299)
              ·
                refine ⟨87578452250346092581660949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58385634833564061721107299 87578452250346092581660949)
                ·
                  refine ⟨4105239949234973089765357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87578452250346092581660949 4105239949234973089765357)
                  ·
                    refine ⟨1539464980963114908662009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4105239949234973089765357 1539464980963114908662009)
                    ·
                      refine ⟨1154598735722336181496507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539464980963114908662009 1154598735722336181496507)
                      ·
                        rfl

theorem cell23_2248573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_2248573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248573 prefixEnd_2248573 := by exact prefixLift 2248573
  have htrace : WordTrace (prefixWord ++ tailWord_2248573) baseStart_2248573 baseEnd_2248573 := by
    simpa [prefixWord, tailWord_2248573, baseEnd_2248573] using wordTrace_append hprefix tailTrace_2248573
  have hstable : (prefixWord ++ tailWord_2248573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248573).length < 2 ^ (prefixWord ++ tailWord_2248573).sum := by decide
  have hdescent : baseEnd_2248573 < baseStart_2248573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248583 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 3, 5]
def baseStart_2248583 : Nat := 118140960795 + 2248583 * 2 ^ 59
def prefixEnd_2248583 : Nat := 4983230072969 + 3 ^ 40 * 2248583 * 2
def baseEnd_2248583 : Nat := 384867956842960380790487

theorem tailTrace_2248583 : CollatzResearch.WordTrace tailWord_2248583 prefixEnd_2248583 384867956842960380790487 := by
  unfold tailWord_2248583
  simp only [CollatzResearch.WordTrace]
  refine ⟨82012559612775293247526403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54675039741850195498350935 82012559612775293247526403)
  ·
    refine ⟨123018839419162939871289605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82012559612775293247526403 123018839419162939871289605)
    ·
      refine ⟨23066032391093051225866801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123018839419162939871289605 23066032391093051225866801)
      ·
        refine ⟨17299524293319788419400101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23066032391093051225866801 17299524293319788419400101)
        ·
          refine ⟨3243660804997460328637519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17299524293319788419400101 3243660804997460328637519)
          ·
            refine ⟨4865491207496190492956279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243660804997460328637519 4865491207496190492956279)
            ·
              refine ⟨7298236811244285739434419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865491207496190492956279 7298236811244285739434419)
              ·
                refine ⟨10947355216866428609151629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7298236811244285739434419 10947355216866428609151629)
                ·
                  refine ⟨4105258206324910728431861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10947355216866428609151629 4105258206324910728431861)
                  ·
                    refine ⟨384867956842960380790487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4105258206324910728431861 384867956842960380790487)
                    ·
                      rfl

theorem cell23_2248583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_2248583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248583 prefixEnd_2248583 := by exact prefixLift 2248583
  have htrace : WordTrace (prefixWord ++ tailWord_2248583) baseStart_2248583 baseEnd_2248583 := by
    simpa [prefixWord, tailWord_2248583, baseEnd_2248583] using wordTrace_append hprefix tailTrace_2248583
  have hstable : (prefixWord ++ tailWord_2248583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248583).length < 2 ^ (prefixWord ++ tailWord_2248583).sum := by decide
  have hdescent : baseEnd_2248583 < baseStart_2248583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248633 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2248633 : Nat := 118140960795 + 2248633 * 2 ^ 59
def prefixEnd_2248633 : Nat := 4983230072969 + 3 ^ 40 * 2248633 * 2
def baseEnd_2248633 : Nat := 1154629544561605946746231

theorem tailTrace_2248633 : CollatzResearch.WordTrace tailWord_2248633 prefixEnd_2248633 1154629544561605946746231 := by
  unfold tailWord_2248633
  simp only [CollatzResearch.WordTrace]
  refine ⟨82014383262594151786846553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54676255508396101191231035 82014383262594151786846553)
  ·
    refine ⟨61510787446945613840134915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82014383262594151786846553 61510787446945613840134915)
    ·
      refine ⟨92266181170418420760202373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61510787446945613840134915 92266181170418420760202373)
      ·
        refine ⟨17299908969453453892537945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92266181170418420760202373 17299908969453453892537945)
        ·
          refine ⟨12974931727090090419403459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17299908969453453892537945 12974931727090090419403459)
          ·
            refine ⟨19462397590635135629105189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12974931727090090419403459 19462397590635135629105189)
            ·
              refine ⟨3649199548244087930457223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19462397590635135629105189 3649199548244087930457223)
              ·
                refine ⟨5473799322366131895685835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649199548244087930457223 5473799322366131895685835)
                ·
                  refine ⟨8210698983549197843528753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5473799322366131895685835 8210698983549197843528753)
                  ·
                    refine ⟨6158024237661898382646565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8210698983549197843528753 6158024237661898382646565)
                    ·
                      refine ⟨1154629544561605946746231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6158024237661898382646565 1154629544561605946746231)
                      ·
                        rfl

theorem cell23_2248633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2248633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248633 prefixEnd_2248633 := by exact prefixLift 2248633
  have htrace : WordTrace (prefixWord ++ tailWord_2248633) baseStart_2248633 baseEnd_2248633 := by
    simpa [prefixWord, tailWord_2248633, baseEnd_2248633] using wordTrace_append hprefix tailTrace_2248633
  have hstable : (prefixWord ++ tailWord_2248633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248633).length < 2 ^ (prefixWord ++ tailWord_2248633).sum := by decide
  have hdescent : baseEnd_2248633 < baseStart_2248633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248637 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_2248637 : Nat := 118140960795 + 2248637 * 2 ^ 59
def prefixEnd_2248637 : Nat := 4983230072969 + 3 ^ 40 * 2248637 * 2
def baseEnd_2248637 : Nat := 1154631598484223931096213

theorem tailTrace_2248637 : CollatzResearch.WordTrace tailWord_2248637 prefixEnd_2248637 1154631598484223931096213 := by
  unfold tailWord_2248637
  simp only [CollatzResearch.WordTrace]
  refine ⟨82014529154579660469992165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54676352769719773646661443 82014529154579660469992165)
  ·
    refine ⟨15377724216483686338123531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82014529154579660469992165 15377724216483686338123531)
    ·
      refine ⟨23066586324725529507185297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15377724216483686338123531 23066586324725529507185297)
      ·
        refine ⟨17299939743544147130388973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23066586324725529507185297 17299939743544147130388973)
        ·
          refine ⟨6487477403829055173895865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17299939743544147130388973 6487477403829055173895865)
          ·
            refine ⟨4865608052871791380421899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6487477403829055173895865 4865608052871791380421899)
            ·
              refine ⟨7298412079307687070632849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865608052871791380421899 7298412079307687070632849)
              ·
                refine ⟨5473809059480765302974637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7298412079307687070632849 5473809059480765302974637)
                ·
                  refine ⟨2052678397305286988615489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5473809059480765302974637 2052678397305286988615489)
                  ·
                    refine ⟨1539508797978965241461617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052678397305286988615489 1539508797978965241461617)
                    ·
                      refine ⟨1154631598484223931096213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539508797978965241461617 1154631598484223931096213)
                      ·
                        rfl

theorem cell23_2248637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_2248637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248637 prefixEnd_2248637 := by exact prefixLift 2248637
  have htrace : WordTrace (prefixWord ++ tailWord_2248637) baseStart_2248637 baseEnd_2248637 := by
    simpa [prefixWord, tailWord_2248637, baseEnd_2248637] using wordTrace_append hprefix tailTrace_2248637
  have hstable : (prefixWord ++ tailWord_2248637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248637).length < 2 ^ (prefixWord ++ tailWord_2248637).sum := by decide
  have hdescent : baseEnd_2248637 < baseStart_2248637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248654 : List Nat := [4, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_2248654 : Nat := 118140960795 + 2248654 * 2 ^ 59
def prefixEnd_2248654 : Nat := 4983230072969 + 3 ^ 40 * 2248654 * 2
def baseEnd_2248654 : Nat := 1154640327655350364583635

theorem tailTrace_2248654 : CollatzResearch.WordTrace tailWord_2248654 prefixEnd_2248654 1154640327655350364583635 := by
  unfold tailWord_2248654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251893649439759046670127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54676766130345381582240677 10251893649439759046670127)
  ·
    refine ⟨15377840474159638570005191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10251893649439759046670127 15377840474159638570005191)
    ·
      refine ⟨23066760711239457855007787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15377840474159638570005191 23066760711239457855007787)
      ·
        refine ⟨34600141066859186782511681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23066760711239457855007787 34600141066859186782511681)
        ·
          refine ⟨25950105800144390086883761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34600141066859186782511681 25950105800144390086883761)
          ·
            refine ⟨19462579350108292565162821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25950105800144390086883761 19462579350108292565162821)
            ·
              refine ⟨3649233628145304855968029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19462579350108292565162821 3649233628145304855968029)
              ·
                refine ⟨1368462610554489320988011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3649233628145304855968029 1368462610554489320988011)
                ·
                  refine ⟨2052693915831733981482017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368462610554489320988011 2052693915831733981482017)
                  ·
                    refine ⟨1539520436873800486111513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052693915831733981482017 1539520436873800486111513)
                    ·
                      refine ⟨1154640327655350364583635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539520436873800486111513 1154640327655350364583635)
                      ·
                        rfl

theorem cell23_2248654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_2248654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248654 prefixEnd_2248654 := by exact prefixLift 2248654
  have htrace : WordTrace (prefixWord ++ tailWord_2248654) baseStart_2248654 baseEnd_2248654 := by
    simpa [prefixWord, tailWord_2248654, baseEnd_2248654] using wordTrace_append hprefix tailTrace_2248654
  have hstable : (prefixWord ++ tailWord_2248654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248654).length < 2 ^ (prefixWord ++ tailWord_2248654).sum := by decide
  have hdescent : baseEnd_2248654 < baseStart_2248654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248687 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 2, 1, 3]
def baseStart_2248687 : Nat := 118140960795 + 2248687 * 2 ^ 59
def prefixEnd_2248687 : Nat := 4983230072969 + 3 ^ 40 * 2248687 * 2
def baseEnd_2248687 : Nat := 1154657272516948735470983

theorem tailTrace_2248687 : CollatzResearch.WordTrace tailWord_2248687 prefixEnd_2248687 1154657272516948735470983 := by
  unfold tailWord_2248687
  simp only [CollatzResearch.WordTrace]
  refine ⟨82016352804398519009312315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54677568536265679339541543 82016352804398519009312315)
  ·
    refine ⟨123024529206597778513968473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82016352804398519009312315 123024529206597778513968473)
    ·
      refine ⟨92268396904948333885476355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123024529206597778513968473 92268396904948333885476355)
      ·
        refine ⟨138402595357422500828214533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92268396904948333885476355 138402595357422500828214533)
        ·
          refine ⟨25950486629516718905290225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138402595357422500828214533 25950486629516718905290225)
          ·
            refine ⟨19462864972137539178967669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25950486629516718905290225 19462864972137539178967669)
            ·
              refine ⟨1824643591137894298028219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19462864972137539178967669 1824643591137894298028219)
              ·
                refine ⟨2736965386706841447042329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824643591137894298028219 2736965386706841447042329)
                ·
                  refine ⟨2052724040030131085281747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2736965386706841447042329 2052724040030131085281747)
                  ·
                    refine ⟨3079086060045196627922621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052724040030131085281747 3079086060045196627922621)
                    ·
                      refine ⟨1154657272516948735470983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3079086060045196627922621 1154657272516948735470983)
                      ·
                        rfl

theorem cell23_2248687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 1, 3].length) (baseStart_2248687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248687 prefixEnd_2248687 := by exact prefixLift 2248687
  have htrace : WordTrace (prefixWord ++ tailWord_2248687) baseStart_2248687 baseEnd_2248687 := by
    simpa [prefixWord, tailWord_2248687, baseEnd_2248687] using wordTrace_append hprefix tailTrace_2248687
  have hstable : (prefixWord ++ tailWord_2248687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248687).length < 2 ^ (prefixWord ++ tailWord_2248687).sum := by decide
  have hdescent : baseEnd_2248687 < baseStart_2248687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248697 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 1, 3, 2]
def baseStart_2248697 : Nat := 118140960795 + 2248697 * 2 ^ 59
def prefixEnd_2248697 : Nat := 4983230072969 + 3 ^ 40 * 2248697 * 2
def baseEnd_2248697 : Nat := 1154662407323493696345937

theorem tailTrace_2248697 : CollatzResearch.WordTrace tailWord_2248697 prefixEnd_2248697 1154662407323493696345937 := by
  unfold tailWord_2248697
  simp only [CollatzResearch.WordTrace]
  refine ⟨82016717534362290717176345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54677811689574860478117563 82016717534362290717176345)
  ·
    refine ⟨61512538150771718037882259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82016717534362290717176345 61512538150771718037882259)
    ·
      refine ⟨92268807226157577056823389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61512538150771718037882259 92268807226157577056823389)
      ·
        refine ⟨34600802709809091396308771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92268807226157577056823389 34600802709809091396308771)
        ·
          refine ⟨51901204064713637094463157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34600802709809091396308771 51901204064713637094463157)
          ·
            refine ⟨4865737881066903477605921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51901204064713637094463157 4865737881066903477605921)
            ·
              refine ⟨3649303410800177608204441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4865737881066903477605921 3649303410800177608204441)
              ·
                refine ⟨2736977558100133206153331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649303410800177608204441 2736977558100133206153331)
                ·
                  refine ⟨4105466337150199809229997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736977558100133206153331 4105466337150199809229997)
                  ·
                    refine ⟨1539549876431324928461249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4105466337150199809229997 1539549876431324928461249)
                    ·
                      refine ⟨1154662407323493696345937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539549876431324928461249 1154662407323493696345937)
                      ·
                        rfl

theorem cell23_2248697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_2248697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248697 prefixEnd_2248697 := by exact prefixLift 2248697
  have htrace : WordTrace (prefixWord ++ tailWord_2248697) baseStart_2248697 baseEnd_2248697 := by
    simpa [prefixWord, tailWord_2248697, baseEnd_2248697] using wordTrace_append hprefix tailTrace_2248697
  have hstable : (prefixWord ++ tailWord_2248697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248697).length < 2 ^ (prefixWord ++ tailWord_2248697).sum := by decide
  have hdescent : baseEnd_2248697 < baseStart_2248697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248800 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 1, 6, 2]
def baseStart_2248800 : Nat := 118140960795 + 2248800 * 2 ^ 59
def prefixEnd_2248800 : Nat := 4983230072969 + 3 ^ 40 * 2248800 * 2
def baseEnd_2248800 : Nat := 1154715295830906793357963

theorem tailTrace_2248800 : CollatzResearch.WordTrace tailWord_2248800 prefixEnd_2248800 1154715295830906793357963 := by
  unfold tailWord_2248800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41010237126494569654087927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54680316168659426205450569 41010237126494569654087927)
  ·
    refine ⟨61515355689741854481131891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41010237126494569654087927 61515355689741854481131891)
    ·
      refine ⟨92273033534612781721697837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61515355689741854481131891 92273033534612781721697837)
      ·
        refine ⟨34602387575479793145636689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92273033534612781721697837 34602387575479793145636689)
        ·
          refine ⟨25951790681609844859227517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34602387575479793145636689 25951790681609844859227517)
          ·
            refine ⟨9731921505603691822210319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25951790681609844859227517 9731921505603691822210319)
            ·
              refine ⟨14597882258405537733315479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9731921505603691822210319 14597882258405537733315479)
              ·
                refine ⟨21896823387608306599973219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14597882258405537733315479 21896823387608306599973219)
                ·
                  refine ⟨32845235081412459899959829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21896823387608306599973219 32845235081412459899959829)
                  ·
                    refine ⟨1539620394441209057810617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32845235081412459899959829 1539620394441209057810617)
                    ·
                      refine ⟨1154715295830906793357963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539620394441209057810617 1154715295830906793357963)
                      ·
                        rfl

theorem cell23_2248800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_2248800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248800 prefixEnd_2248800 := by exact prefixLift 2248800
  have htrace : WordTrace (prefixWord ++ tailWord_2248800) baseStart_2248800 baseEnd_2248800 := by
    simpa [prefixWord, tailWord_2248800, baseEnd_2248800] using wordTrace_append hprefix tailTrace_2248800
  have hstable : (prefixWord ++ tailWord_2248800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248800).length < 2 ^ (prefixWord ++ tailWord_2248800).sum := by decide
  have hdescent : baseEnd_2248800 < baseStart_2248800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248840 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 8]
def baseStart_2248840 : Nat := 118140960795 + 2248840 * 2 ^ 59
def prefixEnd_2248840 : Nat := 4983230072969 + 3 ^ 40 * 2248840 * 2
def baseEnd_2248840 : Nat := 128303981673009626317531

theorem tailTrace_2248840 : CollatzResearch.WordTrace tailWord_2248840 prefixEnd_2248840 128303981673009626317531 := by
  unfold tailWord_2248840
  simp only [CollatzResearch.WordTrace]
  refine ⟨41010966586422113069815987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54681288781896150759754649 41010966586422113069815987)
  ·
    refine ⟨61516449879633169604723981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41010966586422113069815987 61516449879633169604723981)
    ·
      refine ⟨23068668704862438601771493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61516449879633169604723981 23068668704862438601771493)
      ·
        refine ⟨4325375382161707237832155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23068668704862438601771493 4325375382161707237832155)
        ·
          refine ⟨6488063073242560856748233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325375382161707237832155 6488063073242560856748233)
          ·
            refine ⟨4866047304931920642561175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6488063073242560856748233 4866047304931920642561175)
            ·
              refine ⟨7299070957397880963841763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866047304931920642561175 7299070957397880963841763)
              ·
                refine ⟨10948606436096821445762645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7299070957397880963841763 10948606436096821445762645)
                ·
                  refine ⟨128303981673009626317531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10948606436096821445762645 128303981673009626317531)
                  ·
                    rfl

theorem cell23_2248840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 8].length) (baseStart_2248840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248840 prefixEnd_2248840 := by exact prefixLift 2248840
  have htrace : WordTrace (prefixWord ++ tailWord_2248840) baseStart_2248840 baseEnd_2248840 := by
    simpa [prefixWord, tailWord_2248840, baseEnd_2248840] using wordTrace_append hprefix tailTrace_2248840
  have hstable : (prefixWord ++ tailWord_2248840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248840).length < 2 ^ (prefixWord ++ tailWord_2248840).sum := by decide
  have hdescent : baseEnd_2248840 < baseStart_2248840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248883 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 3, 6]
def baseStart_2248883 : Nat := 118140960795 + 2248883 * 2 ^ 59
def prefixEnd_2248883 : Nat := 4983230072969 + 3 ^ 40 * 2248883 * 2
def baseEnd_2248883 : Nat := 384919304908409989540027

theorem tailTrace_2248883 : CollatzResearch.WordTrace tailWord_2248883 prefixEnd_2248883 384919304908409989540027 := by
  unfold tailWord_2248883
  simp only [CollatzResearch.WordTrace]
  refine ⟨82023501511688444483447303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54682334341125629655631535 82023501511688444483447303)
  ·
    refine ⟨123035252267532666725170955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82023501511688444483447303 123035252267532666725170955)
    ·
      refine ⟨184552878401299000087756433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123035252267532666725170955 184552878401299000087756433)
      ·
        refine ⟨138414658800974250065817325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184552878401299000087756433 138414658800974250065817325)
        ·
          refine ⟨51905497050365343774681497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138414658800974250065817325 51905497050365343774681497)
          ·
            refine ⟨38929122787774007831011123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51905497050365343774681497 38929122787774007831011123)
            ·
              refine ⟨58393684181661011746516685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38929122787774007831011123 58393684181661011746516685)
              ·
                refine ⟨21897631568122879404943757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58393684181661011746516685 21897631568122879404943757)
                ·
                  refine ⟨8211611838046079776853909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21897631568122879404943757 8211611838046079776853909)
                  ·
                    refine ⟨384919304908409989540027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8211611838046079776853909 384919304908409989540027)
                    ·
                      rfl

theorem cell23_2248883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 6].length) (baseStart_2248883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248883 prefixEnd_2248883 := by exact prefixLift 2248883
  have htrace : WordTrace (prefixWord ++ tailWord_2248883) baseStart_2248883 baseEnd_2248883 := by
    simpa [prefixWord, tailWord_2248883, baseEnd_2248883] using wordTrace_append hprefix tailTrace_2248883
  have hstable : (prefixWord ++ tailWord_2248883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248883).length < 2 ^ (prefixWord ++ tailWord_2248883).sum := by decide
  have hdescent : baseEnd_2248883 < baseStart_2248883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248913 : List Nat := [1, 2, 2, 1, 2, 2, 3, 10]
def baseStart_2248913 : Nat := 118140960795 + 2248913 * 2 ^ 59
def prefixEnd_2248913 : Nat := 4983230072969 + 3 ^ 40 * 2248913 * 2
def baseEnd_2248913 : Nat := 42769382190550550046109

theorem tailTrace_2248913 : CollatzResearch.WordTrace tailWord_2248913 prefixEnd_2248913 42769382190550550046109 := by
  unfold tailWord_2248913
  simp only [CollatzResearch.WordTrace]
  refine ⟨82024595701579759607039393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54683063801053173071359595 82024595701579759607039393)
  ·
    refine ⟨61518446776184819705279545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82024595701579759607039393 61518446776184819705279545)
    ·
      refine ⟨46138835082138614778959659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61518446776184819705279545 46138835082138614778959659)
      ·
        refine ⟨69208252623207922168439489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46138835082138614778959659 69208252623207922168439489)
        ·
          refine ⟨51906189467405941626329617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69208252623207922168439489 51906189467405941626329617)
          ·
            refine ⟨38929642100554456219747213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51906189467405941626329617 38929642100554456219747213)
            ·
              refine ⟨14598615787707921082405205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38929642100554456219747213 14598615787707921082405205)
              ·
                refine ⟨42769382190550550046109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14598615787707921082405205 42769382190550550046109)
                ·
                  rfl

theorem cell23_2248913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 10].length) (baseStart_2248913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248913 prefixEnd_2248913 := by exact prefixLift 2248913
  have htrace : WordTrace (prefixWord ++ tailWord_2248913) baseStart_2248913 baseEnd_2248913 := by
    simpa [prefixWord, tailWord_2248913, baseEnd_2248913] using wordTrace_append hprefix tailTrace_2248913
  have hstable : (prefixWord ++ tailWord_2248913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248913).length < 2 ^ (prefixWord ++ tailWord_2248913).sum := by decide
  have hdescent : baseEnd_2248913 < baseStart_2248913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248920 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2248920 : Nat := 118140960795 + 2248920 * 2 ^ 59
def prefixEnd_2248920 : Nat := 4983230072969 + 3 ^ 40 * 2248920 * 2
def baseEnd_2248920 : Nat := 1154776913509446323857411

theorem tailTrace_2248920 : CollatzResearch.WordTrace tailWord_2248920 prefixEnd_2248920 1154776913509446323857411 := by
  unfold tailWord_2248920
  simp only [CollatzResearch.WordTrace]
  refine ⟨41012425506277199901272107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54683234008369599868362809 41012425506277199901272107)
  ·
    refine ⟨61518638259415799851908161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41012425506277199901272107 61518638259415799851908161)
    ·
      refine ⟨46138978694561849888931121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61518638259415799851908161 46138978694561849888931121)
      ·
        refine ⟨34604234020921387416698341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46138978694561849888931121 34604234020921387416698341)
        ·
          refine ⟨6488293878922760140630939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34604234020921387416698341 6488293878922760140630939)
          ·
            refine ⟨9732440818384140210946409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488293878922760140630939 9732440818384140210946409)
            ·
              refine ⟨7299330613788105158209807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9732440818384140210946409 7299330613788105158209807)
              ·
                refine ⟨10948995920682157737314711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7299330613788105158209807 10948995920682157737314711)
                ·
                  refine ⟨16423493881023236605972067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10948995920682157737314711 16423493881023236605972067)
                  ·
                    refine ⟨24635240821534854908958101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16423493881023236605972067 24635240821534854908958101)
                    ·
                      refine ⟨1154776913509446323857411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24635240821534854908958101 1154776913509446323857411)
                      ·
                        rfl

theorem cell23_2248920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2248920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248920 prefixEnd_2248920 := by exact prefixLift 2248920
  have htrace : WordTrace (prefixWord ++ tailWord_2248920) baseStart_2248920 baseEnd_2248920 := by
    simpa [prefixWord, tailWord_2248920, baseEnd_2248920] using wordTrace_append hprefix tailTrace_2248920
  have hstable : (prefixWord ++ tailWord_2248920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248920).length < 2 ^ (prefixWord ++ tailWord_2248920).sum := by decide
  have hdescent : baseEnd_2248920 < baseStart_2248920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248941 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2248941 : Nat := 118140960795 + 2248941 * 2 ^ 59
def prefixEnd_2248941 : Nat := 4983230072969 + 3 ^ 40 * 2248941 * 2
def baseEnd_2248941 : Nat := 1154787696603190741694815

theorem tailTrace_2248941 : CollatzResearch.WordTrace tailWord_2248941 prefixEnd_2248941 1154787696603190741694815 := by
  unfold tailWord_2248941
  simp only [CollatzResearch.WordTrace]
  refine ⟨82025616945478320389058677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54683744630318880259372451 82025616945478320389058677)
  ·
    refine ⟨7689901588638592536474251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82025616945478320389058677 7689901588638592536474251)
    ·
      refine ⟨11534852382957888804711377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7689901588638592536474251 11534852382957888804711377)
      ·
        refine ⟨8651139287218416603533533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11534852382957888804711377 8651139287218416603533533)
        ·
          refine ⟨3244177232706906226325075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8651139287218416603533533 3244177232706906226325075)
          ·
            refine ⟨4866265849060359339487613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244177232706906226325075 4866265849060359339487613)
            ·
              refine ⟨1824849693397634752307855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4866265849060359339487613 1824849693397634752307855)
              ·
                refine ⟨2737274540096452128461783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824849693397634752307855 2737274540096452128461783)
                ·
                  refine ⟨4105911810144678192692675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737274540096452128461783 4105911810144678192692675)
                  ·
                    refine ⟨6158867715217017289039013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4105911810144678192692675 6158867715217017289039013)
                    ·
                      refine ⟨1154787696603190741694815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6158867715217017289039013 1154787696603190741694815)
                      ·
                        rfl

theorem cell23_2248941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2248941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248941 prefixEnd_2248941 := by exact prefixLift 2248941
  have htrace : WordTrace (prefixWord ++ tailWord_2248941) baseStart_2248941 baseEnd_2248941 := by
    simpa [prefixWord, tailWord_2248941, baseEnd_2248941] using wordTrace_append hprefix tailTrace_2248941
  have hstable : (prefixWord ++ tailWord_2248941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248941).length < 2 ^ (prefixWord ++ tailWord_2248941).sum := by decide
  have hdescent : baseEnd_2248941 < baseStart_2248941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248957 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_2248957 : Nat := 118140960795 + 2248957 * 2 ^ 59
def prefixEnd_2248957 : Nat := 4983230072969 + 3 ^ 40 * 2248957 * 2
def baseEnd_2248957 : Nat := 1154795912293662679094741

theorem tailTrace_2248957 : CollatzResearch.WordTrace tailWord_2248957 prefixEnd_2248957 1154795912293662679094741 := by
  unfold tailWord_2248957
  simp only [CollatzResearch.WordTrace]
  refine ⟨82026200513420355121641125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54684133675613570081094083 82026200513420355121641125)
  ·
    refine ⟨15379912596266316585307711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82026200513420355121641125 15379912596266316585307711)
    ·
      refine ⟨23069868894399474877961567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15379912596266316585307711 23069868894399474877961567)
      ·
        refine ⟨34604803341599212316942351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23069868894399474877961567 34604803341599212316942351)
        ·
          refine ⟨51907205012398818475413527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34604803341599212316942351 51907205012398818475413527)
          ·
            refine ⟨77860807518598227713120291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51907205012398818475413527 77860807518598227713120291)
            ·
              refine ⟨116791211277897341569680437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77860807518598227713120291 116791211277897341569680437)
              ·
                refine ⟨10949176057302875772157541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116791211277897341569680437 10949176057302875772157541)
                ·
                  refine ⟨2052970510744289207279539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10949176057302875772157541 2052970510744289207279539)
                  ·
                    refine ⟨3079455766116433810919309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052970510744289207279539 3079455766116433810919309)
                    ·
                      refine ⟨1154795912293662679094741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3079455766116433810919309 1154795912293662679094741)
                      ·
                        rfl

theorem cell23_2248957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_2248957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248957 prefixEnd_2248957 := by exact prefixLift 2248957
  have htrace : WordTrace (prefixWord ++ tailWord_2248957) baseStart_2248957 baseEnd_2248957 := by
    simpa [prefixWord, tailWord_2248957, baseEnd_2248957] using wordTrace_append hprefix tailTrace_2248957
  have hstable : (prefixWord ++ tailWord_2248957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248957).length < 2 ^ (prefixWord ++ tailWord_2248957).sum := by decide
  have hdescent : baseEnd_2248957 < baseStart_2248957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248958 : List Nat := [4, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_2248958 : Nat := 118140960795 + 2248958 * 2 ^ 59
def prefixEnd_2248958 : Nat := 4983230072969 + 3 ^ 40 * 2248958 * 2
def baseEnd_2248958 : Nat := 1154796425774317175182237

theorem tailTrace_2248958 : CollatzResearch.WordTrace tailWord_2248958 prefixEnd_2248958 1154796425774317175182237 := by
  unfold tailWord_2248958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253279623302091536553441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54684157990944488194951685 10253279623302091536553441)
  ·
    refine ⟨7689959717476568652415081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10253279623302091536553441 7689959717476568652415081)
    ·
      refine ⟨5767469788107426489311311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7689959717476568652415081 5767469788107426489311311)
      ·
        refine ⟨8651204682161139733966967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767469788107426489311311 8651204682161139733966967)
        ·
          refine ⟨12976807023241709600950451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8651204682161139733966967 12976807023241709600950451)
          ·
            refine ⟨19465210534862564401425677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12976807023241709600950451 19465210534862564401425677)
            ·
              refine ⟨7299453950573461650534629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19465210534862564401425677 7299453950573461650534629)
              ·
                refine ⟨1368647615732524059475243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7299453950573461650534629 1368647615732524059475243)
                ·
                  refine ⟨2052971423598786089212865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368647615732524059475243 2052971423598786089212865)
                  ·
                    refine ⟨1539728567699089566909649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052971423598786089212865 1539728567699089566909649)
                    ·
                      refine ⟨1154796425774317175182237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539728567699089566909649 1154796425774317175182237)
                      ·
                        rfl

theorem cell23_2248958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_2248958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248958 prefixEnd_2248958 := by exact prefixLift 2248958
  have htrace : WordTrace (prefixWord ++ tailWord_2248958) baseStart_2248958 baseEnd_2248958 := by
    simpa [prefixWord, tailWord_2248958, baseEnd_2248958] using wordTrace_append hprefix tailTrace_2248958
  have hstable : (prefixWord ++ tailWord_2248958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248958).length < 2 ^ (prefixWord ++ tailWord_2248958).sum := by decide
  have hdescent : baseEnd_2248958 < baseStart_2248958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248964 : List Nat := [2, 3, 2, 2, 4, 1, 1, 8]
def baseStart_2248964 : Nat := 118140960795 + 2248964 * 2 ^ 59
def prefixEnd_2248964 : Nat := 4983230072969 + 3 ^ 40 * 2248964 * 2
def baseEnd_2248964 : Nat := 42770352098453487100267

theorem tailTrace_2248964 : CollatzResearch.WordTrace tailWord_2248964 prefixEnd_2248964 42770352098453487100267 := by
  unfold tailWord_2248964
  simp only [CollatzResearch.WordTrace]
  refine ⟨41013227912197497658572973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54684303882929996878097297 41013227912197497658572973)
  ·
    refine ⟨15379960467074061621964865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41013227912197497658572973 15379960467074061621964865)
    ·
      refine ⟨11534970350305546216473649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15379960467074061621964865 11534970350305546216473649)
      ·
        refine ⟨8651227762729159662355237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11534970350305546216473649 8651227762729159662355237)
        ·
          refine ⟨1622105205511717436691607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8651227762729159662355237 1622105205511717436691607)
          ·
            refine ⟨2433157808267576155037411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622105205511717436691607 2433157808267576155037411)
            ·
              refine ⟨3649736712401364232556117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433157808267576155037411 3649736712401364232556117)
              ·
                refine ⟨42770352098453487100267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3649736712401364232556117 42770352098453487100267)
                ·
                  rfl

theorem cell23_2248964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 8].length) (baseStart_2248964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248964 prefixEnd_2248964 := by exact prefixLift 2248964
  have htrace : WordTrace (prefixWord ++ tailWord_2248964) baseStart_2248964 baseEnd_2248964 := by
    simpa [prefixWord, tailWord_2248964, baseEnd_2248964] using wordTrace_append hprefix tailTrace_2248964
  have hstable : (prefixWord ++ tailWord_2248964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248964).length < 2 ^ (prefixWord ++ tailWord_2248964).sum := by decide
  have hdescent : baseEnd_2248964 < baseStart_2248964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248974 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2248974 : Nat := 118140960795 + 2248974 * 2 ^ 59
def prefixEnd_2248974 : Nat := 4983230072969 + 3 ^ 40 * 2248974 * 2
def baseEnd_2248974 : Nat := 1154804641464789112582163

theorem tailTrace_2248974 : CollatzResearch.WordTrace tailWord_2248974 prefixEnd_2248974 1154804641464789112582163 := by
  unfold tailWord_2248974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253352569294845878126247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54684547036239178016673317 10253352569294845878126247)
  ·
    refine ⟨15380028853942268817189371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10253352569294845878126247 15380028853942268817189371)
    ·
      refine ⟨23070043280913403225784057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15380028853942268817189371 23070043280913403225784057)
      ·
        refine ⟨17302532460685052419338043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23070043280913403225784057 17302532460685052419338043)
        ·
          refine ⟨25953798691027578629007065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17302532460685052419338043 25953798691027578629007065)
          ·
            refine ⟨19465349018270683971755299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25953798691027578629007065 19465349018270683971755299)
            ·
              refine ⟨29198023527406025957632949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19465349018270683971755299 29198023527406025957632949)
              ·
                refine ⟨2737314705694314933528089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29198023527406025957632949 2737314705694314933528089)
                ·
                  refine ⟨2052986029270736200146067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737314705694314933528089 2052986029270736200146067)
                  ·
                    refine ⟨3079479043906104300219101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052986029270736200146067 3079479043906104300219101)
                    ·
                      refine ⟨1154804641464789112582163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3079479043906104300219101 1154804641464789112582163)
                      ·
                        rfl

theorem cell23_2248974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2248974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248974 prefixEnd_2248974 := by exact prefixLift 2248974
  have htrace : WordTrace (prefixWord ++ tailWord_2248974) baseStart_2248974 baseEnd_2248974 := by
    simpa [prefixWord, tailWord_2248974, baseEnd_2248974] using wordTrace_append hprefix tailTrace_2248974
  have hstable : (prefixWord ++ tailWord_2248974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248974).length < 2 ^ (prefixWord ++ tailWord_2248974).sum := by decide
  have hdescent : baseEnd_2248974 < baseStart_2248974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2248984 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 1, 3, 2]
def baseStart_2248984 : Nat := 118140960795 + 2248984 * 2 ^ 59
def prefixEnd_2248984 : Nat := 4983230072969 + 3 ^ 40 * 2248984 * 2
def baseEnd_2248984 : Nat := 1154809776271334073457117

theorem tailTrace_2248984 : CollatzResearch.WordTrace tailWord_2248984 prefixEnd_2248984 1154809776271334073457117 := by
  unfold tailWord_2248984
  simp only [CollatzResearch.WordTrace]
  refine ⟨41013592642161269366437003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54684790189548359155249337 41013592642161269366437003)
  ·
    refine ⟨61520388963241904049655505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41013592642161269366437003 61520388963241904049655505)
    ·
      refine ⟨46140291722431428037241629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61520388963241904049655505 46140291722431428037241629)
      ·
        refine ⟨17302609395911785513965611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46140291722431428037241629 17302609395911785513965611)
        ·
          refine ⟨25953914093867678270948417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17302609395911785513965611 25953914093867678270948417)
          ·
            refine ⟨19465435570400758703211313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25953914093867678270948417 19465435570400758703211313)
            ·
              refine ⟨14599076677800569027408485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19465435570400758703211313 14599076677800569027408485)
              ·
                refine ⟨2737326877087606692639091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14599076677800569027408485 2737326877087606692639091)
                ·
                  refine ⟨4105990315631410038958637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737326877087606692639091 4105990315631410038958637)
                  ·
                    refine ⟨1539746368361778764609489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4105990315631410038958637 1539746368361778764609489)
                    ·
                      refine ⟨1154809776271334073457117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539746368361778764609489 1154809776271334073457117)
                      ·
                        rfl

theorem cell23_2248984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_2248984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2248984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2248984 prefixEnd_2248984 := by exact prefixLift 2248984
  have htrace : WordTrace (prefixWord ++ tailWord_2248984) baseStart_2248984 baseEnd_2248984 := by
    simpa [prefixWord, tailWord_2248984, baseEnd_2248984] using wordTrace_append hprefix tailTrace_2248984
  have hstable : (prefixWord ++ tailWord_2248984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2248984).length < 2 ^ (prefixWord ++ tailWord_2248984).sum := by decide
  have hdescent : baseEnd_2248984 < baseStart_2248984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2248984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249057 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_2249057 : Nat := 118140960795 + 2249057 * 2 ^ 59
def prefixEnd_2249057 : Nat := 4983230072969 + 3 ^ 40 * 2249057 * 2
def baseEnd_2249057 : Nat := 1154847260359112287844281

theorem tailTrace_2249057 : CollatzResearch.WordTrace tailWord_2249057 prefixEnd_2249057 1154847260359112287844281 := by
  unfold tailWord_2249057
  simp only [CollatzResearch.WordTrace]
  refine ⟨82029847813058072200281425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54686565208705381466854283 82029847813058072200281425)
  ·
    refine ⟨61522385859793554150211069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82029847813058072200281425 61522385859793554150211069)
    ·
      refine ⟨23070894697422582806329151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61522385859793554150211069 23070894697422582806329151)
      ·
        refine ⟨34606342046133874209493727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23070894697422582806329151 34606342046133874209493727)
        ·
          refine ⟨51909513069200811314240591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34606342046133874209493727 51909513069200811314240591)
          ·
            refine ⟨77864269603801216971360887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51909513069200811314240591 77864269603801216971360887)
            ·
              refine ⟨116796404405701825457041331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77864269603801216971360887 116796404405701825457041331)
              ·
                refine ⟨175194606608552738185561997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116796404405701825457041331 175194606608552738185561997)
                ·
                  refine ⟨65697977478207276819585749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175194606608552738185561997 65697977478207276819585749)
                  ·
                    refine ⟨1539796347145483050459041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65697977478207276819585749 1539796347145483050459041)
                    ·
                      refine ⟨1154847260359112287844281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539796347145483050459041 1154847260359112287844281)
                      ·
                        rfl

theorem cell23_2249057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_2249057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249057 prefixEnd_2249057 := by exact prefixLift 2249057
  have htrace : WordTrace (prefixWord ++ tailWord_2249057) baseStart_2249057 baseEnd_2249057 := by
    simpa [prefixWord, tailWord_2249057, baseEnd_2249057] using wordTrace_append hprefix tailTrace_2249057
  have hstable : (prefixWord ++ tailWord_2249057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249057).length < 2 ^ (prefixWord ++ tailWord_2249057).sum := by decide
  have hdescent : baseEnd_2249057 < baseStart_2249057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249077 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2249077 : Nat := 118140960795 + 2249077 * 2 ^ 59
def prefixEnd_2249077 : Nat := 4983230072969 + 3 ^ 40 * 2249077 * 2
def baseEnd_2249077 : Nat := 1154857529972202209594189

theorem tailTrace_2249077 : CollatzResearch.WordTrace tailWord_2249077 prefixEnd_2249077 1154857529972202209594189 := by
  unfold tailWord_2249077
  simp only [CollatzResearch.WordTrace]
  refine ⟨82030577272985615616009485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54687051515323743744006323 82030577272985615616009485)
  ·
    refine ⟨30761466477369605856003557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82030577272985615616009485 30761466477369605856003557)
    ·
      refine ⟨5767774964506801098000667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30761466477369605856003557 5767774964506801098000667)
      ·
        refine ⟨8651662446760201647001001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767774964506801098000667 8651662446760201647001001)
        ·
          refine ⟨6488746835070151235250751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8651662446760201647001001 6488746835070151235250751)
          ·
            refine ⟨9733120252605226852876127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488746835070151235250751 9733120252605226852876127)
            ·
              refine ⟨14599680378907840279314191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9733120252605226852876127 14599680378907840279314191)
              ·
                refine ⟨21899520568361760418971287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14599680378907840279314191 21899520568361760418971287)
                ·
                  refine ⟨32849280852542640628456931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21899520568361760418971287 32849280852542640628456931)
                  ·
                    refine ⟨49273921278813960942685397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32849280852542640628456931 49273921278813960942685397)
                    ·
                      refine ⟨1154857529972202209594189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49273921278813960942685397 1154857529972202209594189)
                      ·
                        rfl

theorem cell23_2249077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2249077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249077 prefixEnd_2249077 := by exact prefixLift 2249077
  have htrace : WordTrace (prefixWord ++ tailWord_2249077) baseStart_2249077 baseEnd_2249077 := by
    simpa [prefixWord, tailWord_2249077, baseEnd_2249077] using wordTrace_append hprefix tailTrace_2249077
  have hstable : (prefixWord ++ tailWord_2249077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249077).length < 2 ^ (prefixWord ++ tailWord_2249077).sum := by decide
  have hdescent : baseEnd_2249077 < baseStart_2249077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249124 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_2249124 : Nat := 118140960795 + 2249124 * 2 ^ 59
def prefixEnd_2249124 : Nat := 4983230072969 + 3 ^ 40 * 2249124 * 2
def baseEnd_2249124 : Nat := 1154881663562963525706473

theorem tailTrace_2249124 : CollatzResearch.WordTrace tailWord_2249124 prefixEnd_2249124 1154881663562963525706473 := by
  unfold tailWord_2249124
  simp only [CollatzResearch.WordTrace]
  refine ⟨41016145751907671321485213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54688194335876895095313617 41016145751907671321485213)
  ·
    refine ⟨15381054656965376745556955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41016145751907671321485213 15381054656965376745556955)
    ·
      refine ⟨23071581985448065118335433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15381054656965376745556955 23071581985448065118335433)
      ·
        refine ⟨17303686489086048838751575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23071581985448065118335433 17303686489086048838751575)
        ·
          refine ⟨25955529733629073258127363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17303686489086048838751575 25955529733629073258127363)
          ·
            refine ⟨38933294600443609887191045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25955529733629073258127363 38933294600443609887191045)
            ·
              refine ⟨7299992737583176853848321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38933294600443609887191045 7299992737583176853848321)
              ·
                refine ⟨5474994553187382640386241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7299992737583176853848321 5474994553187382640386241)
                ·
                  refine ⟨4106245914890536980289681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5474994553187382640386241 4106245914890536980289681)
                  ·
                    refine ⟨3079684436167902735217261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4106245914890536980289681 3079684436167902735217261)
                    ·
                      refine ⟨1154881663562963525706473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3079684436167902735217261 1154881663562963525706473)
                      ·
                        rfl

theorem cell23_2249124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_2249124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249124 prefixEnd_2249124 := by exact prefixLift 2249124
  have htrace : WordTrace (prefixWord ++ tailWord_2249124) baseStart_2249124 baseEnd_2249124 := by
    simpa [prefixWord, tailWord_2249124, baseEnd_2249124] using wordTrace_append hprefix tailTrace_2249124
  have hstable : (prefixWord ++ tailWord_2249124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249124).length < 2 ^ (prefixWord ++ tailWord_2249124).sum := by decide
  have hdescent : baseEnd_2249124 < baseStart_2249124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249181 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_2249181 : Nat := 118140960795 + 2249181 * 2 ^ 59
def prefixEnd_2249181 : Nat := 4983230072969 + 3 ^ 40 * 2249181 * 2
def baseEnd_2249181 : Nat := 1154910931960269802693711

theorem tailTrace_2249181 : CollatzResearch.WordTrace tailWord_2249181 prefixEnd_2249181 1154910931960269802693711 := by
  unfold tailWord_2249181
  simp only [CollatzResearch.WordTrace]
  refine ⟨82034370464608841377795397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54689580309739227585196931 82034370464608841377795397)
  ·
    refine ⟨15381444462114157758336637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82034370464608841377795397 15381444462114157758336637)
    ·
      refine ⟨5768041673292809159376239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15381444462114157758336637 5768041673292809159376239)
      ·
        refine ⟨8652062509939213739064359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5768041673292809159376239 8652062509939213739064359)
        ·
          refine ⟨12978093764908820608596539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8652062509939213739064359 12978093764908820608596539)
          ·
            refine ⟨19467140647363230912894809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12978093764908820608596539 19467140647363230912894809)
            ·
              refine ⟨14600355485522423184671107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19467140647363230912894809 14600355485522423184671107)
              ·
                refine ⟨21900533228283634777006661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14600355485522423184671107 21900533228283634777006661)
                ·
                  refine ⟨4106349980303181520688749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21900533228283634777006661 4106349980303181520688749)
                  ·
                    refine ⟨1539881242613693070258281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4106349980303181520688749 1539881242613693070258281)
                    ·
                      refine ⟨1154910931960269802693711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539881242613693070258281 1154910931960269802693711)
                      ·
                        rfl

theorem cell23_2249181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_2249181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249181 prefixEnd_2249181 := by exact prefixLift 2249181
  have htrace : WordTrace (prefixWord ++ tailWord_2249181) baseStart_2249181 baseEnd_2249181 := by
    simpa [prefixWord, tailWord_2249181, baseEnd_2249181] using wordTrace_append hprefix tailTrace_2249181
  have hstable : (prefixWord ++ tailWord_2249181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249181).length < 2 ^ (prefixWord ++ tailWord_2249181).sum := by decide
  have hdescent : baseEnd_2249181 < baseStart_2249181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249245 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_2249245 : Nat := 118140960795 + 2249245 * 2 ^ 59
def prefixEnd_2249245 : Nat := 4983230072969 + 3 ^ 40 * 2249245 * 2
def baseEnd_2249245 : Nat := 1154943794722157552293417

theorem tailTrace_2249245 : CollatzResearch.WordTrace tailWord_2249245 prefixEnd_2249245 1154943794722157552293417 := by
  unfold tailWord_2249245
  simp only [CollatzResearch.WordTrace]
  refine ⟨82036704736376980308125189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54691136490917986872083459 82036704736376980308125189)
  ·
    refine ⟨15381882138070683807773473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82036704736376980308125189 15381882138070683807773473)
    ·
      refine ⟨11536411603553012855830105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15381882138070683807773473 11536411603553012855830105)
      ·
        refine ⟨8652308702664759641872579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11536411603553012855830105 8652308702664759641872579)
        ·
          refine ⟨12978463053997139462808869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8652308702664759641872579 12978463053997139462808869)
          ·
            refine ⟨2433461822624463649276663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12978463053997139462808869 2433461822624463649276663)
            ·
              refine ⟨3650192733936695473914995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433461822624463649276663 3650192733936695473914995)
              ·
                refine ⟨5475289100905043210872493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650192733936695473914995 5475289100905043210872493)
                ·
                  refine ⟨2053233412839391204077185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5475289100905043210872493 2053233412839391204077185)
                  ·
                    refine ⟨1539925059629543403057889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2053233412839391204077185 1539925059629543403057889)
                    ·
                      refine ⟨1154943794722157552293417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539925059629543403057889 1154943794722157552293417)
                      ·
                        rfl

theorem cell23_2249245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_2249245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249245 prefixEnd_2249245 := by exact prefixLift 2249245
  have htrace : WordTrace (prefixWord ++ tailWord_2249245) baseStart_2249245 baseEnd_2249245 := by
    simpa [prefixWord, tailWord_2249245, baseEnd_2249245] using wordTrace_append hprefix tailTrace_2249245
  have hstable : (prefixWord ++ tailWord_2249245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249245).length < 2 ^ (prefixWord ++ tailWord_2249245).sum := by decide
  have hdescent : baseEnd_2249245 < baseStart_2249245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249247 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 2, 7]
def baseStart_2249247 : Nat := 118140960795 + 2249247 * 2 ^ 59
def prefixEnd_2249247 : Nat := 4983230072969 + 3 ^ 40 * 2249247 * 2
def baseEnd_2249247 : Nat := 384981607227822181489469

theorem tailTrace_2249247 : CollatzResearch.WordTrace tailWord_2249247 prefixEnd_2249247 384981607227822181489469 := by
  unfold tailWord_2249247
  simp only [CollatzResearch.WordTrace]
  refine ⟨82036777682369734649697995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54691185121579823099798663 82036777682369734649697995)
  ·
    refine ⟨123055166523554601974546993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82036777682369734649697995 123055166523554601974546993)
    ·
      refine ⟨92291374892665951480910245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123055166523554601974546993 92291374892665951480910245)
      ·
        refine ⟨17304632792374865902670671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92291374892665951480910245 17304632792374865902670671)
        ·
          refine ⟨25956949188562298854006007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17304632792374865902670671 25956949188562298854006007)
          ·
            refine ⟨38935423782843448281009011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25956949188562298854006007 38935423782843448281009011)
            ·
              refine ⟨58403135674265172421513517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38935423782843448281009011 58403135674265172421513517)
              ·
                refine ⟨21901175877849439658067569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58403135674265172421513517 21901175877849439658067569)
                ·
                  refine ⟨16425881908387079743550677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21901175877849439658067569 16425881908387079743550677)
                  ·
                    refine ⟨384981607227822181489469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16425881908387079743550677 384981607227822181489469)
                    ·
                      rfl

theorem cell23_2249247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_2249247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249247 prefixEnd_2249247 := by exact prefixLift 2249247
  have htrace : WordTrace (prefixWord ++ tailWord_2249247) baseStart_2249247 baseEnd_2249247 := by
    simpa [prefixWord, tailWord_2249247, baseEnd_2249247] using wordTrace_append hprefix tailTrace_2249247
  have hstable : (prefixWord ++ tailWord_2249247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249247).length < 2 ^ (prefixWord ++ tailWord_2249247).sum := by decide
  have hdescent : baseEnd_2249247 < baseStart_2249247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249255 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2249255 : Nat := 118140960795 + 2249255 * 2 ^ 59
def prefixEnd_2249255 : Nat := 4983230072969 + 3 ^ 40 * 2249255 * 2
def baseEnd_2249255 : Nat := 384982976509567504389457

theorem tailTrace_2249255 : CollatzResearch.WordTrace tailWord_2249255 prefixEnd_2249255 384982976509567504389457 := by
  unfold tailWord_2249255
  simp only [CollatzResearch.WordTrace]
  refine ⟨82037069466340752015989219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54691379644227168010659479 82037069466340752015989219)
  ·
    refine ⟨123055604199511128023983829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82037069466340752015989219 123055604199511128023983829)
    ·
      refine ⟨2884115723426042063062121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 123055604199511128023983829 2884115723426042063062121)
      ·
        refine ⟨2163086792569531547296591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2884115723426042063062121 2163086792569531547296591)
        ·
          refine ⟨3244630188854297320944887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163086792569531547296591 3244630188854297320944887)
          ·
            refine ⟨4866945283281445981417331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244630188854297320944887 4866945283281445981417331)
            ·
              refine ⟨7300417924922168972125997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866945283281445981417331 7300417924922168972125997)
              ·
                refine ⟨2737656721845813364547249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7300417924922168972125997 2737656721845813364547249)
                ·
                  refine ⟨2053242541384360023410437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737656721845813364547249 2053242541384360023410437)
                  ·
                    refine ⟨384982976509567504389457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2053242541384360023410437 384982976509567504389457)
                    ·
                      rfl

theorem cell23_2249255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2249255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249255 prefixEnd_2249255 := by exact prefixLift 2249255
  have htrace : WordTrace (prefixWord ++ tailWord_2249255) baseStart_2249255 baseEnd_2249255 := by
    simpa [prefixWord, tailWord_2249255, baseEnd_2249255] using wordTrace_append hprefix tailTrace_2249255
  have hstable : (prefixWord ++ tailWord_2249255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249255).length < 2 ^ (prefixWord ++ tailWord_2249255).sum := by decide
  have hdescent : baseEnd_2249255 < baseStart_2249255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249271 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 3, 3, 2]
def baseStart_2249271 : Nat := 118140960795 + 2249271 * 2 ^ 59
def prefixEnd_2249271 : Nat := 4983230072969 + 3 ^ 40 * 2249271 * 2
def baseEnd_2249271 : Nat := 1154957145219174450568297

theorem tailTrace_2249271 : CollatzResearch.WordTrace tailWord_2249271 prefixEnd_2249271 1154957145219174450568297 := by
  unfold tailWord_2249271
  simp only [CollatzResearch.WordTrace]
  refine ⟨82037653034282786748571667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54691768689521857832381111 82037653034282786748571667)
  ·
    refine ⟨123056479551424180122857501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82037653034282786748571667 123056479551424180122857501)
    ·
      refine ⟨46146179831784067546071563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123056479551424180122857501 46146179831784067546071563)
      ·
        refine ⟨69219269747676101319107345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46146179831784067546071563 69219269747676101319107345)
        ·
          refine ⟨51914452310757075989330509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69219269747676101319107345 51914452310757075989330509)
          ·
            refine ⟨19467919616533903495998941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51914452310757075989330509 19467919616533903495998941)
            ·
              refine ⟨7300469856200213810999603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19467919616533903495998941 7300469856200213810999603)
              ·
                refine ⟨10950704784300320716499405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7300469856200213810999603 10950704784300320716499405)
                ·
                  refine ⟨4106514294112620268687277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10950704784300320716499405 4106514294112620268687277)
                  ·
                    refine ⟨1539942860292232600757729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4106514294112620268687277 1539942860292232600757729)
                    ·
                      refine ⟨1154957145219174450568297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1539942860292232600757729 1154957145219174450568297)
                      ·
                        rfl

theorem cell23_2249271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_2249271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249271 prefixEnd_2249271 := by exact prefixLift 2249271
  have htrace : WordTrace (prefixWord ++ tailWord_2249271) baseStart_2249271 baseEnd_2249271 := by
    simpa [prefixWord, tailWord_2249271, baseEnd_2249271] using wordTrace_append hprefix tailTrace_2249271
  have hstable : (prefixWord ++ tailWord_2249271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249271).length < 2 ^ (prefixWord ++ tailWord_2249271).sum := by decide
  have hdescent : baseEnd_2249271 < baseStart_2249271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249304 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2249304 : Nat := 118140960795 + 2249304 * 2 ^ 59
def prefixEnd_2249304 : Nat := 4983230072969 + 3 ^ 40 * 2249304 * 2
def baseEnd_2249304 : Nat := 1154974090080772821455645

theorem tailTrace_2249304 : CollatzResearch.WordTrace tailWord_2249304 prefixEnd_2249304 1154974090080772821455645 := by
  unfold tailWord_2249304
  simp only [CollatzResearch.WordTrace]
  refine ⟨41019428321581616692261483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54692571095442155589681977 41019428321581616692261483)
  ·
    refine ⟨61529142482372425038392225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41019428321581616692261483 61529142482372425038392225)
    ·
      refine ⟨46146856861779318778794169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61529142482372425038392225 46146856861779318778794169)
      ·
        refine ⟨34610142646334489084095627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46146856861779318778794169 34610142646334489084095627)
        ·
          refine ⟨51915213969501733626143441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34610142646334489084095627 51915213969501733626143441)
          ·
            refine ⟨38936410477126300219607581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51915213969501733626143441 38936410477126300219607581)
            ·
              refine ⟨14601153928922362582352843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38936410477126300219607581 14601153928922362582352843)
              ·
                refine ⟨21901730893383543873529265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14601153928922362582352843 21901730893383543873529265)
                ·
                  refine ⟨16426298170037657905146949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21901730893383543873529265 16426298170037657905146949)
                  ·
                    refine ⟨3079930906882060857215053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16426298170037657905146949 3079930906882060857215053)
                    ·
                      refine ⟨1154974090080772821455645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3079930906882060857215053 1154974090080772821455645)
                      ·
                        rfl

theorem cell23_2249304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2249304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249304 prefixEnd_2249304 := by exact prefixLift 2249304
  have htrace : WordTrace (prefixWord ++ tailWord_2249304) baseStart_2249304 baseEnd_2249304 := by
    simpa [prefixWord, tailWord_2249304, baseEnd_2249304] using wordTrace_append hprefix tailTrace_2249304
  have hstable : (prefixWord ++ tailWord_2249304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249304).length < 2 ^ (prefixWord ++ tailWord_2249304).sum := by decide
  have hdescent : baseEnd_2249304 < baseStart_2249304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249346 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2249346 : Nat := 118140960795 + 2249346 * 2 ^ 59
def prefixEnd_2249346 : Nat := 4983230072969 + 3 ^ 40 * 2249346 * 2
def baseEnd_2249346 : Nat := 1154995656268261657130453

theorem tailTrace_2249346 : CollatzResearch.WordTrace tailWord_2249346 prefixEnd_2249346 1154995656268261657130453 := by
  unfold tailWord_2249346
  simp only [CollatzResearch.WordTrace]
  refine ⟨20510097127252768639387973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54693592339340716371701261 20510097127252768639387973)
  ·
    refine ⟨3845643211359894119885245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20510097127252768639387973 3845643211359894119885245)
    ·
      refine ⟨1442116204259960294956967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3845643211359894119885245 1442116204259960294956967)
      ·
        refine ⟨2163174306389940442435451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442116204259960294956967 2163174306389940442435451)
        ·
          refine ⟨3244761459584910663653177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163174306389940442435451 3244761459584910663653177)
          ·
            refine ⟨2433571094688682997739883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3244761459584910663653177 2433571094688682997739883)
            ·
              refine ⟨3650356642033024496609825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433571094688682997739883 3650356642033024496609825)
              ·
                refine ⟨2737767481524768372457369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3650356642033024496609825 2737767481524768372457369)
                ·
                  refine ⟨2053325611143576279343027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737767481524768372457369 2053325611143576279343027)
                  ·
                    refine ⟨3079988416715364419014541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2053325611143576279343027 3079988416715364419014541)
                    ·
                      refine ⟨1154995656268261657130453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3079988416715364419014541 1154995656268261657130453)
                      ·
                        rfl

theorem cell23_2249346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2249346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249346 prefixEnd_2249346 := by exact prefixLift 2249346
  have htrace : WordTrace (prefixWord ++ tailWord_2249346) baseStart_2249346 baseEnd_2249346 := by
    simpa [prefixWord, tailWord_2249346, baseEnd_2249346] using wordTrace_append hprefix tailTrace_2249346
  have hstable : (prefixWord ++ tailWord_2249346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249346).length < 2 ^ (prefixWord ++ tailWord_2249346).sum := by decide
  have hdescent : baseEnd_2249346 < baseStart_2249346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249394 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2249394 : Nat := 118140960795 + 2249394 * 2 ^ 59
def prefixEnd_2249394 : Nat := 4983230072969 + 3 ^ 40 * 2249394 * 2
def baseEnd_2249394 : Nat := 1155020303339677469330231

theorem tailTrace_2249394 : CollatzResearch.WordTrace tailWord_2249394 prefixEnd_2249394 1155020303339677469330231 := by
  unfold tailWord_2249394
  simp only [CollatzResearch.WordTrace]
  refine ⟨20510534803209294688824809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54694759475224785836866157 20510534803209294688824809)
  ·
    refine ⟨15382901102406971016618607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20510534803209294688824809 15382901102406971016618607)
    ·
      refine ⟨23074351653610456524927911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15382901102406971016618607 23074351653610456524927911)
      ·
        refine ⟨34611527480415684787391867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23074351653610456524927911 34611527480415684787391867)
        ·
          refine ⟨51917291220623527181087801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34611527480415684787391867 51917291220623527181087801)
          ·
            refine ⟨38937968415467645385815851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51917291220623527181087801 38937968415467645385815851)
            ·
              refine ⟨58406952623201468078723777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38937968415467645385815851 58406952623201468078723777)
              ·
                refine ⟨43805214467401101059042833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58406952623201468078723777 43805214467401101059042833)
                ·
                  refine ⟨32853910850550825794282125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43805214467401101059042833 32853910850550825794282125)
                  ·
                    refine ⟨12320216568956559672855797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32853910850550825794282125 12320216568956559672855797)
                    ·
                      refine ⟨1155020303339677469330231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12320216568956559672855797 1155020303339677469330231)
                      ·
                        rfl

theorem cell23_2249394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2249394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249394 prefixEnd_2249394 := by exact prefixLift 2249394
  have htrace : WordTrace (prefixWord ++ tailWord_2249394) baseStart_2249394 baseEnd_2249394 := by
    simpa [prefixWord, tailWord_2249394, baseEnd_2249394] using wordTrace_append hprefix tailTrace_2249394
  have hstable : (prefixWord ++ tailWord_2249394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249394).length < 2 ^ (prefixWord ++ tailWord_2249394).sum := by decide
  have hdescent : baseEnd_2249394 < baseStart_2249394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249418 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_2249418 : Nat := 118140960795 + 2249418 * 2 ^ 59
def prefixEnd_2249418 : Nat := 4983230072969 + 3 ^ 40 * 2249418 * 2
def baseEnd_2249418 : Nat := 385010875625128458476707

theorem tailTrace_2249418 : CollatzResearch.WordTrace tailWord_2249418 prefixEnd_2249418 385010875625128458476707 := by
  unfold tailWord_2249418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20510753641187557713543227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54695343043166820569448605 20510753641187557713543227)
  ·
    refine ⟨30766130461781336570314841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20510753641187557713543227 30766130461781336570314841)
    ·
      refine ⟨23074597846336002427736131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30766130461781336570314841 23074597846336002427736131)
      ·
        refine ⟨34611896769504003641604197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23074597846336002427736131 34611896769504003641604197)
        ·
          refine ⟨6489730644282000682800787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34611896769504003641604197 6489730644282000682800787)
          ·
            refine ⟨9734595966423001024201181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6489730644282000682800787 9734595966423001024201181)
            ·
              refine ⟨3650473487408625384075443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9734595966423001024201181 3650473487408625384075443)
              ·
                refine ⟨5475710231112938076113165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650473487408625384075443 5475710231112938076113165)
                ·
                  refine ⟨2053391336667351778542437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5475710231112938076113165 2053391336667351778542437)
                  ·
                    refine ⟨385010875625128458476707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2053391336667351778542437 385010875625128458476707)
                    ·
                      rfl

theorem cell23_2249418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_2249418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249418 prefixEnd_2249418 := by exact prefixLift 2249418
  have htrace : WordTrace (prefixWord ++ tailWord_2249418) baseStart_2249418 baseEnd_2249418 := by
    simpa [prefixWord, tailWord_2249418, baseEnd_2249418] using wordTrace_append hprefix tailTrace_2249418
  have hstable : (prefixWord ++ tailWord_2249418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249418).length < 2 ^ (prefixWord ++ tailWord_2249418).sum := by decide
  have hdescent : baseEnd_2249418 < baseStart_2249418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249431 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 6]
def baseStart_2249431 : Nat := 118140960795 + 2249431 * 2 ^ 59
def prefixEnd_2249431 : Nat := 4983230072969 + 3 ^ 40 * 2249431 * 2
def baseEnd_2249431 : Nat := 128337700235988202729729

theorem tailTrace_2249431 : CollatzResearch.WordTrace tailWord_2249431 prefixEnd_2249431 128337700235988202729729 := by
  unfold tailWord_2249431
  simp only [CollatzResearch.WordTrace]
  refine ⟨82043488713703134074396147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54695659142468756049597431 82043488713703134074396147)
  ·
    refine ⟨123065233070554701111594221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82043488713703134074396147 123065233070554701111594221)
    ·
      refine ⟨46149462401458012916847833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123065233070554701111594221 46149462401458012916847833)
      ·
        refine ⟨34612096801093509687635875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46149462401458012916847833 34612096801093509687635875)
        ·
          refine ⟨51918145201640264531453813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34612096801093509687635875 51918145201640264531453813)
          ·
            refine ⟨4867326112653774799823795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51918145201640264531453813 4867326112653774799823795)
            ·
              refine ⟨7300989168980662199735693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4867326112653774799823795 7300989168980662199735693)
              ·
                refine ⟨2737870938367748324900885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7300989168980662199735693 2737870938367748324900885)
                ·
                  refine ⟨128337700235988202729729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2737870938367748324900885 128337700235988202729729)
                  ·
                    rfl

theorem cell23_2249431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 6].length) (baseStart_2249431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249431 prefixEnd_2249431 := by exact prefixLift 2249431
  have htrace : WordTrace (prefixWord ++ tailWord_2249431) baseStart_2249431 baseEnd_2249431 := by
    simpa [prefixWord, tailWord_2249431, baseEnd_2249431] using wordTrace_append hprefix tailTrace_2249431
  have hstable : (prefixWord ++ tailWord_2249431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249431).length < 2 ^ (prefixWord ++ tailWord_2249431).sum := by decide
  have hdescent : baseEnd_2249431 < baseStart_2249431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249481 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_2249481 : Nat := 118140960795 + 2249481 * 2 ^ 59
def prefixEnd_2249481 : Nat := 4983230072969 + 3 ^ 40 * 2249481 * 2
def baseEnd_2249481 : Nat := 1155064976156618628942331

theorem tailTrace_2249481 : CollatzResearch.WordTrace tailWord_2249481 prefixEnd_2249481 1155064976156618628942331 := by
  unfold tailWord_2249481
  simp only [CollatzResearch.WordTrace]
  refine ⟨82045312363521992613716297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54696874909014661742477531 82045312363521992613716297)
  ·
    refine ⟨61533984272641494460287223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82045312363521992613716297 61533984272641494460287223)
    ·
      refine ⟨92300976408962241690430835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61533984272641494460287223 92300976408962241690430835)
      ·
        refine ⟨138451464613443362535646253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92300976408962241690430835 138451464613443362535646253)
        ·
          refine ⟨51919299230041260950867345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138451464613443362535646253 51919299230041260950867345)
          ·
            refine ⟨38939474422530945713150509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51919299230041260950867345 38939474422530945713150509)
            ·
              refine ⟨14602302908449104642431441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38939474422530945713150509 14602302908449104642431441)
              ·
                refine ⟨10951727181336828481823581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14602302908449104642431441 10951727181336828481823581)
                ·
                  refine ⟨4106897693001310680683843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10951727181336828481823581 4106897693001310680683843)
                  ·
                    refine ⟨6160346539501966021025765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4106897693001310680683843 6160346539501966021025765)
                    ·
                      refine ⟨1155064976156618628942331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6160346539501966021025765 1155064976156618628942331)
                      ·
                        rfl

theorem cell23_2249481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_2249481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249481 prefixEnd_2249481 := by exact prefixLift 2249481
  have htrace : WordTrace (prefixWord ++ tailWord_2249481) baseStart_2249481 baseEnd_2249481 := by
    simpa [prefixWord, tailWord_2249481, baseEnd_2249481] using wordTrace_append hprefix tailTrace_2249481
  have hstable : (prefixWord ++ tailWord_2249481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249481).length < 2 ^ (prefixWord ++ tailWord_2249481).sum := by decide
  have hdescent : baseEnd_2249481 < baseStart_2249481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249491 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 1, 6]
def baseStart_2249491 : Nat := 118140960795 + 2249491 * 2 ^ 59
def prefixEnd_2249491 : Nat := 4983230072969 + 3 ^ 40 * 2249491 * 2
def baseEnd_2249491 : Nat := 385023370321054529939095

theorem tailTrace_2249491 : CollatzResearch.WordTrace tailWord_2249491 prefixEnd_2249491 385023370321054529939095 := by
  unfold tailWord_2249491
  simp only [CollatzResearch.WordTrace]
  refine ⟨82045677093485764321580327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54697118062323842881053551 82045677093485764321580327)
  ·
    refine ⟨123068515640228646482370491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82045677093485764321580327 123068515640228646482370491)
    ·
      refine ⟨184602773460342969723555737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123068515640228646482370491 184602773460342969723555737)
      ·
        refine ⟨138452080095257227292666803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184602773460342969723555737 138452080095257227292666803)
        ·
          refine ⟨207678120142885840939000205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138452080095257227292666803 207678120142885840939000205)
          ·
            refine ⟨77879295053582190352125077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207678120142885840939000205 77879295053582190352125077)
            ·
              refine ⟨3650591955636665172755863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77879295053582190352125077 3650591955636665172755863)
              ·
                refine ⟨5475887933454997759133795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650591955636665172755863 5475887933454997759133795)
                ·
                  refine ⟨8213831900182496638700693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475887933454997759133795 8213831900182496638700693)
                  ·
                    refine ⟨385023370321054529939095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8213831900182496638700693 385023370321054529939095)
                    ·
                      rfl

theorem cell23_2249491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 6].length) (baseStart_2249491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249491 prefixEnd_2249491 := by exact prefixLift 2249491
  have htrace : WordTrace (prefixWord ++ tailWord_2249491) baseStart_2249491 baseEnd_2249491 := by
    simpa [prefixWord, tailWord_2249491, baseEnd_2249491] using wordTrace_append hprefix tailTrace_2249491
  have hstable : (prefixWord ++ tailWord_2249491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249491).length < 2 ^ (prefixWord ++ tailWord_2249491).sum := by decide
  have hdescent : baseEnd_2249491 < baseStart_2249491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249498 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_2249498 : Nat := 118140960795 + 2249498 * 2 ^ 59
def prefixEnd_2249498 : Nat := 4983230072969 + 3 ^ 40 * 2249498 * 2
def baseEnd_2249498 : Nat := 1155073705327745062429753

theorem tailTrace_2249498 : CollatzResearch.WordTrace tailWord_2249498 prefixEnd_2249498 1155073705327745062429753 := by
  unfold tailWord_2249498
  simp only [CollatzResearch.WordTrace]
  refine ⟨20511483101115101129271287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54697288269640269678056765 20511483101115101129271287)
  ·
    refine ⟨30767224651672651693906931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20511483101115101129271287 30767224651672651693906931)
    ·
      refine ⟨46150836977508977540860397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30767224651672651693906931 46150836977508977540860397)
      ·
        refine ⟨17306563866565866577822649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46150836977508977540860397 17306563866565866577822649)
        ·
          refine ⟨12979922899924399933366987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17306563866565866577822649 12979922899924399933366987)
          ·
            refine ⟨19469884349886599900050481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12979922899924399933366987 19469884349886599900050481)
            ·
              refine ⟨14602413262414949925037861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19469884349886599900050481 14602413262414949925037861)
              ·
                refine ⟨2737952486702803110944599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14602413262414949925037861 2737952486702803110944599)
                ·
                  refine ⟨4106928730054204666416899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737952486702803110944599 4106928730054204666416899)
                  ·
                    refine ⟨6160393095081306999625349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4106928730054204666416899 6160393095081306999625349)
                    ·
                      refine ⟨1155073705327745062429753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6160393095081306999625349 1155073705327745062429753)
                      ·
                        rfl

theorem cell23_2249498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_2249498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249498 prefixEnd_2249498 := by exact prefixLift 2249498
  have htrace : WordTrace (prefixWord ++ tailWord_2249498) baseStart_2249498 baseEnd_2249498 := by
    simpa [prefixWord, tailWord_2249498, baseEnd_2249498] using wordTrace_append hprefix tailTrace_2249498
  have hstable : (prefixWord ++ tailWord_2249498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249498).length < 2 ^ (prefixWord ++ tailWord_2249498).sum := by decide
  have hdescent : baseEnd_2249498 < baseStart_2249498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249525 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2249525 : Nat := 118140960795 + 2249525 * 2 ^ 59
def prefixEnd_2249525 : Nat := 4983230072969 + 3 ^ 40 * 2249525 * 2
def baseEnd_2249525 : Nat := 385029189768472152264043

theorem tailTrace_2249525 : CollatzResearch.WordTrace tailWord_2249525 prefixEnd_2249525 385029189768472152264043 := by
  unfold tailWord_2249525
  simp only [CollatzResearch.WordTrace]
  refine ⟨82046917175362588128318029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54697944783575058752212019 82046917175362588128318029)
  ·
    refine ⟨30767593940760970548119261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82046917175362588128318029 30767593940760970548119261)
    ·
      refine ⟨11537847727785363955544723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30767593940760970548119261 11537847727785363955544723)
      ·
        refine ⟨17306771591678045933317085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11537847727785363955544723 17306771591678045933317085)
        ·
          refine ⟨6490039346879267224993907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17306771591678045933317085 6490039346879267224993907)
          ·
            refine ⟨9735059020318900837490861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490039346879267224993907 9735059020318900837490861)
            ·
              refine ⟨3650647132619587814059073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9735059020318900837490861 3650647132619587814059073)
              ·
                refine ⟨2737985349464690860544305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3650647132619587814059073 2737985349464690860544305)
                ·
                  refine ⟨2053489012098518145408229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737985349464690860544305 2053489012098518145408229)
                  ·
                    refine ⟨385029189768472152264043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2053489012098518145408229 385029189768472152264043)
                    ·
                      rfl

theorem cell23_2249525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2249525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249525 prefixEnd_2249525 := by exact prefixLift 2249525
  have htrace : WordTrace (prefixWord ++ tailWord_2249525) baseStart_2249525 baseEnd_2249525 := by
    simpa [prefixWord, tailWord_2249525, baseEnd_2249525] using wordTrace_append hprefix tailTrace_2249525
  have hstable : (prefixWord ++ tailWord_2249525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249525).length < 2 ^ (prefixWord ++ tailWord_2249525).sum := by decide
  have hdescent : baseEnd_2249525 < baseStart_2249525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249561 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_2249561 : Nat := 118140960795 + 2249561 * 2 ^ 59
def prefixEnd_2249561 : Nat := 4983230072969 + 3 ^ 40 * 2249561 * 2
def baseEnd_2249561 : Nat := 1155106054608978315941963

theorem tailTrace_2249561 : CollatzResearch.WordTrace tailWord_2249561 prefixEnd_2249561 1155106054608978315941963 := by
  unfold tailWord_2249561
  simp only [CollatzResearch.WordTrace]
  refine ⟨82048230203232166276628537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54698820135488110851085691 82048230203232166276628537)
  ·
    refine ⟨61536172652424124707471403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82048230203232166276628537 61536172652424124707471403)
    ·
      refine ⟨92304258978636187061207105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61536172652424124707471403 92304258978636187061207105)
      ·
        refine ⟨69228194233977140295905329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92304258978636187061207105 69228194233977140295905329)
        ·
          refine ⟨51921145675482855221928997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69228194233977140295905329 51921145675482855221928997)
          ·
            refine ⟨9735214814153035354111687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51921145675482855221928997 9735214814153035354111687)
            ·
              refine ⟨14602822221229553031167531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9735214814153035354111687 14602822221229553031167531)
              ·
                refine ⟨21904233331844329546751297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14602822221229553031167531 21904233331844329546751297)
                ·
                  refine ⟨16428174998883247160063473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21904233331844329546751297 16428174998883247160063473)
                  ·
                    refine ⟨12321131249162435370047605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16428174998883247160063473 12321131249162435370047605)
                    ·
                      refine ⟨1155106054608978315941963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12321131249162435370047605 1155106054608978315941963)
                      ·
                        rfl

theorem cell23_2249561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_2249561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249561 prefixEnd_2249561 := by exact prefixLift 2249561
  have htrace : WordTrace (prefixWord ++ tailWord_2249561) baseStart_2249561 baseEnd_2249561 := by
    simpa [prefixWord, tailWord_2249561, baseEnd_2249561] using wordTrace_append hprefix tailTrace_2249561
  have hstable : (prefixWord ++ tailWord_2249561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249561).length < 2 ^ (prefixWord ++ tailWord_2249561).sum := by decide
  have hdescent : baseEnd_2249561 < baseStart_2249561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249608 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2249608 : Nat := 118140960795 + 2249608 * 2 ^ 59
def prefixEnd_2249608 : Nat := 4983230072969 + 3 ^ 40 * 2249608 * 2
def baseEnd_2249608 : Nat := 1155130188199739632054247

theorem tailTrace_2249608 : CollatzResearch.WordTrace tailWord_2249608 prefixEnd_2249608 1155130188199739632054247 := by
  unfold tailWord_2249608
  simp only [CollatzResearch.WordTrace]
  refine ⟨41024972217030946651794739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54699962956041262202392985 41024972217030946651794739)
  ·
    refine ⟨61537458325546419977692109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41024972217030946651794739 61537458325546419977692109)
    ·
      refine ⟨23076546872079907491634541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61537458325546419977692109 23076546872079907491634541)
      ·
        refine ⟨8653705077029965309362953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23076546872079907491634541 8653705077029965309362953)
        ·
          refine ⟨6490278807772473982022215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8653705077029965309362953 6490278807772473982022215)
          ·
            refine ⟨9735418211658710973033323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490278807772473982022215 9735418211658710973033323)
            ·
              refine ⟨14603127317488066459549985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9735418211658710973033323 14603127317488066459549985)
              ·
                refine ⟨10952345488116049844662489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14603127317488066459549985 10952345488116049844662489)
                ·
                  refine ⟨8214259116087037383496867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10952345488116049844662489 8214259116087037383496867)
                  ·
                    refine ⟨12321388674130556075245301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8214259116087037383496867 12321388674130556075245301)
                    ·
                      refine ⟨1155130188199739632054247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12321388674130556075245301 1155130188199739632054247)
                      ·
                        rfl

theorem cell23_2249608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2249608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249608 prefixEnd_2249608 := by exact prefixLift 2249608
  have htrace : WordTrace (prefixWord ++ tailWord_2249608) baseStart_2249608 baseEnd_2249608 := by
    simpa [prefixWord, tailWord_2249608, baseEnd_2249608] using wordTrace_append hprefix tailTrace_2249608
  have hstable : (prefixWord ++ tailWord_2249608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249608).length < 2 ^ (prefixWord ++ tailWord_2249608).sum := by decide
  have hdescent : baseEnd_2249608 < baseStart_2249608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249611 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 7]
def baseStart_2249611 : Nat := 118140960795 + 2249611 * 2 ^ 59
def prefixEnd_2249611 : Nat := 4983230072969 + 3 ^ 40 * 2249611 * 2
def baseEnd_2249611 : Nat := 128347969849078124479637

theorem tailTrace_2249611 : CollatzResearch.WordTrace tailWord_2249611 prefixEnd_2249611 128347969849078124479637 := by
  unfold tailWord_2249611
  simp only [CollatzResearch.WordTrace]
  refine ⟨82050053853051024815948687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54700035902034016543965791 82050053853051024815948687)
  ·
    refine ⟨123075080779576537223923031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82050053853051024815948687 123075080779576537223923031)
    ·
      refine ⟨184612621169364805835884547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123075080779576537223923031 184612621169364805835884547)
      ·
        refine ⟨276918931754047208753826821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184612621169364805835884547 276918931754047208753826821)
        ·
          refine ⟨51922299703883851641342529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276918931754047208753826821 51922299703883851641342529)
          ·
            refine ⟨38941724777912888731006897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51922299703883851641342529 38941724777912888731006897)
            ·
              refine ⟨29206293583434666548255173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38941724777912888731006897 29206293583434666548255173)
              ·
                refine ⟨5476180046893999977797845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29206293583434666548255173 5476180046893999977797845)
                ·
                  refine ⟨128347969849078124479637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5476180046893999977797845 128347969849078124479637)
                  ·
                    rfl

theorem cell23_2249611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 7].length) (baseStart_2249611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249611 prefixEnd_2249611 := by exact prefixLift 2249611
  have htrace : WordTrace (prefixWord ++ tailWord_2249611) baseStart_2249611 baseEnd_2249611 := by
    simpa [prefixWord, tailWord_2249611, baseEnd_2249611] using wordTrace_append hprefix tailTrace_2249611
  have hstable : (prefixWord ++ tailWord_2249611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249611).length < 2 ^ (prefixWord ++ tailWord_2249611).sum := by decide
  have hdescent : baseEnd_2249611 < baseStart_2249611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249651 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7]
def baseStart_2249651 : Nat := 118140960795 + 2249651 * 2 ^ 59
def prefixEnd_2249651 : Nat := 4983230072969 + 3 ^ 40 * 2249651 * 2
def baseEnd_2249651 : Nat := 1155152267867882963816549

theorem tailTrace_2249651 : CollatzResearch.WordTrace tailWord_2249651 prefixEnd_2249651 1155152267867882963816549 := by
  unfold tailWord_2249651
  simp only [CollatzResearch.WordTrace]
  refine ⟨82051512772906111647404807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54701008515270741098269871 82051512772906111647404807)
  ·
    refine ⟨123077269159359167471107211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82051512772906111647404807 123077269159359167471107211)
    ·
      refine ⟨184615903739038751206660817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123077269159359167471107211 184615903739038751206660817)
      ·
        refine ⟨138461927804279063404995613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184615903739038751206660817 138461927804279063404995613)
        ·
          refine ⟨51923222926604648776873355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138461927804279063404995613 51923222926604648776873355)
          ·
            refine ⟨77884834389906973165310033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51923222926604648776873355 77884834389906973165310033)
            ·
              refine ⟨58413625792430229873982525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77884834389906973165310033 58413625792430229873982525)
              ·
                refine ⟨21905109672161336202743447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58413625792430229873982525 21905109672161336202743447)
                ·
                  refine ⟨32857664508242004304115171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21905109672161336202743447 32857664508242004304115171)
                  ·
                    refine ⟨49286496762363006456172757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32857664508242004304115171 49286496762363006456172757)
                    ·
                      refine ⟨1155152267867882963816549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49286496762363006456172757 1155152267867882963816549)
                      ·
                        rfl

theorem cell23_2249651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_2249651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249651 prefixEnd_2249651 := by exact prefixLift 2249651
  have htrace : WordTrace (prefixWord ++ tailWord_2249651) baseStart_2249651 baseEnd_2249651 := by
    simpa [prefixWord, tailWord_2249651, baseEnd_2249651] using wordTrace_append hprefix tailTrace_2249651
  have hstable : (prefixWord ++ tailWord_2249651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249651).length < 2 ^ (prefixWord ++ tailWord_2249651).sum := by decide
  have hdescent : baseEnd_2249651 < baseStart_2249651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249652 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2249652 : Nat := 118140960795 + 2249652 * 2 ^ 59
def prefixEnd_2249652 : Nat := 4983230072969 + 3 ^ 40 * 2249652 * 2
def baseEnd_2249652 : Nat := 1155152781348537459904045

theorem tailTrace_2249652 : CollatzResearch.WordTrace tailWord_2249652 prefixEnd_2249652 1155152781348537459904045 := by
  unfold tailWord_2249652
  simp only [CollatzResearch.WordTrace]
  refine ⟨41025774622951244409095605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54701032830601659212127473 41025774622951244409095605)
  ·
    refine ⟨3846166370901679163352713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41025774622951244409095605 3846166370901679163352713)
    ·
      refine ⟨2884624778176259372514535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3846166370901679163352713 2884624778176259372514535)
      ·
        refine ⟨4326937167264389058771803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884624778176259372514535 4326937167264389058771803)
        ·
          refine ⟨6490405750896583588157705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326937167264389058771803 6490405750896583588157705)
          ·
            refine ⟨4867804313172437691118279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6490405750896583588157705 4867804313172437691118279)
            ·
              refine ⟨7301706469758656536677419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4867804313172437691118279 7301706469758656536677419)
              ·
                refine ⟨10952559704637984805016129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7301706469758656536677419 10952559704637984805016129)
                ·
                  refine ⟨8214419778478488603762097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10952559704637984805016129 8214419778478488603762097)
                  ·
                    refine ⟨6160814833858866452821573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8214419778478488603762097 6160814833858866452821573)
                    ·
                      refine ⟨1155152781348537459904045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6160814833858866452821573 1155152781348537459904045)
                      ·
                        rfl

theorem cell23_2249652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2249652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249652 prefixEnd_2249652 := by exact prefixLift 2249652
  have htrace : WordTrace (prefixWord ++ tailWord_2249652) baseStart_2249652 baseEnd_2249652 := by
    simpa [prefixWord, tailWord_2249652, baseEnd_2249652] using wordTrace_append hprefix tailTrace_2249652
  have hstable : (prefixWord ++ tailWord_2249652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249652).length < 2 ^ (prefixWord ++ tailWord_2249652).sum := by decide
  have hdescent : baseEnd_2249652 < baseStart_2249652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249675 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 2, 5]
def baseStart_2249675 : Nat := 118140960795 + 2249675 * 2 ^ 59
def prefixEnd_2249675 : Nat := 4983230072969 + 3 ^ 40 * 2249675 * 2
def baseEnd_2249675 : Nat := 385054863801196956638813

theorem tailTrace_2249675 : CollatzResearch.WordTrace tailWord_2249675 prefixEnd_2249675 385054863801196956638813 := by
  unfold tailWord_2249675
  simp only [CollatzResearch.WordTrace]
  refine ⟨82052388124819163746278479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54701592083212775830852319 82052388124819163746278479)
  ·
    refine ⟨123078582187228745619417719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82052388124819163746278479 123078582187228745619417719)
    ·
      refine ⟨184617873280843118429126579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123078582187228745619417719 184617873280843118429126579)
      ·
        refine ⟨276926809921264677643689869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184617873280843118429126579 276926809921264677643689869)
        ·
          refine ⟨103847553720474254116383701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276926809921264677643689869 103847553720474254116383701)
          ·
            refine ⟨2433927040323615330852743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103847553720474254116383701 2433927040323615330852743)
            ·
              refine ⟨3650890560485422996279115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433927040323615330852743 3650890560485422996279115)
              ·
                refine ⟨5476335840728134494418673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650890560485422996279115 5476335840728134494418673)
                ·
                  refine ⟨4107251880546100870814005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5476335840728134494418673 4107251880546100870814005)
                  ·
                    refine ⟨385054863801196956638813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4107251880546100870814005 385054863801196956638813)
                    ·
                      rfl

theorem cell23_2249675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 5].length) (baseStart_2249675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249675 prefixEnd_2249675 := by exact prefixLift 2249675
  have htrace : WordTrace (prefixWord ++ tailWord_2249675) baseStart_2249675 baseEnd_2249675 := by
    simpa [prefixWord, tailWord_2249675, baseEnd_2249675] using wordTrace_append hprefix tailTrace_2249675
  have hstable : (prefixWord ++ tailWord_2249675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249675).length < 2 ^ (prefixWord ++ tailWord_2249675).sum := by decide
  have hdescent : baseEnd_2249675 < baseStart_2249675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249677 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2249677 : Nat := 118140960795 + 2249677 * 2 ^ 59
def prefixEnd_2249677 : Nat := 4983230072969 + 3 ^ 40 * 2249677 * 2
def baseEnd_2249677 : Nat := 1155165618364899862091431

theorem tailTrace_2249677 : CollatzResearch.WordTrace tailWord_2249677 prefixEnd_2249677 1155165618364899862091431 := by
  unfold tailWord_2249677
  simp only [CollatzResearch.WordTrace]
  refine ⟨82052461070811918087851285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54701640713874612058567523 82052461070811918087851285)
  ·
    refine ⟨3846209112694308660368029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82052461070811918087851285 3846209112694308660368029)
    ·
      refine ⟨1442328417260365747638011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3846209112694308660368029 1442328417260365747638011)
      ·
        refine ⟨2163492625890548621457017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442328417260365747638011 2163492625890548621457017)
        ·
          refine ⟨1622619469417911466092763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2163492625890548621457017 1622619469417911466092763)
          ·
            refine ⟨2433929204126867199139145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622619469417911466092763 2433929204126867199139145)
            ·
              refine ⟨1825446903095150399354359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433929204126867199139145 1825446903095150399354359)
              ·
                refine ⟨2738170354642725599031539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825446903095150399354359 2738170354642725599031539)
                ·
                  refine ⟨4107255531964088398547309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738170354642725599031539 4107255531964088398547309)
                  ·
                    refine ⟨1540220824486533149455241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4107255531964088398547309 1540220824486533149455241)
                    ·
                      refine ⟨1155165618364899862091431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540220824486533149455241 1155165618364899862091431)
                      ·
                        rfl

theorem cell23_2249677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2249677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249677 prefixEnd_2249677 := by exact prefixLift 2249677
  have htrace : WordTrace (prefixWord ++ tailWord_2249677) baseStart_2249677 baseEnd_2249677 := by
    simpa [prefixWord, tailWord_2249677, baseEnd_2249677] using wordTrace_append hprefix tailTrace_2249677
  have hstable : (prefixWord ++ tailWord_2249677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249677).length < 2 ^ (prefixWord ++ tailWord_2249677).sum := by decide
  have hdescent : baseEnd_2249677 < baseStart_2249677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249739 : List Nat := [1, 1, 1, 1, 6, 4, 1, 3, 1, 4]
def baseStart_2249739 : Nat := 118140960795 + 2249739 * 2 ^ 59
def prefixEnd_2249739 : Nat := 4983230072969 + 3 ^ 40 * 2249739 * 2
def baseEnd_2249739 : Nat := 385065818055159539838715

theorem tailTrace_2249739 : CollatzResearch.WordTrace tailWord_2249739 prefixEnd_2249739 385065818055159539838715 := by
  unfold tailWord_2249739
  simp only [CollatzResearch.WordTrace]
  refine ⟨82054722396587302676608271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54703148264391535117738847 82054722396587302676608271)
  ·
    refine ⟨123082083594880954014912407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82054722396587302676608271 123082083594880954014912407)
    ·
      refine ⟨184623125392321431022368611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123082083594880954014912407 184623125392321431022368611)
      ·
        refine ⟨276934688088482146533552917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184623125392321431022368611 276934688088482146533552917)
        ·
          refine ⟨12981313504147600618760293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 276934688088482146533552917 12981313504147600618760293)
          ·
            refine ⟨2433996282027675116017555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12981313504147600618760293 2433996282027675116017555)
            ·
              refine ⟨3650994423041512674026333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433996282027675116017555 3650994423041512674026333)
              ·
                refine ⟨1369122908640567252759875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3650994423041512674026333 1369122908640567252759875)
                ·
                  refine ⟨2053684362960850879139813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369122908640567252759875 2053684362960850879139813)
                  ·
                    refine ⟨385065818055159539838715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2053684362960850879139813 385065818055159539838715)
                    ·
                      rfl

theorem cell23_2249739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 4].length) (baseStart_2249739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249739 prefixEnd_2249739 := by exact prefixLift 2249739
  have htrace : WordTrace (prefixWord ++ tailWord_2249739) baseStart_2249739 baseEnd_2249739 := by
    simpa [prefixWord, tailWord_2249739, baseEnd_2249739] using wordTrace_append hprefix tailTrace_2249739
  have hstable : (prefixWord ++ tailWord_2249739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249739).length < 2 ^ (prefixWord ++ tailWord_2249739).sum := by decide
  have hdescent : baseEnd_2249739 < baseStart_2249739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249745 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_2249745 : Nat := 118140960795 + 2249745 * 2 ^ 59
def prefixEnd_2249745 : Nat := 4983230072969 + 3 ^ 40 * 2249745 * 2
def baseEnd_2249745 : Nat := 1155200535049405596041117

theorem tailTrace_2249745 : CollatzResearch.WordTrace tailWord_2249745 prefixEnd_2249745 1155200535049405596041117 := by
  unfold tailWord_2249745
  simp only [CollatzResearch.WordTrace]
  refine ⟨82054941234565565701326689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54703294156377043800884459 82054941234565565701326689)
  ·
    refine ⟨61541205925924174275995017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82054941234565565701326689 61541205925924174275995017)
    ·
      refine ⟨46155904444443130706996263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61541205925924174275995017 46155904444443130706996263)
      ·
        refine ⟨69233856666664696060494395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46155904444443130706996263 69233856666664696060494395)
        ·
          refine ⟨103850784999997044090741593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69233856666664696060494395 103850784999997044090741593)
          ·
            refine ⟨77888088749997783068056195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103850784999997044090741593 77888088749997783068056195)
            ·
              refine ⟨116832133124996674602084293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77888088749997783068056195 116832133124996674602084293)
              ·
                refine ⟨21906024960936876487890805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116832133124996674602084293 21906024960936876487890805)
                ·
                  refine ⟨2053689840087832170739763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21906024960936876487890805 2053689840087832170739763)
                  ·
                    refine ⟨3080534760131748256109645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2053689840087832170739763 3080534760131748256109645)
                    ·
                      refine ⟨1155200535049405596041117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3080534760131748256109645 1155200535049405596041117)
                      ·
                        rfl

theorem cell23_2249745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_2249745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249745 prefixEnd_2249745 := by exact prefixLift 2249745
  have htrace : WordTrace (prefixWord ++ tailWord_2249745) baseStart_2249745 baseEnd_2249745 := by
    simpa [prefixWord, tailWord_2249745, baseEnd_2249745] using wordTrace_append hprefix tailTrace_2249745
  have hstable : (prefixWord ++ tailWord_2249745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249745).length < 2 ^ (prefixWord ++ tailWord_2249745).sum := by decide
  have hdescent : baseEnd_2249745 < baseStart_2249745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249746 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2249746 : Nat := 118140960795 + 2249746 * 2 ^ 59
def prefixEnd_2249746 : Nat := 4983230072969 + 3 ^ 40 * 2249746 * 2
def baseEnd_2249746 : Nat := 1155201048530060092128613

theorem tailTrace_2249746 : CollatzResearch.WordTrace tailWord_2249746 prefixEnd_2249746 1155201048530060092128613 := by
  unfold tailWord_2249746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20513744426890485718028273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54703318471707961914742061 20513744426890485718028273)
  ·
    refine ⟨15385308320167864288521205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20513744426890485718028273 15385308320167864288521205)
    ·
      refine ⟨1442372655015737277048863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15385308320167864288521205 1442372655015737277048863)
      ·
        refine ⟨2163558982523605915573295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442372655015737277048863 2163558982523605915573295)
        ·
          refine ⟨3245338473785408873359943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163558982523605915573295 3245338473785408873359943)
          ·
            refine ⟨4868007710678113310039915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245338473785408873359943 4868007710678113310039915)
            ·
              refine ⟨7302011566017169965059873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868007710678113310039915 7302011566017169965059873)
              ·
                refine ⟨5476508674512877473794905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7302011566017169965059873 5476508674512877473794905)
                ·
                  refine ⟨4107381505884658105346179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5476508674512877473794905 4107381505884658105346179)
                  ·
                    refine ⟨6161072258826987158019269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4107381505884658105346179 6161072258826987158019269)
                    ·
                      refine ⟨1155201048530060092128613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6161072258826987158019269 1155201048530060092128613)
                      ·
                        rfl

theorem cell23_2249746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2249746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249746 prefixEnd_2249746 := by exact prefixLift 2249746
  have htrace : WordTrace (prefixWord ++ tailWord_2249746) baseStart_2249746 baseEnd_2249746 := by
    simpa [prefixWord, tailWord_2249746, baseEnd_2249746] using wordTrace_append hprefix tailTrace_2249746
  have hstable : (prefixWord ++ tailWord_2249746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249746).length < 2 ^ (prefixWord ++ tailWord_2249746).sum := by decide
  have hdescent : baseEnd_2249746 < baseStart_2249746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249756 : List Nat := [2, 2, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_2249756 : Nat := 118140960795 + 2249756 * 2 ^ 59
def prefixEnd_2249756 : Nat := 4983230072969 + 3 ^ 40 * 2249756 * 2
def baseEnd_2249756 : Nat := 385068727778868351001189

theorem tailTrace_2249756 : CollatzResearch.WordTrace tailWord_2249756 prefixEnd_2249756 385068727778868351001189 := by
  unfold tailWord_2249756
  simp only [CollatzResearch.WordTrace]
  refine ⟨41027671218762857289988561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54703561625017143053318081 41027671218762857289988561)
  ·
    refine ⟨30770753414072142967491421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41027671218762857289988561 30770753414072142967491421)
    ·
      refine ⟨11539032530277053612809283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30770753414072142967491421 11539032530277053612809283)
      ·
        refine ⟨17308548795415580419213925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11539032530277053612809283 17308548795415580419213925)
        ·
          refine ⟨3245352899140421328602611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17308548795415580419213925 3245352899140421328602611)
          ·
            refine ⟨4868029348710631992903917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245352899140421328602611 4868029348710631992903917)
            ·
              refine ⟨1825511005766486997338969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4868029348710631992903917 1825511005766486997338969)
              ·
                refine ⟨1369133254324865248004227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1825511005766486997338969 1369133254324865248004227)
                ·
                  refine ⟨2053699881487297872006341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369133254324865248004227 2053699881487297872006341)
                  ·
                    refine ⟨385068727778868351001189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2053699881487297872006341 385068727778868351001189)
                    ·
                      rfl

theorem cell23_2249756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_2249756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249756 prefixEnd_2249756 := by exact prefixLift 2249756
  have htrace : WordTrace (prefixWord ++ tailWord_2249756) baseStart_2249756 baseEnd_2249756 := by
    simpa [prefixWord, tailWord_2249756, baseEnd_2249756] using wordTrace_append hprefix tailTrace_2249756
  have hstable : (prefixWord ++ tailWord_2249756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249756).length < 2 ^ (prefixWord ++ tailWord_2249756).sum := by decide
  have hdescent : baseEnd_2249756 < baseStart_2249756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249782 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2249782 : Nat := 118140960795 + 2249782 * 2 ^ 59
def prefixEnd_2249782 : Nat := 4983230072969 + 3 ^ 40 * 2249782 * 2
def baseEnd_2249782 : Nat := 385073177944540650426149

theorem tailTrace_2249782 : CollatzResearch.WordTrace tailWord_2249782 prefixEnd_2249782 385073177944540650426149 := by
  unfold tailWord_2249782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128518170964470063776475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54704193823621014013615733 5128518170964470063776475)
  ·
    refine ⟨7692777256446705095664713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5128518170964470063776475 7692777256446705095664713)
    ·
      refine ⟨5769582942335028821748535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7692777256446705095664713 5769582942335028821748535)
      ·
        refine ⟨8654374413502543232622803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769582942335028821748535 8654374413502543232622803)
        ·
          refine ⟨12981561620253814848934205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8654374413502543232622803 12981561620253814848934205)
          ·
            refine ⟨4868085607595180568350327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12981561620253814848934205 4868085607595180568350327)
            ·
              refine ⟨7302128411392770852525491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868085607595180568350327 7302128411392770852525491)
              ·
                refine ⟨10953192617089156278788237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7302128411392770852525491 10953192617089156278788237)
                ·
                  refine ⟨4107447231408433604545589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10953192617089156278788237 4107447231408433604545589)
                  ·
                    refine ⟨385073177944540650426149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4107447231408433604545589 385073177944540650426149)
                    ·
                      rfl

theorem cell23_2249782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2249782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249782 prefixEnd_2249782 := by exact prefixLift 2249782
  have htrace : WordTrace (prefixWord ++ tailWord_2249782) baseStart_2249782 baseEnd_2249782 := by
    simpa [prefixWord, tailWord_2249782, baseEnd_2249782] using wordTrace_append hprefix tailTrace_2249782
  have hstable : (prefixWord ++ tailWord_2249782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249782).length < 2 ^ (prefixWord ++ tailWord_2249782).sum := by decide
  have hdescent : baseEnd_2249782 < baseStart_2249782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249789 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_2249789 : Nat := 118140960795 + 2249789 * 2 ^ 59
def prefixEnd_2249789 : Nat := 4983230072969 + 3 ^ 40 * 2249789 * 2
def baseEnd_2249789 : Nat := 1155223128198203423890915

theorem tailTrace_2249789 : CollatzResearch.WordTrace tailWord_2249789 prefixEnd_2249789 1155223128198203423890915 := by
  unfold tailWord_2249789
  simp only [CollatzResearch.WordTrace]
  refine ⟨82056546046406161215928421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54704364030937440810618947 82056546046406161215928421)
  ·
    refine ⟨15385602383701155227986579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82056546046406161215928421 15385602383701155227986579)
    ·
      refine ⟨23078403575551732841979869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15385602383701155227986579 23078403575551732841979869)
      ·
        refine ⟨8654401340831899815742451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23078403575551732841979869 8654401340831899815742451)
        ·
          refine ⟨12981602011247849723613677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8654401340831899815742451 12981602011247849723613677)
          ·
            refine ⟨4868100754217943646355129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12981602011247849723613677 4868100754217943646355129)
            ·
              refine ⟨3651075565663457734766347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4868100754217943646355129 3651075565663457734766347)
              ·
                refine ⟨5476613348495186602149521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651075565663457734766347 5476613348495186602149521)
                ·
                  refine ⟨4107460011371389951612141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5476613348495186602149521 4107460011371389951612141)
                  ·
                    refine ⟨1540297504264271231854553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4107460011371389951612141 1540297504264271231854553)
                    ·
                      refine ⟨1155223128198203423890915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540297504264271231854553 1155223128198203423890915)
                      ·
                        rfl

theorem cell23_2249789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_2249789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249789 prefixEnd_2249789 := by exact prefixLift 2249789
  have htrace : WordTrace (prefixWord ++ tailWord_2249789) baseStart_2249789 baseEnd_2249789 := by
    simpa [prefixWord, tailWord_2249789, baseEnd_2249789] using wordTrace_append hprefix tailTrace_2249789
  have hstable : (prefixWord ++ tailWord_2249789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249789).length < 2 ^ (prefixWord ++ tailWord_2249789).sum := by decide
  have hdescent : baseEnd_2249789 < baseStart_2249789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249812 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_2249812 : Nat := 118140960795 + 2249812 * 2 ^ 59
def prefixEnd_2249812 : Nat := 4983230072969 + 3 ^ 40 * 2249812 * 2
def baseEnd_2249812 : Nat := 385078312751085611301103

theorem tailTrace_2249812 : CollatzResearch.WordTrace tailWord_2249812 prefixEnd_2249812 385078312751085611301103 := by
  unfold tailWord_2249812
  simp only [CollatzResearch.WordTrace]
  refine ⟨41028692462661418072007845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54704923283548557429343793 41028692462661418072007845)
  ·
    refine ⟨7692879836749015888501471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41028692462661418072007845 7692879836749015888501471)
    ·
      refine ⟨11539319755123523832752207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7692879836749015888501471 11539319755123523832752207)
      ·
        refine ⟨17308979632685285749128311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11539319755123523832752207 17308979632685285749128311)
        ·
          refine ⟨25963469449027928623692467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17308979632685285749128311 25963469449027928623692467)
          ·
            refine ⟨38945204173541892935538701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25963469449027928623692467 38945204173541892935538701)
            ·
              refine ⟨14604451565078209850827013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38945204173541892935538701 14604451565078209850827013)
              ·
                refine ⟨2738334668452164347030065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14604451565078209850827013 2738334668452164347030065)
                ·
                  refine ⟨2053751001339123260272549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738334668452164347030065 2053751001339123260272549)
                  ·
                    refine ⟨385078312751085611301103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2053751001339123260272549 385078312751085611301103)
                    ·
                      rfl

theorem cell23_2249812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_2249812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249812 prefixEnd_2249812 := by exact prefixLift 2249812
  have htrace : WordTrace (prefixWord ++ tailWord_2249812) baseStart_2249812 baseEnd_2249812 := by
    simpa [prefixWord, tailWord_2249812, baseEnd_2249812] using wordTrace_append hprefix tailTrace_2249812
  have hstable : (prefixWord ++ tailWord_2249812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249812).length < 2 ^ (prefixWord ++ tailWord_2249812).sum := by decide
  have hdescent : baseEnd_2249812 < baseStart_2249812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249818 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_2249818 : Nat := 118140960795 + 2249818 * 2 ^ 59
def prefixEnd_2249818 : Nat := 4983230072969 + 3 ^ 40 * 2249818 * 2
def baseEnd_2249818 : Nat := 1155238019137183810428281

theorem tailTrace_2249818 : CollatzResearch.WordTrace tailWord_2249818 prefixEnd_2249818 1155238019137183810428281 := by
  unfold tailWord_2249818
  simp only [CollatzResearch.WordTrace]
  refine ⟨20514400940825274792183527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54705069175534066112489405 20514400940825274792183527)
  ·
    refine ⟨30771601411237912188275291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20514400940825274792183527 30771601411237912188275291)
    ·
      refine ⟨46157402116856868282412937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30771601411237912188275291 46157402116856868282412937)
      ·
        refine ⟨34618051587642651211809703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46157402116856868282412937 34618051587642651211809703)
        ·
          refine ⟨51927077381463976817714555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34618051587642651211809703 51927077381463976817714555)
          ·
            refine ⟨77890616072195965226571833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51927077381463976817714555 77890616072195965226571833)
            ·
              refine ⟨58417962054146973919928875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77890616072195965226571833 58417962054146973919928875)
              ·
                refine ⟨87626943081220460879893313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58417962054146973919928875 87626943081220460879893313)
                ·
                  refine ⟨65720207310915345659919985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87626943081220460879893313 65720207310915345659919985)
                  ·
                    refine ⟨49290155483186509244939989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65720207310915345659919985 49290155483186509244939989)
                    ·
                      refine ⟨1155238019137183810428281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49290155483186509244939989 1155238019137183810428281)
                      ·
                        rfl

theorem cell23_2249818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_2249818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249818 prefixEnd_2249818 := by exact prefixLift 2249818
  have htrace : WordTrace (prefixWord ++ tailWord_2249818) baseStart_2249818 baseEnd_2249818 := by
    simpa [prefixWord, tailWord_2249818, baseEnd_2249818] using wordTrace_append hprefix tailTrace_2249818
  have hstable : (prefixWord ++ tailWord_2249818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249818).length < 2 ^ (prefixWord ++ tailWord_2249818).sum := by decide
  have hdescent : baseEnd_2249818 < baseStart_2249818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249852 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_2249852 : Nat := 118140960795 + 2249852 * 2 ^ 59
def prefixEnd_2249852 : Nat := 4983230072969 + 3 ^ 40 * 2249852 * 2
def baseEnd_2249852 : Nat := 1155255477479436677403125

theorem tailTrace_2249852 : CollatzResearch.WordTrace tailWord_2249852 prefixEnd_2249852 1155255477479436677403125 := by
  unfold tailWord_2249852
  simp only [CollatzResearch.WordTrace]
  refine ⟨41029421922588961487735905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54705895896785281983647873 41029421922588961487735905)
  ·
    refine ⟨30772066441941721115801929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41029421922588961487735905 30772066441941721115801929)
    ·
      refine ⟨23079049831456290836851447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30772066441941721115801929 23079049831456290836851447)
      ·
        refine ⟨34618574747184436255277171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23079049831456290836851447 34618574747184436255277171)
        ·
          refine ⟨51927862120776654382915757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34618574747184436255277171 51927862120776654382915757)
          ·
            refine ⟨19472948295291245393593409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51927862120776654382915757 19472948295291245393593409)
            ·
              refine ⟨14604711221468434045195057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19472948295291245393593409 14604711221468434045195057)
              ·
                refine ⟨10953533416101325533896293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14604711221468434045195057 10953533416101325533896293)
                ·
                  refine ⟨2053787515518998537605555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10953533416101325533896293 2053787515518998537605555)
                  ·
                    refine ⟨3080681273278497806408333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2053787515518998537605555 3080681273278497806408333)
                    ·
                      refine ⟨1155255477479436677403125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3080681273278497806408333 1155255477479436677403125)
                      ·
                        rfl

theorem cell23_2249852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_2249852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249852 prefixEnd_2249852 := by exact prefixLift 2249852
  have htrace : WordTrace (prefixWord ++ tailWord_2249852) baseStart_2249852 baseEnd_2249852 := by
    simpa [prefixWord, tailWord_2249852, baseEnd_2249852] using wordTrace_append hprefix tailTrace_2249852
  have hstable : (prefixWord ++ tailWord_2249852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249852).length < 2 ^ (prefixWord ++ tailWord_2249852).sum := by decide
  have hdescent : baseEnd_2249852 < baseStart_2249852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249885 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2249885 : Nat := 118140960795 + 2249885 * 2 ^ 59
def prefixEnd_2249885 : Nat := 4983230072969 + 3 ^ 40 * 2249885 * 2
def baseEnd_2249885 : Nat := 385090807447011682763491

theorem tailTrace_2249885 : CollatzResearch.WordTrace tailWord_2249885 prefixEnd_2249885 385090807447011682763491 := by
  unfold tailWord_2249885
  simp only [CollatzResearch.WordTrace]
  refine ⟨82060047454058369611423109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54706698302705579740948739 82060047454058369611423109)
  ·
    refine ⟨15386258897635944302141833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82060047454058369611423109 15386258897635944302141833)
    ·
      refine ⟨11539694173226958226606375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15386258897635944302141833 11539694173226958226606375)
      ·
        refine ⟨17309541259840437339909563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11539694173226958226606375 17309541259840437339909563)
        ·
          refine ⟨25964311889760656009864345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17309541259840437339909563 25964311889760656009864345)
          ·
            refine ⟨19473233917320492007398259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25964311889760656009864345 19473233917320492007398259)
            ·
              refine ⟨29209850875980738011097389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19473233917320492007398259 29209850875980738011097389)
              ·
                refine ⟨10953694078492776754161521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29209850875980738011097389 10953694078492776754161521)
                ·
                  refine ⟨8215270558869582565621141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10953694078492776754161521 8215270558869582565621141)
                  ·
                    refine ⟨385090807447011682763491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8215270558869582565621141 385090807447011682763491)
                    ·
                      rfl

theorem cell23_2249885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2249885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249885 prefixEnd_2249885 := by exact prefixLift 2249885
  have htrace : WordTrace (prefixWord ++ tailWord_2249885) baseStart_2249885 baseEnd_2249885 := by
    simpa [prefixWord, tailWord_2249885, baseEnd_2249885] using wordTrace_append hprefix tailTrace_2249885
  have hstable : (prefixWord ++ tailWord_2249885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249885).length < 2 ^ (prefixWord ++ tailWord_2249885).sum := by decide
  have hdescent : baseEnd_2249885 < baseStart_2249885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249886 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2249886 : Nat := 118140960795 + 2249886 * 2 ^ 59
def prefixEnd_2249886 : Nat := 4983230072969 + 3 ^ 40 * 2249886 * 2
def baseEnd_2249886 : Nat := 1155272935821689544377969

theorem tailTrace_2249886 : CollatzResearch.WordTrace tailWord_2249886 prefixEnd_2249886 1155272935821689544377969 := by
  unfold tailWord_2249886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10257510490881843347776189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54706722618036497854806341 10257510490881843347776189)
  ·
    refine ⟨3846566434080691255416071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10257510490881843347776189 3846566434080691255416071)
    ·
      refine ⟨5769849651121036883124107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3846566434080691255416071 5769849651121036883124107)
      ·
        refine ⟨8654774476681555324686161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769849651121036883124107 8654774476681555324686161)
        ·
          refine ⟨6491080857511166493514621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8654774476681555324686161 6491080857511166493514621)
          ·
            refine ⟨2434155321566687435067983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6491080857511166493514621 2434155321566687435067983)
            ·
              refine ⟨3651232982350031152601975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434155321566687435067983 3651232982350031152601975)
              ·
                refine ⟨5476849473525046728902963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651232982350031152601975 5476849473525046728902963)
                ·
                  refine ⟨8215274210287570093354445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5476849473525046728902963 8215274210287570093354445)
                  ·
                    refine ⟨3080727828857838785007917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8215274210287570093354445 3080727828857838785007917)
                    ·
                      refine ⟨1155272935821689544377969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3080727828857838785007917 1155272935821689544377969)
                      ·
                        rfl

theorem cell23_2249886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2249886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249886 prefixEnd_2249886 := by exact prefixLift 2249886
  have htrace : WordTrace (prefixWord ++ tailWord_2249886) baseStart_2249886 baseEnd_2249886 := by
    simpa [prefixWord, tailWord_2249886, baseEnd_2249886] using wordTrace_append hprefix tailTrace_2249886
  have hstable : (prefixWord ++ tailWord_2249886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249886).length < 2 ^ (prefixWord ++ tailWord_2249886).sum := by decide
  have hdescent : baseEnd_2249886 < baseStart_2249886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249945 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 6, 5]
def baseStart_2249945 : Nat := 118140960795 + 2249945 * 2 ^ 59
def prefixEnd_2249945 : Nat := 4983230072969 + 3 ^ 40 * 2249945 * 2
def baseEnd_2249945 : Nat := 385101077060101604513399

theorem tailTrace_2249945 : CollatzResearch.WordTrace tailWord_2249945 prefixEnd_2249945 385101077060101604513399 := by
  unfold tailWord_2249945
  simp only [CollatzResearch.WordTrace]
  refine ⟨82062235833840999858607289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54708157222560666572404859 82062235833840999858607289)
  ·
    refine ⟨61546676875380749893955467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82062235833840999858607289 61546676875380749893955467)
    ·
      refine ⟨92320015313071124840933201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61546676875380749893955467 92320015313071124840933201)
      ·
        refine ⟨69240011484803343630699901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92320015313071124840933201 69240011484803343630699901)
        ·
          refine ⟨25965004306801253861512463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69240011484803343630699901 25965004306801253861512463)
          ·
            refine ⟨38947506460201880792268695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25965004306801253861512463 38947506460201880792268695)
            ·
              refine ⟨58421259690302821188403043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38947506460201880792268695 58421259690302821188403043)
              ·
                refine ⟨87631889535454231782604565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58421259690302821188403043 87631889535454231782604565)
                ·
                  refine ⟨4107744821974417114809589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87631889535454231782604565 4107744821974417114809589)
                  ·
                    refine ⟨385101077060101604513399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4107744821974417114809589 385101077060101604513399)
                    ·
                      rfl

theorem cell23_2249945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_2249945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249945 prefixEnd_2249945 := by exact prefixLift 2249945
  have htrace : WordTrace (prefixWord ++ tailWord_2249945) baseStart_2249945 baseEnd_2249945 := by
    simpa [prefixWord, tailWord_2249945, baseEnd_2249945] using wordTrace_append hprefix tailTrace_2249945
  have hstable : (prefixWord ++ tailWord_2249945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249945).length < 2 ^ (prefixWord ++ tailWord_2249945).sum := by decide
  have hdescent : baseEnd_2249945 < baseStart_2249945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2249962 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2249962 : Nat := 118140960795 + 2249962 * 2 ^ 59
def prefixEnd_2249962 : Nat := 4983230072969 + 3 ^ 40 * 2249962 * 2
def baseEnd_2249962 : Nat := 385103986783810415675873

theorem tailTrace_2249962 : CollatzResearch.WordTrace tailWord_2249962 prefixEnd_2249962 385103986783810415675873 := by
  unfold tailWord_2249962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20515713968694852940494035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54708570583186274507984093 20515713968694852940494035)
  ·
    refine ⟨30773570953042279410741053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20515713968694852940494035 30773570953042279410741053)
    ·
      refine ⟨11540089107390854779027895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30773570953042279410741053 11540089107390854779027895)
      ·
        refine ⟨17310133661086282168541843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11540089107390854779027895 17310133661086282168541843)
        ·
          refine ⟨25965200491629423252812765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17310133661086282168541843 25965200491629423252812765)
          ·
            refine ⟨9736950184361033719804787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25965200491629423252812765 9736950184361033719804787)
            ·
              refine ⟨14605425276541550579707181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9736950184361033719804787 14605425276541550579707181)
              ·
                refine ⟨5477034478703081467390193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14605425276541550579707181 5477034478703081467390193)
                ·
                  refine ⟨4107775859027311100542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5477034478703081467390193 4107775859027311100542645)
                  ·
                    refine ⟨385103986783810415675873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4107775859027311100542645 385103986783810415675873)
                    ·
                      rfl

theorem cell23_2249962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2249962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2249962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2249962 prefixEnd_2249962 := by exact prefixLift 2249962
  have htrace : WordTrace (prefixWord ++ tailWord_2249962) baseStart_2249962 baseEnd_2249962 := by
    simpa [prefixWord, tailWord_2249962, baseEnd_2249962] using wordTrace_append hprefix tailTrace_2249962
  have hstable : (prefixWord ++ tailWord_2249962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2249962).length < 2 ^ (prefixWord ++ tailWord_2249962).sum := by decide
  have hdescent : baseEnd_2249962 < baseStart_2249962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2249962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250005 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 10]
def baseStart_2250005 : Nat := 118140960795 + 2250005 * 2 ^ 59
def prefixEnd_2250005 : Nat := 4983230072969 + 3 ^ 40 * 2250005 * 2
def baseEnd_2250005 : Nat := 128370448891063842087769

theorem tailTrace_2250005 : CollatzResearch.WordTrace tailWord_2250005 prefixEnd_2250005 128370448891063842087769 := by
  unfold tailWord_2250005
  simp only [CollatzResearch.WordTrace]
  refine ⟨82064424213623630105791469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54709616142415753403860979 82064424213623630105791469)
  ·
    refine ⟨30774159080108861289671801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82064424213623630105791469 30774159080108861289671801)
    ·
      refine ⟨23080619310081645967253851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30774159080108861289671801 23080619310081645967253851)
      ·
        refine ⟨34620928965122468950880777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23080619310081645967253851 34620928965122468950880777)
        ·
          refine ⟨25965696723841851713160583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34620928965122468950880777 25965696723841851713160583)
          ·
            refine ⟨38948545085762777569740875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25965696723841851713160583 38948545085762777569740875)
            ·
              refine ⟨58422817628644166354611313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38948545085762777569740875 58422817628644166354611313)
              ·
                refine ⟨43817113221483124765958485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58422817628644166354611313 43817113221483124765958485)
                ·
                  refine ⟨128370448891063842087769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43817113221483124765958485 128370448891063842087769)
                  ·
                    rfl

theorem cell23_2250005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_2250005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250005 prefixEnd_2250005 := by exact prefixLift 2250005
  have htrace : WordTrace (prefixWord ++ tailWord_2250005) baseStart_2250005 baseEnd_2250005 := by
    simpa [prefixWord, tailWord_2250005, baseEnd_2250005] using wordTrace_append hprefix tailTrace_2250005
  have hstable : (prefixWord ++ tailWord_2250005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250005).length < 2 ^ (prefixWord ++ tailWord_2250005).sum := by decide
  have hdescent : baseEnd_2250005 < baseStart_2250005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250016 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2250016 : Nat := 118140960795 + 2250016 * 2 ^ 59
def prefixEnd_2250016 : Nat := 4983230072969 + 3 ^ 40 * 2250016 * 2
def baseEnd_2250016 : Nat := 1155339688306774035752371

theorem tailTrace_2250016 : CollatzResearch.WordTrace tailWord_2250016 prefixEnd_2250016 1155339688306774035752371 := by
  unfold tailWord_2250016
  simp only [CollatzResearch.WordTrace]
  refine ⟨41032412708291889492220951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54709883611055852656294601 41032412708291889492220951)
  ·
    refine ⟨61548619062437834238331427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41032412708291889492220951 61548619062437834238331427)
    ·
      refine ⟨92322928593656751357497141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61548619062437834238331427 92322928593656751357497141)
      ·
        refine ⟨8655274555655320439765357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92322928593656751357497141 8655274555655320439765357)
        ·
          refine ⟨3245727958370745164912009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8655274555655320439765357 3245727958370745164912009)
          ·
            refine ⟨2434295968778058873684007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3245727958370745164912009 2434295968778058873684007)
            ·
              refine ⟨3651443953167088310526011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434295968778058873684007 3651443953167088310526011)
              ·
                refine ⟨5477165929750632465789017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651443953167088310526011 5477165929750632465789017)
                ·
                  refine ⟨4107874447312974349341763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5477165929750632465789017 4107874447312974349341763)
                  ·
                    refine ⟨6161811670969461524012645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4107874447312974349341763 6161811670969461524012645)
                    ·
                      refine ⟨1155339688306774035752371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6161811670969461524012645 1155339688306774035752371)
                      ·
                        rfl

theorem cell23_2250016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2250016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250016 prefixEnd_2250016 := by exact prefixLift 2250016
  have htrace : WordTrace (prefixWord ++ tailWord_2250016) baseStart_2250016 baseEnd_2250016 := by
    simpa [prefixWord, tailWord_2250016, baseEnd_2250016] using wordTrace_append hprefix tailTrace_2250016
  have hstable : (prefixWord ++ tailWord_2250016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250016).length < 2 ^ (prefixWord ++ tailWord_2250016).sum := by decide
  have hdescent : baseEnd_2250016 < baseStart_2250016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250019 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 3]
def baseStart_2250019 : Nat := 118140960795 + 2250019 * 2 ^ 59
def prefixEnd_2250019 : Nat := 4983230072969 + 3 ^ 40 * 2250019 * 2
def baseEnd_2250019 : Nat := 1155341228748737524014857

theorem tailTrace_2250019 : CollatzResearch.WordTrace tailWord_2250019 prefixEnd_2250019 1155341228748737524014857 := by
  unfold tailWord_2250019
  simp only [CollatzResearch.WordTrace]
  refine ⟨82064934835572910496801111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54709956557048606997867407 82064934835572910496801111)
  ·
    refine ⟨123097402253359365745201667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82064934835572910496801111 123097402253359365745201667)
    ·
      refine ⟨184646103380039048617802501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123097402253359365745201667 184646103380039048617802501)
      ·
        refine ⟨34621144383757321615837969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184646103380039048617802501 34621144383757321615837969)
        ·
          refine ⟨25965858287817991211878477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34621144383757321615837969 25965858287817991211878477)
          ·
            refine ⟨9737196857931746704454429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25965858287817991211878477 9737196857931746704454429)
            ·
              refine ⟨3651448821724405014170411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9737196857931746704454429 3651448821724405014170411)
              ·
                refine ⟨5477173232586607521255617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651448821724405014170411 5477173232586607521255617)
                ·
                  refine ⟨4107879924439955640941713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5477173232586607521255617 4107879924439955640941713)
                  ·
                    refine ⟨3080909943329966730706285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4107879924439955640941713 3080909943329966730706285)
                    ·
                      refine ⟨1155341228748737524014857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3080909943329966730706285 1155341228748737524014857)
                      ·
                        rfl

theorem cell23_2250019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_2250019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250019 prefixEnd_2250019 := by exact prefixLift 2250019
  have htrace : WordTrace (prefixWord ++ tailWord_2250019) baseStart_2250019 baseEnd_2250019 := by
    simpa [prefixWord, tailWord_2250019, baseEnd_2250019] using wordTrace_append hprefix tailTrace_2250019
  have hstable : (prefixWord ++ tailWord_2250019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250019).length < 2 ^ (prefixWord ++ tailWord_2250019).sum := by decide
  have hdescent : baseEnd_2250019 < baseStart_2250019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250029 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2250029 : Nat := 118140960795 + 2250029 * 2 ^ 59
def prefixEnd_2250029 : Nat := 4983230072969 + 3 ^ 40 * 2250029 * 2
def baseEnd_2250029 : Nat := 1155346363555282484889811

theorem tailTrace_2250029 : CollatzResearch.WordTrace tailWord_2250029 prefixEnd_2250029 1155346363555282484889811 := by
  unfold tailWord_2250029
  simp only [CollatzResearch.WordTrace]
  refine ⟨82065299565536682204665141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54710199710357788136443427 82065299565536682204665141)
  ·
    refine ⟨7693621834269063956687357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82065299565536682204665141 7693621834269063956687357)
    ·
      refine ⟨2885108187850898983757759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7693621834269063956687357 2885108187850898983757759)
      ·
        refine ⟨4327662281776348475636639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2885108187850898983757759 4327662281776348475636639)
        ·
          refine ⟨6491493422664522713454959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327662281776348475636639 6491493422664522713454959)
          ·
            refine ⟨9737240133996784070182439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6491493422664522713454959 9737240133996784070182439)
            ·
              refine ⟨14605860200995176105273659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9737240133996784070182439 14605860200995176105273659)
              ·
                refine ⟨21908790301492764157910489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14605860200995176105273659 21908790301492764157910489)
                ·
                  refine ⟨16431592726119573118432867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21908790301492764157910489 16431592726119573118432867)
                  ·
                    refine ⟨24647389089179359677649301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16431592726119573118432867 24647389089179359677649301)
                    ·
                      refine ⟨1155346363555282484889811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24647389089179359677649301 1155346363555282484889811)
                      ·
                        rfl

theorem cell23_2250029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2250029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250029 prefixEnd_2250029 := by exact prefixLift 2250029
  have htrace : WordTrace (prefixWord ++ tailWord_2250029) baseStart_2250029 baseEnd_2250029 := by
    simpa [prefixWord, tailWord_2250029, baseEnd_2250029] using wordTrace_append hprefix tailTrace_2250029
  have hstable : (prefixWord ++ tailWord_2250029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250029).length < 2 ^ (prefixWord ++ tailWord_2250029).sum := by decide
  have hdescent : baseEnd_2250029 < baseStart_2250029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250069 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2250069 : Nat := 118140960795 + 2250069 * 2 ^ 59
def prefixEnd_2250069 : Nat := 4983230072969 + 3 ^ 40 * 2250069 * 2
def baseEnd_2250069 : Nat := 385122300927154109463209

theorem tailTrace_2250069 : CollatzResearch.WordTrace tailWord_2250069 prefixEnd_2250069 385122300927154109463209 := by
  unfold tailWord_2250069
  simp only [CollatzResearch.WordTrace]
  refine ⟨82066758485391769036121261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54711172323594512690747507 82066758485391769036121261)
  ·
    refine ⟨30775034432021913388545473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82066758485391769036121261 30775034432021913388545473)
    ·
      refine ⟨23081275824016435041409105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30775034432021913388545473 23081275824016435041409105)
      ·
        refine ⟨17310956868012326281056829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23081275824016435041409105 17310956868012326281056829)
        ·
          refine ⟨6491608825504622355396311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17310956868012326281056829 6491608825504622355396311)
          ·
            refine ⟨9737413238256933533094467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6491608825504622355396311 9737413238256933533094467)
            ·
              refine ⟨14606119857385400299641701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9737413238256933533094467 14606119857385400299641701)
              ·
                refine ⟨2738647473259762556182819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14606119857385400299641701 2738647473259762556182819)
                ·
                  refine ⟨4107971209889643834274229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738647473259762556182819 4107971209889643834274229)
                  ·
                    refine ⟨385122300927154109463209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4107971209889643834274229 385122300927154109463209)
                    ·
                      rfl

theorem cell23_2250069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2250069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250069 prefixEnd_2250069 := by exact prefixLift 2250069
  have htrace : WordTrace (prefixWord ++ tailWord_2250069) baseStart_2250069 baseEnd_2250069 := by
    simpa [prefixWord, tailWord_2250069, baseEnd_2250069] using wordTrace_append hprefix tailTrace_2250069
  have hstable : (prefixWord ++ tailWord_2250069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250069).length < 2 ^ (prefixWord ++ tailWord_2250069).sum := by decide
  have hdescent : baseEnd_2250069 < baseStart_2250069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250083 : List Nat := [1, 1, 1, 5, 2, 2, 3, 3, 1, 1, 3]
def baseStart_2250083 : Nat := 118140960795 + 2250083 * 2 ^ 59
def prefixEnd_2250083 : Nat := 4983230072969 + 3 ^ 40 * 2250083 * 2
def baseEnd_2250083 : Nat := 1155374091510625273614563

theorem tailTrace_2250083 : CollatzResearch.WordTrace tailWord_2250083 prefixEnd_2250083 1155374091510625273614563 := by
  unfold tailWord_2250083
  simp only [CollatzResearch.WordTrace]
  refine ⟨82067269107341049427130903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54711512738227366284753935 82067269107341049427130903)
  ·
    refine ⟨123100903661011574140696355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82067269107341049427130903 123100903661011574140696355)
    ·
      refine ⟨184651355491517361211044533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123100903661011574140696355 184651355491517361211044533)
      ·
        refine ⟨17311064577329752613535425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 184651355491517361211044533 17311064577329752613535425)
        ·
          refine ⟨12983298432997314460151569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17311064577329752613535425 12983298432997314460151569)
          ·
            refine ⟨9737473824747985845113677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12983298432997314460151569 9737473824747985845113677)
            ·
              refine ⟨3651552684280494691917629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9737473824747985845113677 3651552684280494691917629)
              ·
                refine ⟨1369332256605185509469111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3651552684280494691917629 1369332256605185509469111)
                ·
                  refine ⟨2053998384907778264203667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369332256605185509469111 2053998384907778264203667)
                  ·
                    refine ⟨3080997577361667396305501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2053998384907778264203667 3080997577361667396305501)
                    ·
                      refine ⟨1155374091510625273614563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3080997577361667396305501 1155374091510625273614563)
                      ·
                        rfl

theorem cell23_2250083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_2250083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250083 prefixEnd_2250083 := by exact prefixLift 2250083
  have htrace : WordTrace (prefixWord ++ tailWord_2250083) baseStart_2250083 baseEnd_2250083 := by
    simpa [prefixWord, tailWord_2250083, baseEnd_2250083] using wordTrace_append hprefix tailTrace_2250083
  have hstable : (prefixWord ++ tailWord_2250083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250083).length < 2 ^ (prefixWord ++ tailWord_2250083).sum := by decide
  have hdescent : baseEnd_2250083 < baseStart_2250083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250109 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_2250109 : Nat := 118140960795 + 2250109 * 2 ^ 59
def prefixEnd_2250109 : Nat := 4983230072969 + 3 ^ 40 * 2250109 * 2
def baseEnd_2250109 : Nat := 1155387442007642171889443

theorem tailTrace_2250109 : CollatzResearch.WordTrace tailWord_2250109 prefixEnd_2250109 1155387442007642171889443 := by
  unfold tailWord_2250109
  simp only [CollatzResearch.WordTrace]
  refine ⟨82068217405246855867577381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54712144936831237245051587 82068217405246855867577381)
  ·
    refine ⟨15387790763483785475170759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82068217405246855867577381 15387790763483785475170759)
    ·
      refine ⟨23081686145225678212756139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15387790763483785475170759 23081686145225678212756139)
      ·
        refine ⟨34622529217838517319134209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23081686145225678212756139 34622529217838517319134209)
        ·
          refine ⟨25966896913378887989350657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34622529217838517319134209 25966896913378887989350657)
          ·
            refine ⟨19475172685034165992012993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25966896913378887989350657 19475172685034165992012993)
            ·
              refine ⟨14606379513775624494009745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19475172685034165992012993 14606379513775624494009745)
              ·
                refine ⟨10954784635331718370507309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14606379513775624494009745 10954784635331718370507309)
                ·
                  refine ⟨4108044238249394388940241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10954784635331718370507309 4108044238249394388940241)
                  ·
                    refine ⟨3081033178687045791705181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4108044238249394388940241 3081033178687045791705181)
                    ·
                      refine ⟨1155387442007642171889443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081033178687045791705181 1155387442007642171889443)
                      ·
                        rfl

theorem cell23_2250109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_2250109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250109 prefixEnd_2250109 := by exact prefixLift 2250109
  have htrace : WordTrace (prefixWord ++ tailWord_2250109) baseStart_2250109 baseEnd_2250109 := by
    simpa [prefixWord, tailWord_2250109, baseEnd_2250109] using wordTrace_append hprefix tailTrace_2250109
  have hstable : (prefixWord ++ tailWord_2250109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250109).length < 2 ^ (prefixWord ++ tailWord_2250109).sum := by decide
  have hdescent : baseEnd_2250109 < baseStart_2250109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250116 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_2250116 : Nat := 118140960795 + 2250116 * 2 ^ 59
def prefixEnd_2250116 : Nat := 4983230072969 + 3 ^ 40 * 2250116 * 2
def baseEnd_2250116 : Nat := 385130345457407881500637

theorem tailTrace_2250116 : CollatzResearch.WordTrace tailWord_2250116 prefixEnd_2250116 385130345457407881500637 := by
  unfold tailWord_2250116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41034236358110748031541101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54712315144147664042054801 41034236358110748031541101)
  ·
    refine ⟨15387838634291530511827913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41034236358110748031541101 15387838634291530511827913)
    ·
      refine ⟨11540878975718647883870935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15387838634291530511827913 11540878975718647883870935)
      ·
        refine ⟨17311318463577971825806403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11540878975718647883870935 17311318463577971825806403)
        ·
          refine ⟨25966977695366957738709605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17311318463577971825806403 25966977695366957738709605)
          ·
            refine ⟨4868808317881304576008051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25966977695366957738709605 4868808317881304576008051)
            ·
              refine ⟨7303212476821956864012077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868808317881304576008051 7303212476821956864012077)
              ·
                refine ⟨2738704678808233824004529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7303212476821956864012077 2738704678808233824004529)
                ·
                  refine ⟨2054028509106175368003397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738704678808233824004529 2054028509106175368003397)
                  ·
                    refine ⟨385130345457407881500637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054028509106175368003397 385130345457407881500637)
                    ·
                      rfl

theorem cell23_2250116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_2250116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250116 prefixEnd_2250116 := by exact prefixLift 2250116
  have htrace : WordTrace (prefixWord ++ tailWord_2250116) baseStart_2250116 baseEnd_2250116 := by
    simpa [prefixWord, tailWord_2250116, baseEnd_2250116] using wordTrace_append hprefix tailTrace_2250116
  have hstable : (prefixWord ++ tailWord_2250116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250116).length < 2 ^ (prefixWord ++ tailWord_2250116).sum := by decide
  have hdescent : baseEnd_2250116 < baseStart_2250116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250136 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2250136 : Nat := 118140960795 + 2250136 * 2 ^ 59
def prefixEnd_2250136 : Nat := 4983230072969 + 3 ^ 40 * 2250136 * 2
def baseEnd_2250136 : Nat := 1155401305985313566251819

theorem tailTrace_2250136 : CollatzResearch.WordTrace tailWord_2250136 prefixEnd_2250136 1155401305985313566251819 := by
  unfold tailWord_2250136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41034601088074519739405131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54712801450766026319206841 41034601088074519739405131)
  ·
    refine ⟨61551901632111779609107697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41034601088074519739405131 61551901632111779609107697)
    ·
      refine ⟨46163926224083834706830773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61551901632111779609107697 46163926224083834706830773)
      ·
        refine ⟨4327868083507859503765385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46163926224083834706830773 4327868083507859503765385)
        ·
          refine ⟨3245901062630894627824039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4327868083507859503765385 3245901062630894627824039)
          ·
            refine ⟨4868851593946341941736059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245901062630894627824039 4868851593946341941736059)
            ·
              refine ⟨7303277390919512912604089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868851593946341941736059 7303277390919512912604089)
              ·
                refine ⟨5477458043189634684453067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7303277390919512912604089 5477458043189634684453067)
                ·
                  refine ⟨8216187064784452026679601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5477458043189634684453067 8216187064784452026679601)
                  ·
                    refine ⟨6162140298588339020009701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8216187064784452026679601 6162140298588339020009701)
                    ·
                      refine ⟨1155401305985313566251819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6162140298588339020009701 1155401305985313566251819)
                      ·
                        rfl

theorem cell23_2250136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2250136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250136 prefixEnd_2250136 := by exact prefixLift 2250136
  have htrace : WordTrace (prefixWord ++ tailWord_2250136) baseStart_2250136 baseEnd_2250136 := by
    simpa [prefixWord, tailWord_2250136, baseEnd_2250136] using wordTrace_append hprefix tailTrace_2250136
  have hstable : (prefixWord ++ tailWord_2250136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250136).length < 2 ^ (prefixWord ++ tailWord_2250136).sum := by decide
  have hdescent : baseEnd_2250136 < baseStart_2250136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250140 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2250140 : Nat := 118140960795 + 2250140 * 2 ^ 59
def prefixEnd_2250140 : Nat := 4983230072969 + 3 ^ 40 * 2250140 * 2
def baseEnd_2250140 : Nat := 1155403359907931550601801

theorem tailTrace_2250140 : CollatzResearch.WordTrace tailWord_2250140 prefixEnd_2250140 1155403359907931550601801 := by
  unfold tailWord_2250140
  simp only [CollatzResearch.WordTrace]
  refine ⟨41034674034067274080977937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54712898712089698774637249 41034674034067274080977937)
  ·
    refine ⟨30776005525550455560733453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41034674034067274080977937 30776005525550455560733453)
    ·
      refine ⟨11541002072081420835275045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30776005525550455560733453 11541002072081420835275045)
      ·
        refine ⟨2163937888515266406614071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11541002072081420835275045 2163937888515266406614071)
        ·
          refine ⟨3245906832772899609921107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163937888515266406614071 3245906832772899609921107)
          ·
            refine ⟨4868860249159349414881661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245906832772899609921107 4868860249159349414881661)
            ·
              refine ⟨1825822593434756030580623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4868860249159349414881661 1825822593434756030580623)
              ·
                refine ⟨2738733890152134045870935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825822593434756030580623 2738733890152134045870935)
                ·
                  refine ⟨4108100835228201068806403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738733890152134045870935 4108100835228201068806403)
                  ·
                    refine ⟨6162151252842301603209605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4108100835228201068806403 6162151252842301603209605)
                    ·
                      refine ⟨1155403359907931550601801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6162151252842301603209605 1155403359907931550601801)
                      ·
                        rfl

theorem cell23_2250140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2250140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250140 prefixEnd_2250140 := by exact prefixLift 2250140
  have htrace : WordTrace (prefixWord ++ tailWord_2250140) baseStart_2250140 baseEnd_2250140 := by
    simpa [prefixWord, tailWord_2250140, baseEnd_2250140] using wordTrace_append hprefix tailTrace_2250140
  have hstable : (prefixWord ++ tailWord_2250140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250140).length < 2 ^ (prefixWord ++ tailWord_2250140).sum := by decide
  have hdescent : baseEnd_2250140 < baseStart_2250140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250143 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 1, 2, 3]
def baseStart_2250143 : Nat := 118140960795 + 2250143 * 2 ^ 59
def prefixEnd_2250143 : Nat := 4983230072969 + 3 ^ 40 * 2250143 * 2
def baseEnd_2250143 : Nat := 1155404900349895038864287

theorem tailTrace_2250143 : CollatzResearch.WordTrace tailWord_2250143 prefixEnd_2250143 1155404900349895038864287 := by
  unfold tailWord_2250143
  simp only [CollatzResearch.WordTrace]
  refine ⟨82069457487123679674315083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54712971658082453116210055 82069457487123679674315083)
  ·
    refine ⟨123104186230685519511472625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82069457487123679674315083 123104186230685519511472625)
    ·
      refine ⟨92328139673014139633604469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123104186230685519511472625 92328139673014139633604469)
      ·
        refine ⟨8655763094345075590650419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92328139673014139633604469 8655763094345075590650419)
        ·
          refine ⟨12983644641517613385975629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8655763094345075590650419 12983644641517613385975629)
          ·
            refine ⟨4868866740569105019740861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12983644641517613385975629 4868866740569105019740861)
            ·
              refine ⟨1825825027713414382402823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4868866740569105019740861 1825825027713414382402823)
              ·
                refine ⟨2738737541570121573604235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825825027713414382402823 2738737541570121573604235)
                ·
                  refine ⟨4108106312355182360406353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738737541570121573604235 4108106312355182360406353)
                  ·
                    refine ⟨3081079734266386770304765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4108106312355182360406353 3081079734266386770304765)
                    ·
                      refine ⟨1155404900349895038864287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081079734266386770304765 1155404900349895038864287)
                      ·
                        rfl

theorem cell23_2250143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_2250143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250143 prefixEnd_2250143 := by exact prefixLift 2250143
  have htrace : WordTrace (prefixWord ++ tailWord_2250143) baseStart_2250143 baseEnd_2250143 := by
    simpa [prefixWord, tailWord_2250143, baseEnd_2250143] using wordTrace_append hprefix tailTrace_2250143
  have hstable : (prefixWord ++ tailWord_2250143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250143).length < 2 ^ (prefixWord ++ tailWord_2250143).sum := by decide
  have hdescent : baseEnd_2250143 < baseStart_2250143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250156 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_2250156 : Nat := 118140960795 + 2250156 * 2 ^ 59
def prefixEnd_2250156 : Nat := 4983230072969 + 3 ^ 40 * 2250156 * 2
def baseEnd_2250156 : Nat := 1155411575598403488001727

theorem tailTrace_2250156 : CollatzResearch.WordTrace tailWord_2250156 prefixEnd_2250156 1155411575598403488001727 := by
  unfold tailWord_2250156
  simp only [CollatzResearch.WordTrace]
  refine ⟨41034965818038291447269161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54713287757384388596358881 41034965818038291447269161)
  ·
    refine ⟨30776224363528718585451871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41034965818038291447269161 30776224363528718585451871)
    ·
      refine ⟨46164336545293077878177807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30776224363528718585451871 46164336545293077878177807)
      ·
        refine ⟨69246504817939616817266711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46164336545293077878177807 69246504817939616817266711)
        ·
          refine ⟨103869757226909425225900067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69246504817939616817266711 103869757226909425225900067)
          ·
            refine ⟨155804635840364137838850101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103869757226909425225900067 155804635840364137838850101)
            ·
              refine ⟨14606684610034137922392197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155804635840364137838850101 14606684610034137922392197)
              ·
                refine ⟨2738753364381400860448537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14606684610034137922392197 2738753364381400860448537)
                ·
                  refine ⟨2054065023286050645336403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738753364381400860448537 2054065023286050645336403)
                  ·
                    refine ⟨3081097534929075968004605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054065023286050645336403 3081097534929075968004605)
                    ·
                      refine ⟨1155411575598403488001727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081097534929075968004605 1155411575598403488001727)
                      ·
                        rfl

theorem cell23_2250156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_2250156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250156 prefixEnd_2250156 := by exact prefixLift 2250156
  have htrace : WordTrace (prefixWord ++ tailWord_2250156) baseStart_2250156 baseEnd_2250156 := by
    simpa [prefixWord, tailWord_2250156, baseEnd_2250156] using wordTrace_append hprefix tailTrace_2250156
  have hstable : (prefixWord ++ tailWord_2250156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250156).length < 2 ^ (prefixWord ++ tailWord_2250156).sum := by decide
  have hdescent : baseEnd_2250156 < baseStart_2250156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250157 : List Nat := [1, 5, 2, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2250157 : Nat := 118140960795 + 2250157 * 2 ^ 59
def prefixEnd_2250157 : Nat := 4983230072969 + 3 ^ 40 * 2250157 * 2
def baseEnd_2250157 : Nat := 1155412089079057984089223

theorem tailTrace_2250157 : CollatzResearch.WordTrace tailWord_2250157 prefixEnd_2250157 1155412089079057984089223 := by
  unfold tailWord_2250157
  simp only [CollatzResearch.WordTrace]
  refine ⟨82069968109072960065324725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54713312072715306710216483 82069968109072960065324725)
  ·
    refine ⟨7694059510225590006124193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82069968109072960065324725 7694059510225590006124193)
    ·
      refine ⟨5770544632669192504593145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7694059510225590006124193 5770544632669192504593145)
      ·
        refine ⟨4327908474501894378444859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5770544632669192504593145 4327908474501894378444859)
        ·
          refine ⟨6491862711752841567667289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327908474501894378444859 6491862711752841567667289)
          ·
            refine ⟨4868897033814631175750467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6491862711752841567667289 4868897033814631175750467)
            ·
              refine ⟨7303345550721946763625701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868897033814631175750467 7303345550721946763625701)
              ·
                refine ⟨1369377290760365018179819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7303345550721946763625701 1369377290760365018179819)
                ·
                  refine ⟨2054065936140547527269729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369377290760365018179819 2054065936140547527269729)
                  ·
                    refine ⟨1540549452105410645452297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2054065936140547527269729 1540549452105410645452297)
                    ·
                      refine ⟨1155412089079057984089223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540549452105410645452297 1155412089079057984089223)
                      ·
                        rfl

theorem cell23_2250157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2250157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250157 prefixEnd_2250157 := by exact prefixLift 2250157
  have htrace : WordTrace (prefixWord ++ tailWord_2250157) baseStart_2250157 baseEnd_2250157 := by
    simpa [prefixWord, tailWord_2250157, baseEnd_2250157] using wordTrace_append hprefix tailTrace_2250157
  have hstable : (prefixWord ++ tailWord_2250157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250157).length < 2 ^ (prefixWord ++ tailWord_2250157).sum := by decide
  have hdescent : baseEnd_2250157 < baseStart_2250157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250209 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_2250209 : Nat := 118140960795 + 2250209 * 2 ^ 59
def prefixEnd_2250209 : Nat := 4983230072969 + 3 ^ 40 * 2250209 * 2
def baseEnd_2250209 : Nat := 1155438790073091780638983

theorem tailTrace_2250209 : CollatzResearch.WordTrace tailWord_2250209 prefixEnd_2250209 1155438790073091780638983 := by
  unfold tailWord_2250209
  simp only [CollatzResearch.WordTrace]
  refine ⟨82071864704884572946217681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54714576469923048630811787 82071864704884572946217681)
  ·
    refine ⟨61553898528663429709663261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82071864704884572946217681 61553898528663429709663261)
    ·
      refine ⟨23082711948248786141123723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61553898528663429709663261 23082711948248786141123723)
      ·
        refine ⟨34624067922373179211685585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23082711948248786141123723 34624067922373179211685585)
        ·
          refine ⟨25968050941779884408764189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34624067922373179211685585 25968050941779884408764189)
          ·
            refine ⟨9738019103167456653286571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25968050941779884408764189 9738019103167456653286571)
            ·
              refine ⟨14607028654751184979929857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9738019103167456653286571 14607028654751184979929857)
              ·
                refine ⟨10955271491063388734947393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14607028654751184979929857 10955271491063388734947393)
                ·
                  refine ⟨8216453618297541551210545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10955271491063388734947393 8216453618297541551210545)
                  ·
                    refine ⟨6162340213723156163407909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8216453618297541551210545 6162340213723156163407909)
                    ·
                      refine ⟨1155438790073091780638983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6162340213723156163407909 1155438790073091780638983)
                      ·
                        rfl

theorem cell23_2250209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_2250209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250209 prefixEnd_2250209 := by exact prefixLift 2250209
  have htrace : WordTrace (prefixWord ++ tailWord_2250209) baseStart_2250209 baseEnd_2250209 := by
    simpa [prefixWord, tailWord_2250209, baseEnd_2250209] using wordTrace_append hprefix tailTrace_2250209
  have hstable : (prefixWord ++ tailWord_2250209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250209).length < 2 ^ (prefixWord ++ tailWord_2250209).sum := by decide
  have hdescent : baseEnd_2250209 < baseStart_2250209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250226 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2250226 : Nat := 118140960795 + 2250226 * 2 ^ 59
def prefixEnd_2250226 : Nat := 4983230072969 + 3 ^ 40 * 2250226 * 2
def baseEnd_2250226 : Nat := 1155447519244218214126405

theorem tailTrace_2250226 : CollatzResearch.WordTrace tailWord_2250226 prefixEnd_2250226 1155447519244218214126405 := by
  unfold tailWord_2250226
  simp only [CollatzResearch.WordTrace]
  refine ⟨20518121186455746212396633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54714989830548656566391021 20518121186455746212396633)
  ·
    refine ⟨15388590889841809659297475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20518121186455746212396633 15388590889841809659297475)
    ·
      refine ⟨23082886334762714488946213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15388590889841809659297475 23082886334762714488946213)
      ·
        refine ⟨4328041187768008966677415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23082886334762714488946213 4328041187768008966677415)
        ·
          refine ⟨6492061781652013450016123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328041187768008966677415 6492061781652013450016123)
          ·
            refine ⟨9738092672478020175024185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6492061781652013450016123 9738092672478020175024185)
            ·
              refine ⟨7303569504358515131268139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9738092672478020175024185 7303569504358515131268139)
              ·
                refine ⟨10955354256537772696902209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7303569504358515131268139 10955354256537772696902209)
                ·
                  refine ⟨8216515692403329522676657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10955354256537772696902209 8216515692403329522676657)
                  ·
                    refine ⟨6162386769302497142007493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8216515692403329522676657 6162386769302497142007493)
                    ·
                      refine ⟨1155447519244218214126405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6162386769302497142007493 1155447519244218214126405)
                      ·
                        rfl

theorem cell23_2250226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2250226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250226 prefixEnd_2250226 := by exact prefixLift 2250226
  have htrace : WordTrace (prefixWord ++ tailWord_2250226) baseStart_2250226 baseEnd_2250226 := by
    simpa [prefixWord, tailWord_2250226, baseEnd_2250226] using wordTrace_append hprefix tailTrace_2250226
  have hstable : (prefixWord ++ tailWord_2250226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250226).length < 2 ^ (prefixWord ++ tailWord_2250226).sum := by decide
  have hdescent : baseEnd_2250226 < baseStart_2250226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250230 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_2250230 : Nat := 118140960795 + 2250230 * 2 ^ 59
def prefixEnd_2250230 : Nat := 4983230072969 + 3 ^ 40 * 2250230 * 2
def baseEnd_2250230 : Nat := 1155449573166836198476387

theorem tailTrace_2250230 : CollatzResearch.WordTrace tailWord_2250230 prefixEnd_2250230 1155449573166836198476387 := by
  unfold tailWord_2250230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129539414863030845795759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54715087091872329021821429 5129539414863030845795759)
  ·
    refine ⟨7694309122294546268693639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5129539414863030845795759 7694309122294546268693639)
    ·
      refine ⟨11541463683441819403040459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7694309122294546268693639 11541463683441819403040459)
      ·
        refine ⟨17312195525162729104560689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11541463683441819403040459 17312195525162729104560689)
        ·
          refine ⟨12984146643872046828420517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17312195525162729104560689 12984146643872046828420517)
          ·
            refine ⟨2434527495726008780328847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12984146643872046828420517 2434527495726008780328847)
            ·
              refine ⟨3651791243589013170493271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434527495726008780328847 3651791243589013170493271)
              ·
                refine ⟨5477686865383519755739907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651791243589013170493271 5477686865383519755739907)
                ·
                  refine ⟨8216530298075279633609861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5477686865383519755739907 8216530298075279633609861)
                  ·
                    refine ⟨1540599430889114931301849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8216530298075279633609861 1540599430889114931301849)
                    ·
                      refine ⟨1155449573166836198476387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540599430889114931301849 1155449573166836198476387)
                      ·
                        rfl

theorem cell23_2250230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_2250230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250230 prefixEnd_2250230 := by exact prefixLift 2250230
  have htrace : WordTrace (prefixWord ++ tailWord_2250230) baseStart_2250230 baseEnd_2250230 := by
    simpa [prefixWord, tailWord_2250230, baseEnd_2250230] using wordTrace_append hprefix tailTrace_2250230
  have hstable : (prefixWord ++ tailWord_2250230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250230).length < 2 ^ (prefixWord ++ tailWord_2250230).sum := by decide
  have hdescent : baseEnd_2250230 < baseStart_2250230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250249 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 2, 5]
def baseStart_2250249 : Nat := 118140960795 + 2250249 * 2 ^ 59
def prefixEnd_2250249 : Nat := 4983230072969 + 3 ^ 40 * 2250249 * 2
def baseEnd_2250249 : Nat := 385153109766423874712933

theorem tailTrace_2250249 : CollatzResearch.WordTrace tailWord_2250249 prefixEnd_2250249 385153109766423874712933 := by
  unfold tailWord_2250249
  simp only [CollatzResearch.WordTrace]
  refine ⟨82073323624739659777673801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54715549083159773185115867 82073323624739659777673801)
  ·
    refine ⟨61554992718554744833255351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82073323624739659777673801 61554992718554744833255351)
    ·
      refine ⟨92332489077832117249883027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61554992718554744833255351 92332489077832117249883027)
      ·
        refine ⟨138498733616748175874824541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92332489077832117249883027 138498733616748175874824541)
        ·
          refine ⟨51937025106280565953059203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138498733616748175874824541 51937025106280565953059203)
          ·
            refine ⟨77905537659420848929588805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51937025106280565953059203 77905537659420848929588805)
            ·
              refine ⟨14607288311141409174297901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77905537659420848929588805 14607288311141409174297901)
              ·
                refine ⟨5477733116678028440361713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14607288311141409174297901 5477733116678028440361713)
                ·
                  refine ⟨4108299837508521330271285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5477733116678028440361713 4108299837508521330271285)
                  ·
                    refine ⟨385153109766423874712933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4108299837508521330271285 385153109766423874712933)
                    ·
                      rfl

theorem cell23_2250249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_2250249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250249 prefixEnd_2250249 := by exact prefixLift 2250249
  have htrace : WordTrace (prefixWord ++ tailWord_2250249) baseStart_2250249 baseEnd_2250249 := by
    simpa [prefixWord, tailWord_2250249, baseEnd_2250249] using wordTrace_append hprefix tailTrace_2250249
  have hstable : (prefixWord ++ tailWord_2250249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250249).length < 2 ^ (prefixWord ++ tailWord_2250249).sum := by decide
  have hdescent : baseEnd_2250249 < baseStart_2250249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250416 : List Nat := [2, 1, 1, 1, 2, 1, 8, 7]
def baseStart_2250416 : Nat := 118140960795 + 2250416 * 2 ^ 59
def prefixEnd_2250416 : Nat := 4983230072969 + 3 ^ 40 * 2250416 * 2
def baseEnd_2250416 : Nat := 42797965946984165583353

theorem tailTrace_2250416 : CollatzResearch.WordTrace tailWord_2250416 prefixEnd_2250416 42797965946984165583353 := by
  unfold tailWord_2250416
  simp only [CollatzResearch.WordTrace]
  refine ⟨41039707307567323649501551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54719609743423098199335401 41039707307567323649501551)
  ·
    refine ⟨61559560961350985474252327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41039707307567323649501551 61559560961350985474252327)
    ·
      refine ⟨92339341442026478211378491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61559560961350985474252327 92339341442026478211378491)
      ·
        refine ⟨138509012163039717317067737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92339341442026478211378491 138509012163039717317067737)
        ·
          refine ⟨103881759122279787987800803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138509012163039717317067737 103881759122279787987800803)
          ·
            refine ⟨155822638683419681981701205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103881759122279787987800803 155822638683419681981701205)
            ·
              refine ⟨1826046547071324398223061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 155822638683419681981701205 1826046547071324398223061)
              ·
                refine ⟨42797965946984165583353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1826046547071324398223061 42797965946984165583353)
                ·
                  rfl

theorem cell23_2250416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 7].length) (baseStart_2250416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250416 prefixEnd_2250416 := by exact prefixLift 2250416
  have htrace : WordTrace (prefixWord ++ tailWord_2250416) baseStart_2250416 baseEnd_2250416 := by
    simpa [prefixWord, tailWord_2250416, baseEnd_2250416] using wordTrace_append hprefix tailTrace_2250416
  have hstable : (prefixWord ++ tailWord_2250416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250416).length < 2 ^ (prefixWord ++ tailWord_2250416).sum := by decide
  have hdescent : baseEnd_2250416 < baseStart_2250416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250421 : List Nat := [1, 3, 3, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_2250421 : Nat := 118140960795 + 2250421 * 2 ^ 59
def prefixEnd_2250421 : Nat := 4983230072969 + 3 ^ 40 * 2250421 * 2
def baseEnd_2250421 : Nat := 1155547647971844951188009

theorem tailTrace_2250421 : CollatzResearch.WordTrace tailWord_2250421 prefixEnd_2250421 1155547647971844951188009 := by
  unfold tailWord_2250421
  simp only [CollatzResearch.WordTrace]
  refine ⟨82079596980116533152935117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54719731320077688768623411 82079596980116533152935117)
  ·
    refine ⟨30779848867543699932350669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82079596980116533152935117 30779848867543699932350669)
    ·
      refine ⟨11542443325328887474631501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30779848867543699932350669 11542443325328887474631501)
      ·
        refine ⟨4328416246998332802986813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11542443325328887474631501 4328416246998332802986813)
        ·
          refine ⟨1623156092624374801120055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4328416246998332802986813 1623156092624374801120055)
          ·
            refine ⟨2434734138936562201680083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623156092624374801120055 2434734138936562201680083)
            ·
              refine ⟨3652101208404843302520125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434734138936562201680083 3652101208404843302520125)
              ·
                refine ⟨1369537953151816238445047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3652101208404843302520125 1369537953151816238445047)
                ·
                  refine ⟨2054306929727724357667571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369537953151816238445047 2054306929727724357667571)
                  ·
                    refine ⟨3081460394591586536501357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054306929727724357667571 3081460394591586536501357)
                    ·
                      refine ⟨1155547647971844951188009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081460394591586536501357 1155547647971844951188009)
                      ·
                        rfl

theorem cell23_2250421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_2250421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250421 prefixEnd_2250421 := by exact prefixLift 2250421
  have htrace : WordTrace (prefixWord ++ tailWord_2250421) baseStart_2250421 baseEnd_2250421 := by
    simpa [prefixWord, tailWord_2250421, baseEnd_2250421] using wordTrace_append hprefix tailTrace_2250421
  have hstable : (prefixWord ++ tailWord_2250421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250421).length < 2 ^ (prefixWord ++ tailWord_2250421).sum := by decide
  have hdescent : baseEnd_2250421 < baseStart_2250421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250430 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_2250430 : Nat := 118140960795 + 2250430 * 2 ^ 59
def prefixEnd_2250430 : Nat := 4983230072969 + 3 ^ 40 * 2250430 * 2
def baseEnd_2250430 : Nat := 1155552269297735415975467

theorem tailTrace_2250430 : CollatzResearch.WordTrace tailWord_2250430 prefixEnd_2250430 1155552269297735415975467 := by
  unfold tailWord_2250430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10259990654635490961251593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54719950158055951793341829 10259990654635490961251593)
  ·
    refine ⟨7694992990976618220938695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10259990654635490961251593 7694992990976618220938695)
    ·
      refine ⟨11542489486464927331408043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7694992990976618220938695 11542489486464927331408043)
      ·
        refine ⟨17313734229697390997112065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11542489486464927331408043 17313734229697390997112065)
        ·
          refine ⟨12985300672273043247834049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17313734229697390997112065 12985300672273043247834049)
          ·
            refine ⟨9738975504204782435875537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12985300672273043247834049 9738975504204782435875537)
            ·
              refine ⟨7304231628153586826906653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9738975504204782435875537 7304231628153586826906653)
              ·
                refine ⟨2739086860557595060089995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7304231628153586826906653 2739086860557595060089995)
                ·
                  refine ⟨4108630290836392590134993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739086860557595060089995 4108630290836392590134993)
                  ·
                    refine ⟨3081472718127294442601245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4108630290836392590134993 3081472718127294442601245)
                    ·
                      refine ⟨1155552269297735415975467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081472718127294442601245 1155552269297735415975467)
                      ·
                        rfl

theorem cell23_2250430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_2250430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250430 prefixEnd_2250430 := by exact prefixLift 2250430
  have htrace : WordTrace (prefixWord ++ tailWord_2250430) baseStart_2250430 baseEnd_2250430 := by
    simpa [prefixWord, tailWord_2250430, baseEnd_2250430] using wordTrace_append hprefix tailTrace_2250430
  have hstable : (prefixWord ++ tailWord_2250430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250430).length < 2 ^ (prefixWord ++ tailWord_2250430).sum := by decide
  have hdescent : baseEnd_2250430 < baseStart_2250430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250438 : List Nat := [6, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2250438 : Nat := 118140960795 + 2250438 * 2 ^ 59
def prefixEnd_2250438 : Nat := 4983230072969 + 3 ^ 40 * 2250438 * 2
def baseEnd_2250438 : Nat := 1155556377142971384675431

theorem tailTrace_2250438 : CollatzResearch.WordTrace tailWord_2250438 prefixEnd_2250438 1155556377142971384675431 := by
  unfold tailWord_2250438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2565006781907967033009499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54720144680703296704202645 2565006781907967033009499)
  ·
    refine ⟨3847510172861950549514249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2565006781907967033009499 3847510172861950549514249)
    ·
      refine ⟨2885632629646462912135687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3847510172861950549514249 2885632629646462912135687)
      ·
        refine ⟨4328448944469694368203531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2885632629646462912135687 4328448944469694368203531)
        ·
          refine ⟨6492673416704541552305297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328448944469694368203531 6492673416704541552305297)
          ·
            refine ⟨4869505062528406164228973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6492673416704541552305297 4869505062528406164228973)
            ·
              refine ⟨1826064398448152311585865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4869505062528406164228973 1826064398448152311585865)
              ·
                refine ⟨1369548298836114233689399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826064398448152311585865 1369548298836114233689399)
                ·
                  refine ⟨2054322448254171350534099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369548298836114233689399 2054322448254171350534099)
                  ·
                    refine ⟨3081483672381257025801149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054322448254171350534099 3081483672381257025801149)
                    ·
                      refine ⟨1155556377142971384675431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081483672381257025801149 1155556377142971384675431)
                      ·
                        rfl

theorem cell23_2250438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2250438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250438 prefixEnd_2250438 := by exact prefixLift 2250438
  have htrace : WordTrace (prefixWord ++ tailWord_2250438) baseStart_2250438 baseEnd_2250438 := by
    simpa [prefixWord, tailWord_2250438, baseEnd_2250438] using wordTrace_append hprefix tailTrace_2250438
  have hstable : (prefixWord ++ tailWord_2250438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250438).length < 2 ^ (prefixWord ++ tailWord_2250438).sum := by decide
  have hdescent : baseEnd_2250438 < baseStart_2250438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250444 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2250444 : Nat := 118140960795 + 2250444 * 2 ^ 59
def prefixEnd_2250444 : Nat := 4983230072969 + 3 ^ 40 * 2250444 * 2
def baseEnd_2250444 : Nat := 1155559458026898361200403

theorem tailTrace_2250444 : CollatzResearch.WordTrace tailWord_2250444 prefixEnd_2250444 1155559458026898361200403 := by
  unfold tailWord_2250444
  simp only [CollatzResearch.WordTrace]
  refine ⟨41040217929516604040511193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54720290572688805387348257 41040217929516604040511193)
  ·
    refine ⟨30780163447137453030383395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41040217929516604040511193 30780163447137453030383395)
    ·
      refine ⟨46170245170706179545575093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30780163447137453030383395 46170245170706179545575093)
      ·
        refine ⟨4328460484753704332397665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46170245170706179545575093 4328460484753704332397665)
        ·
          refine ⟨3246345363565278249298249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4328460484753704332397665 3246345363565278249298249)
          ·
            refine ⟨2434759022673958686973687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3246345363565278249298249 2434759022673958686973687)
            ·
              refine ⟨3652138534010938030460531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434759022673958686973687 3652138534010938030460531)
              ·
                refine ⟨5478207801016407045690797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3652138534010938030460531 5478207801016407045690797)
                ·
                  refine ⟨2054327925381152642134049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5478207801016407045690797 2054327925381152642134049)
                  ·
                    refine ⟨1540745944035864481600537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2054327925381152642134049 1540745944035864481600537)
                    ·
                      refine ⟨1155559458026898361200403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540745944035864481600537 1155559458026898361200403)
                      ·
                        rfl

theorem cell23_2250444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2250444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250444 prefixEnd_2250444 := by exact prefixLift 2250444
  have htrace : WordTrace (prefixWord ++ tailWord_2250444) baseStart_2250444 baseEnd_2250444 := by
    simpa [prefixWord, tailWord_2250444, baseEnd_2250444] using wordTrace_append hprefix tailTrace_2250444
  have hstable : (prefixWord ++ tailWord_2250444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250444).length < 2 ^ (prefixWord ++ tailWord_2250444).sum := by decide
  have hdescent : baseEnd_2250444 < baseStart_2250444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250446 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2250446 : Nat := 118140960795 + 2250446 * 2 ^ 59
def prefixEnd_2250446 : Nat := 4983230072969 + 3 ^ 40 * 2250446 * 2
def baseEnd_2250446 : Nat := 385186828329402451125131

theorem tailTrace_2250446 : CollatzResearch.WordTrace tailWord_2250446 prefixEnd_2250446 385186828329402451125131 := by
  unfold tailWord_2250446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10260063600628245302824399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54720339203350641615063461 10260063600628245302824399)
  ·
    refine ⟨15390095400942367954236599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10260063600628245302824399 15390095400942367954236599)
    ·
      refine ⟨23085143101413551931354899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15390095400942367954236599 23085143101413551931354899)
      ·
        refine ⟨34627714652120327897032349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23085143101413551931354899 34627714652120327897032349)
        ·
          refine ⟨12985392994545122961387131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34627714652120327897032349 12985392994545122961387131)
          ·
            refine ⟨19478089491817684442080697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12985392994545122961387131 19478089491817684442080697)
            ·
              refine ⟨14608567118863263331560523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19478089491817684442080697 14608567118863263331560523)
              ·
                refine ⟨21912850678294894997340785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14608567118863263331560523 21912850678294894997340785)
                ·
                  refine ⟨16434638008721171248005589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21912850678294894997340785 16434638008721171248005589)
                  ·
                    refine ⟨385186828329402451125131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16434638008721171248005589 385186828329402451125131)
                    ·
                      rfl

theorem cell23_2250446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2250446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250446 prefixEnd_2250446 := by exact prefixLift 2250446
  have htrace : WordTrace (prefixWord ++ tailWord_2250446) baseStart_2250446 baseEnd_2250446 := by
    simpa [prefixWord, tailWord_2250446, baseEnd_2250446] using wordTrace_append hprefix tailTrace_2250446
  have hstable : (prefixWord ++ tailWord_2250446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250446).length < 2 ^ (prefixWord ++ tailWord_2250446).sum := by decide
  have hdescent : baseEnd_2250446 < baseStart_2250446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250454 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2250454 : Nat := 118140960795 + 2250454 * 2 ^ 59
def prefixEnd_2250454 : Nat := 4983230072969 + 3 ^ 40 * 2250454 * 2
def baseEnd_2250454 : Nat := 385188197611147774025119

theorem tailTrace_2250454 : CollatzResearch.WordTrace tailWord_2250454 prefixEnd_2250454 385188197611147774025119 := by
  unfold tailWord_2250454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5130050036812311236805401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54720533725997986525924277 5130050036812311236805401)
  ·
    refine ⟨3847537527609233427604051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5130050036812311236805401 3847537527609233427604051)
    ·
      refine ⟨5771306291413850141406077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3847537527609233427604051 5771306291413850141406077)
      ·
        refine ⟨2164239859280193803027279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5771306291413850141406077 2164239859280193803027279)
        ·
          refine ⟨3246359788920290704540919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164239859280193803027279 3246359788920290704540919)
          ·
            refine ⟨4869539683380436056811379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246359788920290704540919 4869539683380436056811379)
            ·
              refine ⟨7304309525070654085217069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4869539683380436056811379 7304309525070654085217069)
              ·
                refine ⟨2739116071901495281956401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7304309525070654085217069 2739116071901495281956401)
                ·
                  refine ⟨2054337053926121461467301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739116071901495281956401 2054337053926121461467301)
                  ·
                    refine ⟨385188197611147774025119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054337053926121461467301 385188197611147774025119)
                    ·
                      rfl

theorem cell23_2250454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2250454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250454 prefixEnd_2250454 := by exact prefixLift 2250454
  have htrace : WordTrace (prefixWord ++ tailWord_2250454) baseStart_2250454 baseEnd_2250454 := by
    simpa [prefixWord, tailWord_2250454, baseEnd_2250454] using wordTrace_append hprefix tailTrace_2250454
  have hstable : (prefixWord ++ tailWord_2250454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250454).length < 2 ^ (prefixWord ++ tailWord_2250454).sum := by decide
  have hdescent : baseEnd_2250454 < baseStart_2250454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250483 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 3, 4, 2]
def baseStart_2250483 : Nat := 118140960795 + 2250483 * 2 ^ 59
def prefixEnd_2250483 : Nat := 4983230072969 + 3 ^ 40 * 2250483 * 2
def baseEnd_2250483 : Nat := 1155579483772423708612723

theorem tailTrace_2250483 : CollatzResearch.WordTrace tailWord_2250483 prefixEnd_2250483 1155579483772423708612723 := by
  unfold tailWord_2250483
  simp only [CollatzResearch.WordTrace]
  refine ⟨82081858305891917741692103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54721238870594611827794735 82081858305891917741692103)
  ·
    refine ⟨123122787458837876612538155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82081858305891917741692103 123122787458837876612538155)
    ·
      refine ⟨184684181188256814918807233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123122787458837876612538155 184684181188256814918807233)
      ·
        refine ⟨138513135891192611189105425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184684181188256814918807233 138513135891192611189105425)
        ·
          refine ⟨103884851918394458391829069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138513135891192611189105425 103884851918394458391829069)
          ·
            refine ⟨38956819469397921896935901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103884851918394458391829069 38956819469397921896935901)
            ·
              refine ⟨14608807301024220711350963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38956819469397921896935901 14608807301024220711350963)
              ·
                refine ⟨21913210951536331067026445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14608807301024220711350963 21913210951536331067026445)
                ·
                  refine ⟨8217454106826124150134917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21913210951536331067026445 8217454106826124150134917)
                  ·
                    refine ⟨1540772645029898278150297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8217454106826124150134917 1540772645029898278150297)
                    ·
                      refine ⟨1155579483772423708612723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540772645029898278150297 1155579483772423708612723)
                      ·
                        rfl

theorem cell23_2250483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4, 2].length) (baseStart_2250483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250483 prefixEnd_2250483 := by exact prefixLift 2250483
  have htrace : WordTrace (prefixWord ++ tailWord_2250483) baseStart_2250483 baseEnd_2250483 := by
    simpa [prefixWord, tailWord_2250483, baseEnd_2250483] using wordTrace_append hprefix tailTrace_2250483
  have hstable : (prefixWord ++ tailWord_2250483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250483).length < 2 ^ (prefixWord ++ tailWord_2250483).sum := by decide
  have hdescent : baseEnd_2250483 < baseStart_2250483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250494 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_2250494 : Nat := 118140960795 + 2250494 * 2 ^ 59
def prefixEnd_2250494 : Nat := 4983230072969 + 3 ^ 40 * 2250494 * 2
def baseEnd_2250494 : Nat := 1155585132059623165575173

theorem tailTrace_2250494 : CollatzResearch.WordTrace tailWord_2250494 prefixEnd_2250494 1155585132059623165575173 := by
  unfold tailWord_2250494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10260282438606508327542817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54721506339234711080228357 10260282438606508327542817)
  ·
    refine ⟨7695211828954881245657113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10260282438606508327542817 7695211828954881245657113)
    ·
      refine ⟨5771408871716160934242835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7695211828954881245657113 5771408871716160934242835)
      ·
        refine ⟨8657113307574241401364253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771408871716160934242835 8657113307574241401364253)
        ·
          refine ⟨3246417490340340525511595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8657113307574241401364253 3246417490340340525511595)
          ·
            refine ⟨4869626235510510788267393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246417490340340525511595 4869626235510510788267393)
            ·
              refine ⟨3652219676632883091200545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869626235510510788267393 3652219676632883091200545)
              ·
                refine ⟨2739164757474662318400409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652219676632883091200545 2739164757474662318400409)
                ·
                  refine ⟨2054373568105996738800307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739164757474662318400409 2054373568105996738800307)
                  ·
                    refine ⟨3081560352158995108200461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054373568105996738800307 3081560352158995108200461)
                    ·
                      refine ⟨1155585132059623165575173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081560352158995108200461 1155585132059623165575173)
                      ·
                        rfl

theorem cell23_2250494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_2250494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250494 prefixEnd_2250494 := by exact prefixLift 2250494
  have htrace : WordTrace (prefixWord ++ tailWord_2250494) baseStart_2250494 baseEnd_2250494 := by
    simpa [prefixWord, tailWord_2250494, baseEnd_2250494] using wordTrace_append hprefix tailTrace_2250494
  have hstable : (prefixWord ++ tailWord_2250494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250494).length < 2 ^ (prefixWord ++ tailWord_2250494).sum := by decide
  have hdescent : baseEnd_2250494 < baseStart_2250494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250496 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_2250496 : Nat := 118140960795 + 2250496 * 2 ^ 59
def prefixEnd_2250496 : Nat := 4983230072969 + 3 ^ 40 * 2250496 * 2
def baseEnd_2250496 : Nat := 1155586159020932157750163

theorem tailTrace_2250496 : CollatzResearch.WordTrace tailWord_2250496 prefixEnd_2250496 1155586159020932157750163 := by
  unfold tailWord_2250496
  simp only [CollatzResearch.WordTrace]
  refine ⟨41041166227422410480957671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54721554969896547307943561 41041166227422410480957671)
  ·
    refine ⟨61561749341133615721436507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41041166227422410480957671 61561749341133615721436507)
    ·
      refine ⟨92342624011700423582154761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61561749341133615721436507 92342624011700423582154761)
      ·
        refine ⟨69256968008775317686616071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92342624011700423582154761 69256968008775317686616071)
        ·
          refine ⟨103885452013162976529924107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69256968008775317686616071 103885452013162976529924107)
          ·
            refine ⟨155828178019744464794886161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103885452013162976529924107 155828178019744464794886161)
            ·
              refine ⟨116871133514808348596164621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155828178019744464794886161 116871133514808348596164621)
              ·
                refine ⟨43826675068053130723561733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116871133514808348596164621 43826675068053130723561733)
                ·
                  refine ⟨8217501575259962010667825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43826675068053130723561733 8217501575259962010667825)
                  ·
                    refine ⟨6163126181444971508000869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8217501575259962010667825 6163126181444971508000869)
                    ·
                      refine ⟨1155586159020932157750163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6163126181444971508000869 1155586159020932157750163)
                      ·
                        rfl

theorem cell23_2250496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_2250496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250496 prefixEnd_2250496 := by exact prefixLift 2250496
  have htrace : WordTrace (prefixWord ++ tailWord_2250496) baseStart_2250496 baseEnd_2250496 := by
    simpa [prefixWord, tailWord_2250496, baseEnd_2250496] using wordTrace_append hprefix tailTrace_2250496
  have hstable : (prefixWord ++ tailWord_2250496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250496).length < 2 ^ (prefixWord ++ tailWord_2250496).sum := by decide
  have hdescent : baseEnd_2250496 < baseStart_2250496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250517 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_2250517 : Nat := 118140960795 + 2250517 * 2 ^ 59
def prefixEnd_2250517 : Nat := 4983230072969 + 3 ^ 40 * 2250517 * 2
def baseEnd_2250517 : Nat := 1155596942114676575587567

theorem tailTrace_2250517 : CollatzResearch.WordTrace tailWord_2250517 prefixEnd_2250517 1155596942114676575587567 := by
  unfold tailWord_2250517
  simp only [CollatzResearch.WordTrace]
  refine ⟨82083098387768741548429805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54722065591845827698953203 82083098387768741548429805)
  ·
    refine ⟨30781161895413278080661177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82083098387768741548429805 30781161895413278080661177)
    ·
      refine ⟨23085871421559958560495883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30781161895413278080661177 23085871421559958560495883)
      ·
        refine ⟨34628807132339937840743825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23085871421559958560495883 34628807132339937840743825)
        ·
          refine ⟨25971605349254953380557869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34628807132339937840743825 25971605349254953380557869)
          ·
            refine ⟨9739352005970607517709201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25971605349254953380557869 9739352005970607517709201)
            ·
              refine ⟨7304514004477955638281901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9739352005970607517709201 7304514004477955638281901)
              ·
                refine ⟨2739192751679233364355713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7304514004477955638281901 2739192751679233364355713)
                ·
                  refine ⟨2054394563759425023266785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739192751679233364355713 2054394563759425023266785)
                  ·
                    refine ⟨1540795922819568767450089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2054394563759425023266785 1540795922819568767450089)
                    ·
                      refine ⟨1155596942114676575587567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540795922819568767450089 1155596942114676575587567)
                      ·
                        rfl

theorem cell23_2250517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_2250517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250517 prefixEnd_2250517 := by exact prefixLift 2250517
  have htrace : WordTrace (prefixWord ++ tailWord_2250517) baseStart_2250517 baseEnd_2250517 := by
    simpa [prefixWord, tailWord_2250517, baseEnd_2250517] using wordTrace_append hprefix tailTrace_2250517
  have hstable : (prefixWord ++ tailWord_2250517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250517).length < 2 ^ (prefixWord ++ tailWord_2250517).sum := by decide
  have hdescent : baseEnd_2250517 < baseStart_2250517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250540 : List Nat := [2, 2, 1, 1, 1, 6, 2, 3, 5]
def baseStart_2250540 : Nat := 118140960795 + 2250540 * 2 ^ 59
def prefixEnd_2250540 : Nat := 4983230072969 + 3 ^ 40 * 2250540 * 2
def baseEnd_2250540 : Nat := 128400972463303331733329

theorem tailTrace_2250540 : CollatzResearch.WordTrace tailWord_2250540 prefixEnd_2250540 128400972463303331733329 := by
  unfold tailWord_2250540
  simp only [CollatzResearch.WordTrace]
  refine ⟨41041968633342708238258537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54722624844456944317678049 41041968633342708238258537)
  ·
    refine ⟨30781476475007031178693903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41041968633342708238258537 30781476475007031178693903)
    ·
      refine ⟨46172214712510546768040855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30781476475007031178693903 46172214712510546768040855)
      ·
        refine ⟨69258322068765820152061283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46172214712510546768040855 69258322068765820152061283)
        ·
          refine ⟨103887483103148730228091925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69258322068765820152061283 103887483103148730228091925)
          ·
            refine ⟨4869725770460096729441809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103887483103148730228091925 4869725770460096729441809)
            ·
              refine ⟨3652294327845072547081357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869725770460096729441809 3652294327845072547081357)
              ·
                refine ⟨1369610372941902205155509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3652294327845072547081357 1369610372941902205155509)
                ·
                  refine ⟨128400972463303331733329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1369610372941902205155509 128400972463303331733329)
                  ·
                    rfl

theorem cell23_2250540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_2250540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250540 prefixEnd_2250540 := by exact prefixLift 2250540
  have htrace : WordTrace (prefixWord ++ tailWord_2250540) baseStart_2250540 baseEnd_2250540 := by
    simpa [prefixWord, tailWord_2250540, baseEnd_2250540] using wordTrace_append hprefix tailTrace_2250540
  have hstable : (prefixWord ++ tailWord_2250540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250540).length < 2 ^ (prefixWord ++ tailWord_2250540).sum := by decide
  have hdescent : baseEnd_2250540 < baseStart_2250540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250543 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 4, 5, 2]
def baseStart_2250543 : Nat := 118140960795 + 2250543 * 2 ^ 59
def prefixEnd_2250543 : Nat := 4983230072969 + 3 ^ 40 * 2250543 * 2
def baseEnd_2250543 : Nat := 1155610292611693473862447

theorem tailTrace_2250543 : CollatzResearch.WordTrace tailWord_2250543 prefixEnd_2250543 1155610292611693473862447 := by
  unfold tailWord_2250543
  simp only [CollatzResearch.WordTrace]
  refine ⟨82084046685674547988876283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54722697790449698659250855 82084046685674547988876283)
  ·
    refine ⟨123126070028511821983314425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82084046685674547988876283 123126070028511821983314425)
    ·
      refine ⟨92344552521383866487485819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123126070028511821983314425 92344552521383866487485819)
      ·
        refine ⟨138516828782075799731228729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92344552521383866487485819 138516828782075799731228729)
        ·
          refine ⟨103887621586556849798421547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138516828782075799731228729 103887621586556849798421547)
          ·
            refine ⟨155831432379835274697632321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103887621586556849798421547 155831432379835274697632321)
            ·
              refine ⟨116873574284876456023224241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155831432379835274697632321 116873574284876456023224241)
              ·
                refine ⟨87655180713657342017418181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116873574284876456023224241 87655180713657342017418181)
                ·
                  refine ⟨16435346383810751628265909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87655180713657342017418181 16435346383810751628265909)
                  ·
                    refine ⟨1540813723482257965149929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16435346383810751628265909 1540813723482257965149929)
                    ·
                      refine ⟨1155610292611693473862447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540813723482257965149929 1155610292611693473862447)
                      ·
                        rfl

theorem cell23_2250543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5, 2].length) (baseStart_2250543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250543 prefixEnd_2250543 := by exact prefixLift 2250543
  have htrace : WordTrace (prefixWord ++ tailWord_2250543) baseStart_2250543 baseEnd_2250543 := by
    simpa [prefixWord, tailWord_2250543, baseEnd_2250543] using wordTrace_append hprefix tailTrace_2250543
  have hstable : (prefixWord ++ tailWord_2250543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250543).length < 2 ^ (prefixWord ++ tailWord_2250543).sum := by decide
  have hdescent : baseEnd_2250543 < baseStart_2250543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250593 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_2250593 : Nat := 118140960795 + 2250593 * 2 ^ 59
def prefixEnd_2250593 : Nat := 4983230072969 + 3 ^ 40 * 2250593 * 2
def baseEnd_2250593 : Nat := 1155635966644418278237217

theorem tailTrace_2250593 : CollatzResearch.WordTrace tailWord_2250593 prefixEnd_2250593 1155635966644418278237217 := by
  unfold tailWord_2250593
  simp only [CollatzResearch.WordTrace]
  refine ⟨82085870335493406528196433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54723913556995604352130955 82085870335493406528196433)
  ·
    refine ⟨61564402751620054896147325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82085870335493406528196433 61564402751620054896147325)
    ·
      refine ⟨23086651031857520586055247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61564402751620054896147325 23086651031857520586055247)
      ·
        refine ⟨34629976547786280879082871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23086651031857520586055247 34629976547786280879082871)
        ·
          refine ⟨51944964821679421318624307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34629976547786280879082871 51944964821679421318624307)
          ·
            refine ⟨77917447232519131977936461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51944964821679421318624307 77917447232519131977936461)
            ·
              refine ⟨29219042712194674491726173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77917447232519131977936461 29219042712194674491726173)
              ·
                refine ⟨10957141017073002934397315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29219042712194674491726173 10957141017073002934397315)
                ·
                  refine ⟨16435711525609504401595973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10957141017073002934397315 16435711525609504401595973)
                  ·
                    refine ⟨3081695911051782075299245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16435711525609504401595973 3081695911051782075299245)
                    ·
                      refine ⟨1155635966644418278237217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081695911051782075299245 1155635966644418278237217)
                      ·
                        rfl

theorem cell23_2250593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_2250593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250593 prefixEnd_2250593 := by exact prefixLift 2250593
  have htrace : WordTrace (prefixWord ++ tailWord_2250593) baseStart_2250593 baseEnd_2250593 := by
    simpa [prefixWord, tailWord_2250593, baseEnd_2250593] using wordTrace_append hprefix tailTrace_2250593
  have hstable : (prefixWord ++ tailWord_2250593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250593).length < 2 ^ (prefixWord ++ tailWord_2250593).sum := by decide
  have hdescent : baseEnd_2250593 < baseStart_2250593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250613 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 8]
def baseStart_2250613 : Nat := 118140960795 + 2250613 * 2 ^ 59
def prefixEnd_2250613 : Nat := 4983230072969 + 3 ^ 40 * 2250613 * 2
def baseEnd_2250613 : Nat := 128405137361945355554125

theorem tailTrace_2250613 : CollatzResearch.WordTrace tailWord_2250613 prefixEnd_2250613 128405137361945355554125 := by
  unfold tailWord_2250613
  simp only [CollatzResearch.WordTrace]
  refine ⟨82086599795420949943924493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54724399863613966629282995 82086599795420949943924493)
  ·
    refine ⟨30782474923282856228971685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82086599795420949943924493 30782474923282856228971685)
    ·
      refine ⟨5771714048115535542932191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30782474923282856228971685 5771714048115535542932191)
      ·
        refine ⟨8657571072173303314398287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771714048115535542932191 8657571072173303314398287)
        ·
          refine ⟨12986356608259954971597431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8657571072173303314398287 12986356608259954971597431)
          ·
            refine ⟨19479534912389932457396147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12986356608259954971597431 19479534912389932457396147)
            ·
              refine ⟨29219302368584898686094221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19479534912389932457396147 29219302368584898686094221)
              ·
                refine ⟨10957238388219337007285333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29219302368584898686094221 10957238388219337007285333)
                ·
                  refine ⟨128405137361945355554125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10957238388219337007285333 128405137361945355554125)
                  ·
                    rfl

theorem cell23_2250613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_2250613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250613 prefixEnd_2250613 := by exact prefixLift 2250613
  have htrace : WordTrace (prefixWord ++ tailWord_2250613) baseStart_2250613 baseEnd_2250613 := by
    simpa [prefixWord, tailWord_2250613, baseEnd_2250613] using wordTrace_append hprefix tailTrace_2250613
  have hstable : (prefixWord ++ tailWord_2250613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250613).length < 2 ^ (prefixWord ++ tailWord_2250613).sum := by decide
  have hdescent : baseEnd_2250613 < baseStart_2250613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250664 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 6]
def baseStart_2250664 : Nat := 118140960795 + 2250664 * 2 ^ 59
def prefixEnd_2250664 : Nat := 4983230072969 + 3 ^ 40 * 2250664 * 2
def baseEnd_2250664 : Nat := 128408047085654166716599

theorem tailTrace_2250664 : CollatzResearch.WordTrace tailWord_2250664 prefixEnd_2250664 128408047085654166716599 := by
  unfold tailWord_2250664
  simp only [CollatzResearch.WordTrace]
  refine ⟨41044229959118092827015523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54725639945490790436020697 41044229959118092827015523)
  ·
    refine ⟨61566344938677139240523285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41044229959118092827015523 61566344938677139240523285)
    ·
      refine ⟨2885922419000490901899529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61566344938677139240523285 2885922419000490901899529)
      ·
        refine ⟨2164441814250368176424647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2885922419000490901899529 2164441814250368176424647)
        ·
          refine ⟨3246662721375552264636971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164441814250368176424647 3246662721375552264636971)
          ·
            refine ⟨4869994082063328396955457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246662721375552264636971 4869994082063328396955457)
            ·
              refine ⟨3652495561547496297716593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869994082063328396955457 3652495561547496297716593)
              ·
                refine ⟨2739371671160622223287445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652495561547496297716593 2739371671160622223287445)
                ·
                  refine ⟨128408047085654166716599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2739371671160622223287445 128408047085654166716599)
                  ·
                    rfl

theorem cell23_2250664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 6].length) (baseStart_2250664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250664 prefixEnd_2250664 := by exact prefixLift 2250664
  have htrace : WordTrace (prefixWord ++ tailWord_2250664) baseStart_2250664 baseEnd_2250664 := by
    simpa [prefixWord, tailWord_2250664, baseEnd_2250664] using wordTrace_append hprefix tailTrace_2250664
  have hstable : (prefixWord ++ tailWord_2250664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250664).length < 2 ^ (prefixWord ++ tailWord_2250664).sum := by decide
  have hdescent : baseEnd_2250664 < baseStart_2250664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250683 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 3]
def baseStart_2250683 : Nat := 118140960795 + 2250683 * 2 ^ 59
def prefixEnd_2250683 : Nat := 4983230072969 + 3 ^ 40 * 2250683 * 2
def baseEnd_2250683 : Nat := 1155682179903322926111803

theorem tailTrace_2250683 : CollatzResearch.WordTrace tailWord_2250683 prefixEnd_2250683 1155682179903322926111803 := by
  unfold tailWord_2250683
  simp only [CollatzResearch.WordTrace]
  refine ⟨82089152905167351898972703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54726101936778234599315135 82089152905167351898972703)
  ·
    refine ⟨123133729357751027848459055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82089152905167351898972703 123133729357751027848459055)
    ·
      refine ⟨184700594036626541772688583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123133729357751027848459055 184700594036626541772688583)
      ·
        refine ⟨277050891054939812659032875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184700594036626541772688583 277050891054939812659032875)
        ·
          refine ⟨415576336582409718988549313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277050891054939812659032875 415576336582409718988549313)
          ·
            refine ⟨311682252436807289241411985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415576336582409718988549313 311682252436807289241411985)
            ·
              refine ⟨233761689327605466931058989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311682252436807289241411985 233761689327605466931058989)
              ·
                refine ⟨87660633497852050099147121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233761689327605466931058989 87660633497852050099147121)
                ·
                  refine ⟨65745475123389037574360341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87660633497852050099147121 65745475123389037574360341)
                  ·
                    refine ⟨3081819146408861136298141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65745475123389037574360341 3081819146408861136298141)
                    ·
                      refine ⟨1155682179903322926111803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081819146408861136298141 1155682179903322926111803)
                      ·
                        rfl

theorem cell23_2250683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 3].length) (baseStart_2250683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250683 prefixEnd_2250683 := by exact prefixLift 2250683
  have htrace : WordTrace (prefixWord ++ tailWord_2250683) baseStart_2250683 baseEnd_2250683 := by
    simpa [prefixWord, tailWord_2250683, baseEnd_2250683] using wordTrace_append hprefix tailTrace_2250683
  have hstable : (prefixWord ++ tailWord_2250683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250683).length < 2 ^ (prefixWord ++ tailWord_2250683).sum := by decide
  have hdescent : baseEnd_2250683 < baseStart_2250683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250697 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 3, 2, 2]
def baseStart_2250697 : Nat := 118140960795 + 2250697 * 2 ^ 59
def prefixEnd_2250697 : Nat := 4983230072969 + 3 ^ 40 * 2250697 * 2
def baseEnd_2250697 : Nat := 1155689368632485871336739

theorem tailTrace_2250697 : CollatzResearch.WordTrace tailWord_2250697 prefixEnd_2250697 1155689368632485871336739 := by
  unfold tailWord_2250697
  simp only [CollatzResearch.WordTrace]
  refine ⟨82089663527116632289982345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54726442351411088193321563 82089663527116632289982345)
  ·
    refine ⟨61567247645337474217486759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82089663527116632289982345 61567247645337474217486759)
    ·
      refine ⟨92350871468006211326230139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61567247645337474217486759 92350871468006211326230139)
      ·
        refine ⟨138526307202009316989345209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92350871468006211326230139 138526307202009316989345209)
        ·
          refine ⟨103894730401506987742008907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138526307202009316989345209 103894730401506987742008907)
          ·
            refine ⟨155842095602260481613013361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103894730401506987742008907 155842095602260481613013361)
            ·
              refine ⟨116881571701695361209760021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155842095602260481613013361 116881571701695361209760021)
              ·
                refine ⟨5478823673516970056707501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116881571701695361209760021 5478823673516970056707501)
                ·
                  refine ⟨2054558877568863771265313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5478823673516970056707501 2054558877568863771265313)
                  ·
                    refine ⟨1540919158176647828448985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2054558877568863771265313 1540919158176647828448985)
                    ·
                      refine ⟨1155689368632485871336739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540919158176647828448985 1155689368632485871336739)
                      ·
                        rfl

theorem cell23_2250697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 2, 2].length) (baseStart_2250697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250697 prefixEnd_2250697 := by exact prefixLift 2250697
  have htrace : WordTrace (prefixWord ++ tailWord_2250697) baseStart_2250697 baseEnd_2250697 := by
    simpa [prefixWord, tailWord_2250697, baseEnd_2250697] using wordTrace_append hprefix tailTrace_2250697
  have hstable : (prefixWord ++ tailWord_2250697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250697).length < 2 ^ (prefixWord ++ tailWord_2250697).sum := by decide
  have hdescent : baseEnd_2250697 < baseStart_2250697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250743 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_2250743 : Nat := 118140960795 + 2250743 * 2 ^ 59
def prefixEnd_2250743 : Nat := 4983230072969 + 3 ^ 40 * 2250743 * 2
def baseEnd_2250743 : Nat := 1155712988742592691361527

theorem tailTrace_2250743 : CollatzResearch.WordTrace tailWord_2250743 prefixEnd_2250743 1155712988742592691361527 := by
  unfold tailWord_2250743
  simp only [CollatzResearch.WordTrace]
  refine ⟨82091341284949982146156883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54727560856633321430771255 82091341284949982146156883)
  ·
    refine ⟨123137011927424973219235325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82091341284949982146156883 123137011927424973219235325)
    ·
      refine ⟨46176379472784364957213247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123137011927424973219235325 46176379472784364957213247)
      ·
        refine ⟨69264569209176547435819871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46176379472784364957213247 69264569209176547435819871)
        ·
          refine ⟨103896853813764821153729807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69264569209176547435819871 103896853813764821153729807)
          ·
            refine ⟨155845280720647231730594711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103896853813764821153729807 155845280720647231730594711)
            ·
              refine ⟨233767921080970847595892067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155845280720647231730594711 233767921080970847595892067)
              ·
                refine ⟨350651881621456271393838101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233767921080970847595892067 350651881621456271393838101)
                ·
                  refine ⟨16436806951005762721586161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 350651881621456271393838101 16436806951005762721586161)
                  ·
                    refine ⟨12327605213254322041189621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16436806951005762721586161 12327605213254322041189621)
                    ·
                      refine ⟨1155712988742592691361527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12327605213254322041189621 1155712988742592691361527)
                      ·
                        rfl

theorem cell23_2250743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_2250743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250743 prefixEnd_2250743 := by exact prefixLift 2250743
  have htrace : WordTrace (prefixWord ++ tailWord_2250743) baseStart_2250743 baseEnd_2250743 := by
    simpa [prefixWord, tailWord_2250743, baseEnd_2250743] using wordTrace_append hprefix tailTrace_2250743
  have hstable : (prefixWord ++ tailWord_2250743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250743).length < 2 ^ (prefixWord ++ tailWord_2250743).sum := by decide
  have hdescent : baseEnd_2250743 < baseStart_2250743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250747 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 3]
def baseStart_2250747 : Nat := 118140960795 + 2250747 * 2 ^ 59
def prefixEnd_2250747 : Nat := 4983230072969 + 3 ^ 40 * 2250747 * 2
def baseEnd_2250747 : Nat := 1155715042665210675711509

theorem tailTrace_2250747 : CollatzResearch.WordTrace tailWord_2250747 prefixEnd_2250747 1155715042665210675711509 := by
  unfold tailWord_2250747
  simp only [CollatzResearch.WordTrace]
  refine ⟨82091487176935490829302495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54727658117956993886201663 82091487176935490829302495)
  ·
    refine ⟨123137230765403236243953743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82091487176935490829302495 123137230765403236243953743)
    ·
      refine ⟨184705846148104854365930615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123137230765403236243953743 184705846148104854365930615)
      ·
        refine ⟨277058769222157281548895923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184705846148104854365930615 277058769222157281548895923)
        ·
          refine ⟨415588153833235922323343885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277058769222157281548895923 415588153833235922323343885)
          ·
            refine ⟨155845557687463470871253957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 415588153833235922323343885 155845557687463470871253957)
            ·
              refine ⟨29221042066399400788360117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155845557687463470871253957 29221042066399400788360117)
              ·
                refine ⟨2739472693724943823908761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29221042066399400788360117 2739472693724943823908761)
                ·
                  refine ⟨2054604520293707867931571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739472693724943823908761 2054604520293707867931571)
                  ·
                    refine ⟨3081906780440561801897357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054604520293707867931571 3081906780440561801897357)
                    ·
                      refine ⟨1155715042665210675711509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081906780440561801897357 1155715042665210675711509)
                      ·
                        rfl

theorem cell23_2250747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 3].length) (baseStart_2250747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250747 prefixEnd_2250747 := by exact prefixLift 2250747
  have htrace : WordTrace (prefixWord ++ tailWord_2250747) baseStart_2250747 baseEnd_2250747 := by
    simpa [prefixWord, tailWord_2250747, baseEnd_2250747] using wordTrace_append hprefix tailTrace_2250747
  have hstable : (prefixWord ++ tailWord_2250747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250747).length < 2 ^ (prefixWord ++ tailWord_2250747).sum := by decide
  have hdescent : baseEnd_2250747 < baseStart_2250747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250798 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_2250798 : Nat := 118140960795 + 2250798 * 2 ^ 59
def prefixEnd_2250798 : Nat := 4983230072969 + 3 ^ 40 * 2250798 * 2
def baseEnd_2250798 : Nat := 1155741230178589976173775

theorem tailTrace_2250798 : CollatzResearch.WordTrace tailWord_2250798 prefixEnd_2250798 1155741230178589976173775 := by
  unfold tailWord_2250798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10261668412468840817426131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54728898199833817692939365 10261668412468840817426131)
  ·
    refine ⟨15392502618703261226139197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10261668412468840817426131 15392502618703261226139197)
    ·
      refine ⟨5772188482013722959802199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15392502618703261226139197 5772188482013722959802199)
      ·
        refine ⟨8658282723020584439703299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5772188482013722959802199 8658282723020584439703299)
        ·
          refine ⟨12987424084530876659554949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8658282723020584439703299 12987424084530876659554949)
          ·
            refine ⟨2435142015849539373666553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12987424084530876659554949 2435142015849539373666553)
            ·
              refine ⟨1826356511887154530249915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435142015849539373666553 1826356511887154530249915)
              ·
                refine ⟨2739534767830731795374873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826356511887154530249915 2739534767830731795374873)
                ·
                  refine ⟨2054651075873048846531155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739534767830731795374873 2054651075873048846531155)
                  ·
                    refine ⟨3081976613809573269796733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054651075873048846531155 3081976613809573269796733)
                    ·
                      refine ⟨1155741230178589976173775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3081976613809573269796733 1155741230178589976173775)
                      ·
                        rfl

theorem cell23_2250798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_2250798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250798 prefixEnd_2250798 := by exact prefixLift 2250798
  have htrace : WordTrace (prefixWord ++ tailWord_2250798) baseStart_2250798 baseEnd_2250798 := by
    simpa [prefixWord, tailWord_2250798, baseEnd_2250798] using wordTrace_append hprefix tailTrace_2250798
  have hstable : (prefixWord ++ tailWord_2250798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250798).length < 2 ^ (prefixWord ++ tailWord_2250798).sum := by decide
  have hdescent : baseEnd_2250798 < baseStart_2250798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250808 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 1, 3, 2]
def baseStart_2250808 : Nat := 118140960795 + 2250808 * 2 ^ 59
def prefixEnd_2250808 : Nat := 4983230072969 + 3 ^ 40 * 2250808 * 2
def baseEnd_2250808 : Nat := 1155746364985134937048729

theorem tailTrace_2250808 : CollatzResearch.WordTrace tailWord_2250808 prefixEnd_2250808 1155746364985134937048729 := by
  unfold tailWord_2250808
  simp only [CollatzResearch.WordTrace]
  refine ⟨41046856014857249123636539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54729141353142998831515385 41046856014857249123636539)
  ·
    refine ⟨61570284022285873685454809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41046856014857249123636539 61570284022285873685454809)
    ·
      refine ⟨46177713016714405264091107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61570284022285873685454809 46177713016714405264091107)
      ·
        refine ⟨69266569525071607896136661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46177713016714405264091107 69266569525071607896136661)
        ·
          refine ⟨1623435223243865810065703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 69266569525071607896136661 1623435223243865810065703)
          ·
            refine ⟨2435152834865798715098555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623435223243865810065703 2435152834865798715098555)
            ·
              refine ⟨3652729252298698072647833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435152834865798715098555 3652729252298698072647833)
              ·
                refine ⟨2739546939224023554485875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652729252298698072647833 2739546939224023554485875)
                ·
                  refine ⟨4109320408836035331728813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739546939224023554485875 4109320408836035331728813)
                  ·
                    refine ⟨1540995153313513249398305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4109320408836035331728813 1540995153313513249398305)
                    ·
                      refine ⟨1155746364985134937048729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1540995153313513249398305 1155746364985134937048729)
                      ·
                        rfl

theorem cell23_2250808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_2250808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250808 prefixEnd_2250808 := by exact prefixLift 2250808
  have htrace : WordTrace (prefixWord ++ tailWord_2250808) baseStart_2250808 baseEnd_2250808 := by
    simpa [prefixWord, tailWord_2250808, baseEnd_2250808] using wordTrace_append hprefix tailTrace_2250808
  have hstable : (prefixWord ++ tailWord_2250808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250808).length < 2 ^ (prefixWord ++ tailWord_2250808).sum := by decide
  have hdescent : baseEnd_2250808 < baseStart_2250808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250844 : List Nat := [2, 2, 4, 1, 1, 3, 1, 4, 5]
def baseStart_2250844 : Nat := 118140960795 + 2250844 * 2 ^ 59
def prefixEnd_2250844 : Nat := 4983230072969 + 3 ^ 40 * 2250844 * 2
def baseEnd_2250844 : Nat := 128418316698744088466507

theorem tailTrace_2250844 : CollatzResearch.WordTrace tailWord_2250844 prefixEnd_2250844 128418316698744088466507 := by
  unfold tailWord_2250844
  simp only [CollatzResearch.WordTrace]
  refine ⟨41047512528792038197791793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54730016705056050930389057 41047512528792038197791793)
  ·
    refine ⟨30785634396594028648343845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41047512528792038197791793 30785634396594028648343845)
    ·
      refine ⟨5772306449361380371564471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30785634396594028648343845 5772306449361380371564471)
      ·
        refine ⟨8658459674042070557346707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5772306449361380371564471 8658459674042070557346707)
        ·
          refine ⟨12987689511063105836020061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8658459674042070557346707 12987689511063105836020061)
          ·
            refine ⟨4870383566648664688507523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12987689511063105836020061 4870383566648664688507523)
            ·
              refine ⟨7305575349972997032761285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870383566648664688507523 7305575349972997032761285)
              ·
                refine ⟨1369795378119936943642741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7305575349972997032761285 1369795378119936943642741)
                ·
                  refine ⟨128418316698744088466507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1369795378119936943642741 128418316698744088466507)
                  ·
                    rfl

theorem cell23_2250844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_2250844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250844 prefixEnd_2250844 := by exact prefixLift 2250844
  have htrace : WordTrace (prefixWord ++ tailWord_2250844) baseStart_2250844 baseEnd_2250844 := by
    simpa [prefixWord, tailWord_2250844, baseEnd_2250844] using wordTrace_append hprefix tailTrace_2250844
  have hstable : (prefixWord ++ tailWord_2250844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250844).length < 2 ^ (prefixWord ++ tailWord_2250844).sum := by decide
  have hdescent : baseEnd_2250844 < baseStart_2250844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250877 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_2250877 : Nat := 118140960795 + 2250877 * 2 ^ 59
def prefixEnd_2250877 : Nat := 4983230072969 + 3 ^ 40 * 2250877 * 2
def baseEnd_2250877 : Nat := 1155781795150295167085911

theorem tailTrace_2250877 : CollatzResearch.WordTrace tailWord_2250877 prefixEnd_2250877 1155781795150295167085911 := by
  unfold tailWord_2250877
  simp only [CollatzResearch.WordTrace]
  refine ⟨82096228666464523031534885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54730819110976348687689923 82096228666464523031534885)
  ·
    refine ⟨15393042874962098068412791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82096228666464523031534885 15393042874962098068412791)
    ·
      refine ⟨23089564312443147102619187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15393042874962098068412791 23089564312443147102619187)
      ·
        refine ⟨34634346468664720653928781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23089564312443147102619187 34634346468664720653928781)
        ·
          refine ⟨12987879925749270245223293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34634346468664720653928781 12987879925749270245223293)
          ·
            refine ⟨4870454972155976341958735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12987879925749270245223293 4870454972155976341958735)
            ·
              refine ⟨7305682458233964512938103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870454972155976341958735 7305682458233964512938103)
              ·
                refine ⟨10958523687350946769407155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7305682458233964512938103 10958523687350946769407155)
                ·
                  refine ⟨16437785531026420154110733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10958523687350946769407155 16437785531026420154110733)
                  ·
                    refine ⟨6164169574134907557791525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16437785531026420154110733 6164169574134907557791525)
                    ·
                      refine ⟨1155781795150295167085911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6164169574134907557791525 1155781795150295167085911)
                      ·
                        rfl

theorem cell23_2250877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_2250877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250877 prefixEnd_2250877 := by exact prefixLift 2250877
  have htrace : WordTrace (prefixWord ++ tailWord_2250877) baseStart_2250877 baseEnd_2250877 := by
    simpa [prefixWord, tailWord_2250877, baseEnd_2250877] using wordTrace_append hprefix tailTrace_2250877
  have hstable : (prefixWord ++ tailWord_2250877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250877).length < 2 ^ (prefixWord ++ tailWord_2250877).sum := by decide
  have hdescent : baseEnd_2250877 < baseStart_2250877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250914 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2250914 : Nat := 118140960795 + 2250914 * 2 ^ 59
def prefixEnd_2250914 : Nat := 4983230072969 + 3 ^ 40 * 2250914 * 2
def baseEnd_2250914 : Nat := 1155800793934511522323241

theorem tailTrace_2250914 : CollatzResearch.WordTrace tailWord_2250914 prefixEnd_2250914 1155800793934511522323241 := by
  unfold tailWord_2250914
  simp only [CollatzResearch.WordTrace]
  refine ⟨20524394541832619587657949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54731718778220318900421197 20524394541832619587657949)
  ·
    refine ⟨7696647953187232345371731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20524394541832619587657949 7696647953187232345371731)
    ·
      refine ⟨11544971929780848518057597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7696647953187232345371731 11544971929780848518057597)
      ·
        refine ⟨4329364473667818194271599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11544971929780848518057597 4329364473667818194271599)
        ·
          refine ⟨6494046710501727291407399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4329364473667818194271599 6494046710501727291407399)
          ·
            refine ⟨9741070065752590937111099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6494046710501727291407399 9741070065752590937111099)
            ·
              refine ⟨14611605098628886405666649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9741070065752590937111099 14611605098628886405666649)
              ·
                refine ⟨10958703823971664804249987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14611605098628886405666649 10958703823971664804249987)
                ·
                  refine ⟨16438055735957497206374981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10958703823971664804249987 16438055735957497206374981)
                  ·
                    refine ⟨3082135450492030726195309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16438055735957497206374981 3082135450492030726195309)
                    ·
                      refine ⟨1155800793934511522323241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082135450492030726195309 1155800793934511522323241)
                      ·
                        rfl

theorem cell23_2250914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2250914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250914 prefixEnd_2250914 := by exact prefixLift 2250914
  have htrace : WordTrace (prefixWord ++ tailWord_2250914) baseStart_2250914 baseEnd_2250914 := by
    simpa [prefixWord, tailWord_2250914, baseEnd_2250914] using wordTrace_append hprefix tailTrace_2250914
  have hstable : (prefixWord ++ tailWord_2250914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250914).length < 2 ^ (prefixWord ++ tailWord_2250914).sum := by decide
  have hdescent : baseEnd_2250914 < baseStart_2250914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250961 : List Nat := [1, 2, 2, 1, 2, 2, 2, 6, 1, 1, 3]
def baseStart_2250961 : Nat := 118140960795 + 2250961 * 2 ^ 59
def prefixEnd_2250961 : Nat := 4983230072969 + 3 ^ 40 * 2250961 * 2
def baseEnd_2250961 : Nat := 1155824927525272838435525

theorem tailTrace_2250961 : CollatzResearch.WordTrace tailWord_2250961 prefixEnd_2250961 1155824927525272838435525 := by
  unfold tailWord_2250961
  simp only [CollatzResearch.WordTrace]
  refine ⟨82099292398160205377592737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54732861598773470251728491 82099292398160205377592737)
  ·
    refine ⟨61574469298620154033194553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82099292398160205377592737 61574469298620154033194553)
    ·
      refine ⟨46180851973965115524895915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61574469298620154033194553 46180851973965115524895915)
      ·
        refine ⟨69271277960947673287343873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46180851973965115524895915 69271277960947673287343873)
        ·
          refine ⟨51953458470710754965507905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69271277960947673287343873 51953458470710754965507905)
          ·
            refine ⟨38965093853033066224130929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51953458470710754965507905 38965093853033066224130929)
            ·
              refine ⟨29223820389774799668098197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38965093853033066224130929 29223820389774799668098197)
              ·
                refine ⟨1369866580770693734442103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29223820389774799668098197 1369866580770693734442103)
                ·
                  refine ⟨2054799871156040601663155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369866580770693734442103 2054799871156040601663155)
                  ·
                    refine ⟨3082199806734060902494733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054799871156040601663155 3082199806734060902494733)
                    ·
                      refine ⟨1155824927525272838435525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082199806734060902494733 1155824927525272838435525)
                      ·
                        rfl

theorem cell23_2250961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_2250961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250961 prefixEnd_2250961 := by exact prefixLift 2250961
  have htrace : WordTrace (prefixWord ++ tailWord_2250961) baseStart_2250961 baseEnd_2250961 := by
    simpa [prefixWord, tailWord_2250961, baseEnd_2250961] using wordTrace_append hprefix tailTrace_2250961
  have hstable : (prefixWord ++ tailWord_2250961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250961).length < 2 ^ (prefixWord ++ tailWord_2250961).sum := by decide
  have hdescent : baseEnd_2250961 < baseStart_2250961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250967 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_2250967 : Nat := 118140960795 + 2250967 * 2 ^ 59
def prefixEnd_2250967 : Nat := 4983230072969 + 3 ^ 40 * 2250967 * 2
def baseEnd_2250967 : Nat := 1155828008409199814960497

theorem tailTrace_2250967 : CollatzResearch.WordTrace tailWord_2250967 prefixEnd_2250967 1155828008409199814960497 := by
  unfold tailWord_2250967
  simp only [CollatzResearch.WordTrace]
  refine ⟨82099511236138468402311155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54733007490758978934874103 82099511236138468402311155)
  ·
    refine ⟨123149266854207702603466733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82099511236138468402311155 123149266854207702603466733)
    ·
      refine ⟨46180975070327888476300025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123149266854207702603466733 46180975070327888476300025)
      ·
        refine ⟨34635731302745916357225019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46180975070327888476300025 34635731302745916357225019)
        ·
          refine ⟨51953596954118874535837529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34635731302745916357225019 51953596954118874535837529)
          ·
            refine ⟨38965197715589155901878147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51953596954118874535837529 38965197715589155901878147)
            ·
              refine ⟨58447796573383733852817221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38965197715589155901878147 58447796573383733852817221)
              ·
                refine ⟨10958961857509450097403229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58447796573383733852817221 10958961857509450097403229)
                ·
                  refine ⟨4109610696566043786526211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10958961857509450097403229 4109610696566043786526211)
                  ·
                    refine ⟨6164416044849065679789317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109610696566043786526211 6164416044849065679789317)
                    ·
                      refine ⟨1155828008409199814960497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6164416044849065679789317 1155828008409199814960497)
                      ·
                        rfl

theorem cell23_2250967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_2250967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250967 prefixEnd_2250967 := by exact prefixLift 2250967
  have htrace : WordTrace (prefixWord ++ tailWord_2250967) baseStart_2250967 baseEnd_2250967 := by
    simpa [prefixWord, tailWord_2250967, baseEnd_2250967] using wordTrace_append hprefix tailTrace_2250967
  have hstable : (prefixWord ++ tailWord_2250967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250967).length < 2 ^ (prefixWord ++ tailWord_2250967).sum := by decide
  have hdescent : baseEnd_2250967 < baseStart_2250967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250977 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2250977 : Nat := 118140960795 + 2250977 * 2 ^ 59
def prefixEnd_2250977 : Nat := 4983230072969 + 3 ^ 40 * 2250977 * 2
def baseEnd_2250977 : Nat := 385277714405248258611817

theorem tailTrace_2250977 : CollatzResearch.WordTrace tailWord_2250977 prefixEnd_2250977 385277714405248258611817 := by
  unfold tailWord_2250977
  simp only [CollatzResearch.WordTrace]
  refine ⟨82099875966102240110175185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54733250644068160073450123 82099875966102240110175185)
  ·
    refine ⟨61574906974576680082631389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82099875966102240110175185 61574906974576680082631389)
    ·
      refine ⟨23090590115466255030986771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61574906974576680082631389 23090590115466255030986771)
      ·
        refine ⟨34635885173199382546480157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23090590115466255030986771 34635885173199382546480157)
        ·
          refine ⟨12988456939949768454930059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34635885173199382546480157 12988456939949768454930059)
          ·
            refine ⟨19482685409924652682395089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12988456939949768454930059 19482685409924652682395089)
            ·
              refine ⟨14612014057443489511796317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19482685409924652682395089 14612014057443489511796317)
              ·
                refine ⟨5479505271541308566923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14612014057443489511796317 5479505271541308566923619)
                ·
                  refine ⟨8219257907311962850385429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5479505271541308566923619 8219257907311962850385429)
                  ·
                    refine ⟨385277714405248258611817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8219257907311962850385429 385277714405248258611817)
                    ·
                      rfl

theorem cell23_2250977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2250977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250977 prefixEnd_2250977 := by exact prefixLift 2250977
  have htrace : WordTrace (prefixWord ++ tailWord_2250977) baseStart_2250977 baseEnd_2250977 := by
    simpa [prefixWord, tailWord_2250977, baseEnd_2250977] using wordTrace_append hprefix tailTrace_2250977
  have hstable : (prefixWord ++ tailWord_2250977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250977).length < 2 ^ (prefixWord ++ tailWord_2250977).sum := by decide
  have hdescent : baseEnd_2250977 < baseStart_2250977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250981 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_2250981 : Nat := 118140960795 + 2250981 * 2 ^ 59
def prefixEnd_2250981 : Nat := 4983230072969 + 3 ^ 40 * 2250981 * 2
def baseEnd_2250981 : Nat := 385278399046120920061811

theorem tailTrace_2250981 : CollatzResearch.WordTrace tailWord_2250981 prefixEnd_2250981 385278399046120920061811 := by
  unfold tailWord_2250981
  simp only [CollatzResearch.WordTrace]
  refine ⟨82100021858087748793320797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54733347905391832528880531 82100021858087748793320797)
  ·
    refine ⟨30787508196782905797495299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82100021858087748793320797 30787508196782905797495299)
    ·
      refine ⟨46181262295174358696242949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30787508196782905797495299 46181262295174358696242949)
      ·
        refine ⟨8658986680345192255545553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46181262295174358696242949 8658986680345192255545553)
        ·
          refine ⟨6494240010258894191659165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8658986680345192255545553 6494240010258894191659165)
          ·
            refine ⟨2435340003847085321872187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6494240010258894191659165 2435340003847085321872187)
            ·
              refine ⟨3653010005770627982808281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435340003847085321872187 3653010005770627982808281)
              ·
                refine ⟨2739757504327970987106211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3653010005770627982808281 2739757504327970987106211)
                ·
                  refine ⟨4109636256491956480659317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739757504327970987106211 4109636256491956480659317)
                  ·
                    refine ⟨385278399046120920061811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4109636256491956480659317 385278399046120920061811)
                    ·
                      rfl

theorem cell23_2250981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_2250981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250981 prefixEnd_2250981 := by exact prefixLift 2250981
  have htrace : WordTrace (prefixWord ++ tailWord_2250981) baseStart_2250981 baseEnd_2250981 := by
    simpa [prefixWord, tailWord_2250981, baseEnd_2250981] using wordTrace_append hprefix tailTrace_2250981
  have hstable : (prefixWord ++ tailWord_2250981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250981).length < 2 ^ (prefixWord ++ tailWord_2250981).sum := by decide
  have hdescent : baseEnd_2250981 < baseStart_2250981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250984 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2250984 : Nat := 118140960795 + 2250984 * 2 ^ 59
def prefixEnd_2250984 : Nat := 4983230072969 + 3 ^ 40 * 2250984 * 2
def baseEnd_2250984 : Nat := 1155836737580326248447919

theorem tailTrace_2250984 : CollatzResearch.WordTrace tailWord_2250984 prefixEnd_2250984 1155836737580326248447919 := by
  unfold tailWord_2250984
  simp only [CollatzResearch.WordTrace]
  refine ⟨41050065638538440152840003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54733420851384586870453337 41050065638538440152840003)
  ·
    refine ⟨61575098457807660229260005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41050065638538440152840003 61575098457807660229260005)
    ·
      refine ⟨11545330960838936292986251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61575098457807660229260005 11545330960838936292986251)
      ·
        refine ⟨17317996441258404439479377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11545330960838936292986251 17317996441258404439479377)
        ·
          refine ⟨12988497330943803329609533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17317996441258404439479377 12988497330943803329609533)
          ·
            refine ⟨4870686499103926248603575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12988497330943803329609533 4870686499103926248603575)
            ·
              refine ⟨7306029748655889372905363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870686499103926248603575 7306029748655889372905363)
              ·
                refine ⟨10959044622983834059358045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7306029748655889372905363 10959044622983834059358045)
                ·
                  refine ⟨4109641733618937772259267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10959044622983834059358045 4109641733618937772259267)
                  ·
                    refine ⟨6164462600428406658388901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109641733618937772259267 6164462600428406658388901)
                    ·
                      refine ⟨1155836737580326248447919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6164462600428406658388901 1155836737580326248447919)
                      ·
                        rfl

theorem cell23_2250984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2250984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250984 prefixEnd_2250984 := by exact prefixLift 2250984
  have htrace : WordTrace (prefixWord ++ tailWord_2250984) baseStart_2250984 baseEnd_2250984 := by
    simpa [prefixWord, tailWord_2250984, baseEnd_2250984] using wordTrace_append hprefix tailTrace_2250984
  have hstable : (prefixWord ++ tailWord_2250984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250984).length < 2 ^ (prefixWord ++ tailWord_2250984).sum := by decide
  have hdescent : baseEnd_2250984 < baseStart_2250984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2250994 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_2250994 : Nat := 118140960795 + 2250994 * 2 ^ 59
def prefixEnd_2250994 : Nat := 4983230072969 + 3 ^ 40 * 2250994 * 2
def baseEnd_2250994 : Nat := 385280624128957069774291

theorem tailTrace_2250994 : CollatzResearch.WordTrace tailWord_2250994 prefixEnd_2250994 385280624128957069774291 := by
  unfold tailWord_2250994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20525124001760163003386009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54733664004693768009029357 20525124001760163003386009)
  ·
    refine ⟨15393843001320122252539507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20525124001760163003386009 15393843001320122252539507)
    ·
      refine ⟨23090764501980183378809261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15393843001320122252539507 23090764501980183378809261)
      ·
        refine ⟨8659036688242568767053473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23090764501980183378809261 8659036688242568767053473)
        ·
          refine ⟨6494277516181926575290105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8659036688242568767053473 6494277516181926575290105)
          ·
            refine ⟨4870708137136444931467579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6494277516181926575290105 4870708137136444931467579)
            ·
              refine ⟨7306062205704667397201369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870708137136444931467579 7306062205704667397201369)
              ·
                refine ⟨5479546654278500547901027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7306062205704667397201369 5479546654278500547901027)
                ·
                  refine ⟨8219319981417750821851541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5479546654278500547901027 8219319981417750821851541)
                  ·
                    refine ⟨385280624128957069774291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8219319981417750821851541 385280624128957069774291)
                    ·
                      rfl

theorem cell23_2250994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_2250994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2250994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2250994 prefixEnd_2250994 := by exact prefixLift 2250994
  have htrace : WordTrace (prefixWord ++ tailWord_2250994) baseStart_2250994 baseEnd_2250994 := by
    simpa [prefixWord, tailWord_2250994, baseEnd_2250994] using wordTrace_append hprefix tailTrace_2250994
  have hstable : (prefixWord ++ tailWord_2250994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2250994).length < 2 ^ (prefixWord ++ tailWord_2250994).sum := by decide
  have hdescent : baseEnd_2250994 < baseStart_2250994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2250994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251004 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_2251004 : Nat := 118140960795 + 2251004 * 2 ^ 59
def prefixEnd_2251004 : Nat := 4983230072969 + 3 ^ 40 * 2251004 * 2
def baseEnd_2251004 : Nat := 1155847007193416170197827

theorem tailTrace_2251004 : CollatzResearch.WordTrace tailWord_2251004 prefixEnd_2251004 1155847007193416170197827 := by
  unfold tailWord_2251004
  simp only [CollatzResearch.WordTrace]
  refine ⟨41050430368502211860704033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54733907158002949147605377 41050430368502211860704033)
  ·
    refine ⟨30787822776376658895528025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41050430368502211860704033 30787822776376658895528025)
    ·
      refine ⟨23090867082282494171646019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30787822776376658895528025 23090867082282494171646019)
      ·
        refine ⟨34636300623423741257469029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23090867082282494171646019 34636300623423741257469029)
        ·
          refine ⟨6494306366891951485775443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34636300623423741257469029 6494306366891951485775443)
          ·
            refine ⟨9741459550337927228663165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6494306366891951485775443 9741459550337927228663165)
            ·
              refine ⟨3653047331376722710748687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9741459550337927228663165 3653047331376722710748687)
              ·
                refine ⟨5479570997065084066123031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653047331376722710748687 5479570997065084066123031)
                ·
                  refine ⟨8219356495597626099184547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5479570997065084066123031 8219356495597626099184547)
                  ·
                    refine ⟨12329034743396439148776821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8219356495597626099184547 12329034743396439148776821)
                    ·
                      refine ⟨1155847007193416170197827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12329034743396439148776821 1155847007193416170197827)
                      ·
                        rfl

theorem cell23_2251004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_2251004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251004 prefixEnd_2251004 := by exact prefixLift 2251004
  have htrace : WordTrace (prefixWord ++ tailWord_2251004) baseStart_2251004 baseEnd_2251004 := by
    simpa [prefixWord, tailWord_2251004, baseEnd_2251004] using wordTrace_append hprefix tailTrace_2251004
  have hstable : (prefixWord ++ tailWord_2251004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251004).length < 2 ^ (prefixWord ++ tailWord_2251004).sum := by decide
  have hdescent : baseEnd_2251004 < baseStart_2251004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251012 : List Nat := [2, 3, 2, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_2251012 : Nat := 118140960795 + 2251012 * 2 ^ 59
def prefixEnd_2251012 : Nat := 4983230072969 + 3 ^ 40 * 2251012 * 2
def baseEnd_2251012 : Nat := 1155851115038652138897791

theorem tailTrace_2251012 : CollatzResearch.WordTrace tailWord_2251012 prefixEnd_2251012 1155851115038652138897791 := by
  unfold tailWord_2251012
  simp only [CollatzResearch.WordTrace]
  refine ⟨41050576260487720543849645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54734101680650294058466193 41050576260487720543849645)
  ·
    refine ⟨15393966097682895203943617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41050576260487720543849645 15393966097682895203943617)
    ·
      refine ⟨11545474573262171402957713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15393966097682895203943617 11545474573262171402957713)
      ·
        refine ⟨8659105929946628552218285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11545474573262171402957713 8659105929946628552218285)
        ·
          refine ⟨3247164723729985707081857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8659105929946628552218285 3247164723729985707081857)
          ·
            refine ⟨2435373542797489280311393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3247164723729985707081857 2435373542797489280311393)
            ·
              refine ⟨1826530157098116960233545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435373542797489280311393 1826530157098116960233545)
              ·
                refine ⟨1369897617823587720175159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826530157098116960233545 1369897617823587720175159)
                ·
                  refine ⟨2054846426735381580262739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369897617823587720175159 2054846426735381580262739)
                  ·
                    refine ⟨3082269640103072370394109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054846426735381580262739 3082269640103072370394109)
                    ·
                      refine ⟨1155851115038652138897791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082269640103072370394109 1155851115038652138897791)
                      ·
                        rfl

theorem cell23_2251012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_2251012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251012 prefixEnd_2251012 := by exact prefixLift 2251012
  have htrace : WordTrace (prefixWord ++ tailWord_2251012) baseStart_2251012 baseEnd_2251012 := by
    simpa [prefixWord, tailWord_2251012, baseEnd_2251012] using wordTrace_append hprefix tailTrace_2251012
  have hstable : (prefixWord ++ tailWord_2251012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251012).length < 2 ^ (prefixWord ++ tailWord_2251012).sum := by decide
  have hdescent : baseEnd_2251012 < baseStart_2251012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251038 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2251038 : Nat := 118140960795 + 2251038 * 2 ^ 59
def prefixEnd_2251038 : Nat := 4983230072969 + 3 ^ 40 * 2251038 * 2
def baseEnd_2251038 : Nat := 1155864465535669037172671

theorem tailTrace_2251038 : CollatzResearch.WordTrace tailWord_2251038 prefixEnd_2251038 1155864465535669037172671 := by
  unfold tailWord_2251038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10262762602360155941018221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54734733879254165018763845 10262762602360155941018221)
  ·
    refine ⟨3848535975885058477881833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10262762602360155941018221 3848535975885058477881833)
    ·
      refine ⟨2886401981913793858411375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3848535975885058477881833 2886401981913793858411375)
      ·
        refine ⟨4329602972870690787617063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886401981913793858411375 4329602972870690787617063)
        ·
          refine ⟨6494404459306036181425595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4329602972870690787617063 6494404459306036181425595)
          ·
            refine ⟨9741606688959054272138393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6494404459306036181425595 9741606688959054272138393)
            ·
              refine ⟨7306205016719290704103795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9741606688959054272138393 7306205016719290704103795)
              ·
                refine ⟨10959307525078936056155693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7306205016719290704103795 10959307525078936056155693)
                ·
                  refine ⟨4109740321904601021058385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10959307525078936056155693 4109740321904601021058385)
                  ·
                    refine ⟨3082305241428450765793789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4109740321904601021058385 3082305241428450765793789)
                    ·
                      refine ⟨1155864465535669037172671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082305241428450765793789 1155864465535669037172671)
                      ·
                        rfl

theorem cell23_2251038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2251038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251038 prefixEnd_2251038 := by exact prefixLift 2251038
  have htrace : WordTrace (prefixWord ++ tailWord_2251038) baseStart_2251038 baseEnd_2251038 := by
    simpa [prefixWord, tailWord_2251038, baseEnd_2251038] using wordTrace_append hprefix tailTrace_2251038
  have hstable : (prefixWord ++ tailWord_2251038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251038).length < 2 ^ (prefixWord ++ tailWord_2251038).sum := by decide
  have hdescent : baseEnd_2251038 < baseStart_2251038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251077 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_2251077 : Nat := 118140960795 + 2251077 * 2 ^ 59
def prefixEnd_2251077 : Nat := 4983230072969 + 3 ^ 40 * 2251077 * 2
def baseEnd_2251077 : Nat := 1155884491281194384584991

theorem tailTrace_2251077 : CollatzResearch.WordTrace tailWord_2251077 prefixEnd_2251077 1155884491281194384584991 := by
  unfold tailWord_2251077
  simp only [CollatzResearch.WordTrace]
  refine ⟨82103523265739957188815485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54735682177159971459210323 82103523265739957188815485)
  ·
    refine ⟨30788821224652483945805807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82103523265739957188815485 30788821224652483945805807)
    ·
      refine ⟨46183231836978725918708711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30788821224652483945805807 46183231836978725918708711)
      ·
        refine ⟨69274847755468088878063067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46183231836978725918708711 69274847755468088878063067)
        ·
          refine ⟨103912271633202133317094601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69274847755468088878063067 103912271633202133317094601)
          ·
            refine ⟨77934203724901599987820951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103912271633202133317094601 77934203724901599987820951)
            ·
              refine ⟨116901305587352399981731427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77934203724901599987820951 116901305587352399981731427)
              ·
                refine ⟨175351958381028599972597141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116901305587352399981731427 175351958381028599972597141)
                ·
                  refine ⟨8219623049110715623715491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175351958381028599972597141 8219623049110715623715491)
                  ·
                    refine ⟨12329434573666073435573237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8219623049110715623715491 12329434573666073435573237)
                    ·
                      refine ⟨1155884491281194384584991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12329434573666073435573237 1155884491281194384584991)
                      ·
                        rfl

theorem cell23_2251077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_2251077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251077 prefixEnd_2251077 := by exact prefixLift 2251077
  have htrace : WordTrace (prefixWord ++ tailWord_2251077) baseStart_2251077 baseEnd_2251077 := by
    simpa [prefixWord, tailWord_2251077, baseEnd_2251077] using wordTrace_append hprefix tailTrace_2251077
  have hstable : (prefixWord ++ tailWord_2251077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251077).length < 2 ^ (prefixWord ++ tailWord_2251077).sum := by decide
  have hdescent : baseEnd_2251077 < baseStart_2251077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251087 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_2251087 : Nat := 118140960795 + 2251087 * 2 ^ 59
def prefixEnd_2251087 : Nat := 4983230072969 + 3 ^ 40 * 2251087 * 2
def baseEnd_2251087 : Nat := 1155889626087739345459945

theorem tailTrace_2251087 : CollatzResearch.WordTrace tailWord_2251087 prefixEnd_2251087 1155889626087739345459945 := by
  unfold tailWord_2251087
  simp only [CollatzResearch.WordTrace]
  refine ⟨82103887995703728896679515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54735925330469152597786343 82103887995703728896679515)
  ·
    refine ⟨123155831993555593345019273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82103887995703728896679515 123155831993555593345019273)
    ·
      refine ⟨92366873995166695008764455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123155831993555593345019273 92366873995166695008764455)
      ·
        refine ⟨138550310992750042513146683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92366873995166695008764455 138550310992750042513146683)
        ·
          refine ⟨207825466489125063769720025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138550310992750042513146683 207825466489125063769720025)
          ·
            refine ⟨155869099866843797827290019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207825466489125063769720025 155869099866843797827290019)
            ·
              refine ⟨233803649800265696740935029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155869099866843797827290019 233803649800265696740935029)
              ·
                refine ⟨21919092168774909069462659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233803649800265696740935029 21919092168774909069462659)
                ·
                  refine ⟨32878638253162363604193989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21919092168774909069462659 32878638253162363604193989)
                  ·
                    refine ⟨6164744672467943175786373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32878638253162363604193989 6164744672467943175786373)
                    ·
                      refine ⟨1155889626087739345459945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6164744672467943175786373 1155889626087739345459945)
                      ·
                        rfl

theorem cell23_2251087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_2251087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251087 prefixEnd_2251087 := by exact prefixLift 2251087
  have htrace : WordTrace (prefixWord ++ tailWord_2251087) baseStart_2251087 baseEnd_2251087 := by
    simpa [prefixWord, tailWord_2251087, baseEnd_2251087] using wordTrace_append hprefix tailTrace_2251087
  have hstable : (prefixWord ++ tailWord_2251087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251087).length < 2 ^ (prefixWord ++ tailWord_2251087).sum := by decide
  have hdescent : baseEnd_2251087 < baseStart_2251087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251127 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 3, 7]
def baseStart_2251127 : Nat := 118140960795 + 2251127 * 2 ^ 59
def prefixEnd_2251127 : Nat := 4983230072969 + 3 ^ 40 * 2251127 * 2
def baseEnd_2251127 : Nat := 385303388437973062986587

theorem tailTrace_2251127 : CollatzResearch.WordTrace tailWord_2251127 prefixEnd_2251127 385303388437973062986587 := by
  unfold tailWord_2251127
  simp only [CollatzResearch.WordTrace]
  refine ⟨82105346915558815728135635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54736897943705877152090423 82105346915558815728135635)
  ·
    refine ⟨123158020373338223592203453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82105346915558815728135635 123158020373338223592203453)
    ·
      refine ⟨46184257640001833847076295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123158020373338223592203453 46184257640001833847076295)
      ·
        refine ⟨69276386460002750770614443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46184257640001833847076295 69276386460002750770614443)
        ·
          refine ⟨103914579690004126155921665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69276386460002750770614443 103914579690004126155921665)
          ·
            refine ⟨77935934767503094616941249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103914579690004126155921665 77935934767503094616941249)
            ·
              refine ⟨58451951075627320962705937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77935934767503094616941249 58451951075627320962705937)
              ·
                refine ⟨43838963306720490722029453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58451951075627320962705937 43838963306720490722029453)
                ·
                  refine ⟨16439611240020184020761045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43838963306720490722029453 16439611240020184020761045)
                  ·
                    refine ⟨385303388437973062986587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16439611240020184020761045 385303388437973062986587)
                    ·
                      rfl

theorem cell23_2251127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_2251127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251127 prefixEnd_2251127 := by exact prefixLift 2251127
  have htrace : WordTrace (prefixWord ++ tailWord_2251127) baseStart_2251127 baseEnd_2251127 := by
    simpa [prefixWord, tailWord_2251127, baseEnd_2251127] using wordTrace_append hprefix tailTrace_2251127
  have hstable : (prefixWord ++ tailWord_2251127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251127).length < 2 ^ (prefixWord ++ tailWord_2251127).sum := by decide
  have hdescent : baseEnd_2251127 < baseStart_2251127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251144 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 4, 5]
def baseStart_2251144 : Nat := 118140960795 + 2251144 * 2 ^ 59
def prefixEnd_2251144 : Nat := 4983230072969 + 3 ^ 40 * 2251144 * 2
def baseEnd_2251144 : Nat := 385306298161681874149061

theorem tailTrace_2251144 : CollatzResearch.WordTrace tailWord_2251144 prefixEnd_2251144 385306298161681874149061 := by
  unfold tailWord_2251144
  simp only [CollatzResearch.WordTrace]
  refine ⟨41052983478248613815752243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54737311304331485087669657 41052983478248613815752243)
  ·
    refine ⟨61579475217372920723628365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41052983478248613815752243 61579475217372920723628365)
    ·
      refine ⟨23092303206514845271360637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61579475217372920723628365 23092303206514845271360637)
      ·
        refine ⟨8659613702443066976760239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23092303206514845271360637 8659613702443066976760239)
        ·
          refine ⟨12989420553664600465140359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8659613702443066976760239 12989420553664600465140359)
          ·
            refine ⟨19484130830496900697710539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12989420553664600465140359 19484130830496900697710539)
            ·
              refine ⟨29226196245745351046565809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19484130830496900697710539 29226196245745351046565809)
              ·
                refine ⟨21919647184309013284924357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29226196245745351046565809 21919647184309013284924357)
                ·
                  refine ⟨4109933847057939990923317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21919647184309013284924357 4109933847057939990923317)
                  ·
                    refine ⟨385306298161681874149061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4109933847057939990923317 385306298161681874149061)
                    ·
                      rfl

theorem cell23_2251144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_2251144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251144 prefixEnd_2251144 := by exact prefixLift 2251144
  have htrace : WordTrace (prefixWord ++ tailWord_2251144) baseStart_2251144 baseEnd_2251144 := by
    simpa [prefixWord, tailWord_2251144, baseEnd_2251144] using wordTrace_append hprefix tailTrace_2251144
  have hstable : (prefixWord ++ tailWord_2251144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251144).length < 2 ^ (prefixWord ++ tailWord_2251144).sum := by decide
  have hdescent : baseEnd_2251144 < baseStart_2251144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251248 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 3, 1, 3]
def baseStart_2251248 : Nat := 118140960795 + 2251248 * 2 ^ 59
def prefixEnd_2251248 : Nat := 4983230072969 + 3 ^ 40 * 2251248 * 2
def baseEnd_2251248 : Nat := 1155972296473113215546705

theorem tailTrace_2251248 : CollatzResearch.WordTrace tailWord_2251248 prefixEnd_2251248 1155972296473113215546705 := by
  unfold tailWord_2251248
  simp only [CollatzResearch.WordTrace]
  refine ⟨41054880074060226696645199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54739840098746968928860265 41054880074060226696645199)
  ·
    refine ⟨61582320111090340044967799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41054880074060226696645199 61582320111090340044967799)
    ·
      refine ⟨92373480166635510067451699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61582320111090340044967799 92373480166635510067451699)
      ·
        refine ⟨138560220249953265101177549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92373480166635510067451699 138560220249953265101177549)
        ·
          refine ⟨51960082593732474412941581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138560220249953265101177549 51960082593732474412941581)
          ·
            refine ⟨19485030972649677904853093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51960082593732474412941581 19485030972649677904853093)
            ·
              refine ⟨3653443307371814607159955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19485030972649677904853093 3653443307371814607159955)
              ·
                refine ⟨5480164961057721910739933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653443307371814607159955 5480164961057721910739933)
                ·
                  refine ⟨2055061860396645716527475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5480164961057721910739933 2055061860396645716527475)
                  ·
                    refine ⟨3082592790594968574791213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055061860396645716527475 3082592790594968574791213)
                    ·
                      refine ⟨1155972296473113215546705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082592790594968574791213 1155972296473113215546705)
                      ·
                        rfl

theorem cell23_2251248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 1, 3].length) (baseStart_2251248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251248 prefixEnd_2251248 := by exact prefixLift 2251248
  have htrace : WordTrace (prefixWord ++ tailWord_2251248) baseStart_2251248 baseEnd_2251248 := by
    simpa [prefixWord, tailWord_2251248, baseEnd_2251248] using wordTrace_append hprefix tailTrace_2251248
  have hstable : (prefixWord ++ tailWord_2251248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251248).length < 2 ^ (prefixWord ++ tailWord_2251248).sum := by decide
  have hdescent : baseEnd_2251248 < baseStart_2251248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251268 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_2251268 : Nat := 118140960795 + 2251268 * 2 ^ 59
def prefixEnd_2251268 : Nat := 4983230072969 + 3 ^ 40 * 2251268 * 2
def baseEnd_2251268 : Nat := 385327522028734379098871

theorem tailTrace_2251268 : CollatzResearch.WordTrace tailWord_2251268 prefixEnd_2251268 385327522028734379098871 := by
  unfold tailWord_2251268
  simp only [CollatzResearch.WordTrace]
  refine ⟨41055244804023998404509229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54740326405365331206012305 41055244804023998404509229)
  ·
    refine ⟨15395716801508999401690961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41055244804023998404509229 15395716801508999401690961)
    ·
      refine ⟨11546787601131749551268221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15395716801508999401690961 11546787601131749551268221)
      ·
        refine ⟨4330045350424406081725583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11546787601131749551268221 4330045350424406081725583)
        ·
          refine ⟨6495068025636609122588375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4330045350424406081725583 6495068025636609122588375)
          ·
            refine ⟨9742602038454913683882563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495068025636609122588375 9742602038454913683882563)
            ·
              refine ⟨14613903057682370525823845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9742602038454913683882563 14613903057682370525823845)
              ·
                refine ⟨2740106823315444473591971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14613903057682370525823845 2740106823315444473591971)
                ·
                  refine ⟨4110160234973166710387957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740106823315444473591971 4110160234973166710387957)
                  ·
                    refine ⟨385327522028734379098871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4110160234973166710387957 385327522028734379098871)
                    ·
                      rfl

theorem cell23_2251268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_2251268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251268 prefixEnd_2251268 := by exact prefixLift 2251268
  have htrace : WordTrace (prefixWord ++ tailWord_2251268) baseStart_2251268 baseEnd_2251268 := by
    simpa [prefixWord, tailWord_2251268, baseEnd_2251268] using wordTrace_append hprefix tailTrace_2251268
  have hstable : (prefixWord ++ tailWord_2251268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251268).length < 2 ^ (prefixWord ++ tailWord_2251268).sum := by decide
  have hdescent : baseEnd_2251268 < baseStart_2251268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251288 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2251288 : Nat := 118140960795 + 2251288 * 2 ^ 59
def prefixEnd_2251288 : Nat := 4983230072969 + 3 ^ 40 * 2251288 * 2
def baseEnd_2251288 : Nat := 1155992835699293059046521

theorem tailTrace_2251288 : CollatzResearch.WordTrace tailWord_2251288 prefixEnd_2251288 1155992835699293059046521 := by
  unfold tailWord_2251288
  simp only [CollatzResearch.WordTrace]
  refine ⟨41055609533987770112373259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54740812711983693483164345 41055609533987770112373259)
  ·
    refine ⟨61583414300981655168559889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41055609533987770112373259 61583414300981655168559889)
    ·
      refine ⟨46187560725736241376419917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61583414300981655168559889 46187560725736241376419917)
      ·
        refine ⟨17320335272151090516157469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46187560725736241376419917 17320335272151090516157469)
        ·
          refine ⟨6495125727056658943559051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17320335272151090516157469 6495125727056658943559051)
          ·
            refine ⟨9742688590584988415338577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495125727056658943559051 9742688590584988415338577)
            ·
              refine ⟨7307016442938741311503933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9742688590584988415338577 7307016442938741311503933)
              ·
                refine ⟨2740131166102027991813975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7307016442938741311503933 2740131166102027991813975)
                ·
                  refine ⟨4110196749153041987720963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740131166102027991813975 4110196749153041987720963)
                  ·
                    refine ⟨6165295123729562981581445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4110196749153041987720963 6165295123729562981581445)
                    ·
                      refine ⟨1155992835699293059046521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6165295123729562981581445 1155992835699293059046521)
                      ·
                        rfl

theorem cell23_2251288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2251288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251288 prefixEnd_2251288 := by exact prefixLift 2251288
  have htrace : WordTrace (prefixWord ++ tailWord_2251288) baseStart_2251288 baseEnd_2251288 := by
    simpa [prefixWord, tailWord_2251288, baseEnd_2251288] using wordTrace_append hprefix tailTrace_2251288
  have hstable : (prefixWord ++ tailWord_2251288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251288).length < 2 ^ (prefixWord ++ tailWord_2251288).sum := by decide
  have hdescent : baseEnd_2251288 < baseStart_2251288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251298 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2251298 : Nat := 118140960795 + 2251298 * 2 ^ 59
def prefixEnd_2251298 : Nat := 4983230072969 + 3 ^ 40 * 2251298 * 2
def baseEnd_2251298 : Nat := 385332656835279339973825

theorem tailTrace_2251298 : CollatzResearch.WordTrace tailWord_2251298 prefixEnd_2251298 385332656835279339973825 := by
  unfold tailWord_2251298
  simp only [CollatzResearch.WordTrace]
  refine ⟨20527895949484827983152637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54741055865292874621740365 20527895949484827983152637)
  ·
    refine ⟨7697960981056810493682239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20527895949484827983152637 7697960981056810493682239)
    ·
      refine ⟨11546941471585215740523359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7697960981056810493682239 11546941471585215740523359)
      ·
        refine ⟨17320412207377823610785039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11546941471585215740523359 17320412207377823610785039)
        ·
          refine ⟨25980618311066735416177559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17320412207377823610785039 25980618311066735416177559)
          ·
            refine ⟨38970927466600103124266339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25980618311066735416177559 38970927466600103124266339)
            ·
              refine ⟨58456391199900154686399509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38970927466600103124266339 58456391199900154686399509)
              ·
                refine ⟨2740143337495319750924977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58456391199900154686399509 2740143337495319750924977)
                ·
                  refine ⟨2055107503121489813193733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2740143337495319750924977 2055107503121489813193733)
                  ·
                    refine ⟨385332656835279339973825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2055107503121489813193733 385332656835279339973825)
                    ·
                      rfl

theorem cell23_2251298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2251298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251298 prefixEnd_2251298 := by exact prefixLift 2251298
  have htrace : WordTrace (prefixWord ++ tailWord_2251298) baseStart_2251298 baseEnd_2251298 := by
    simpa [prefixWord, tailWord_2251298, baseEnd_2251298] using wordTrace_append hprefix tailTrace_2251298
  have hstable : (prefixWord ++ tailWord_2251298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251298).length < 2 ^ (prefixWord ++ tailWord_2251298).sum := by decide
  have hdescent : baseEnd_2251298 < baseStart_2251298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251318 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2251318 : Nat := 118140960795 + 2251318 * 2 ^ 59
def prefixEnd_2251318 : Nat := 4983230072969 + 3 ^ 40 * 2251318 * 2
def baseEnd_2251318 : Nat := 1156008240118927941671383

theorem tailTrace_2251318 : CollatzResearch.WordTrace tailWord_2251318 prefixEnd_2251318 1156008240118927941671383 := by
  unfold tailWord_2251318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132019578616678459271163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54741542171911236898892405 5132019578616678459271163)
  ·
    refine ⟨7698029367925017688906745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5132019578616678459271163 7698029367925017688906745)
    ·
      refine ⟨5773522025943763266680059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7698029367925017688906745 5773522025943763266680059)
      ·
        refine ⟨8660283038915644900020089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5773522025943763266680059 8660283038915644900020089)
        ·
          refine ⟨6495212279186733675015067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8660283038915644900020089 6495212279186733675015067)
          ·
            refine ⟨9742818418780100512522601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495212279186733675015067 9742818418780100512522601)
            ·
              refine ⟨7307113814085075384391951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9742818418780100512522601 7307113814085075384391951)
              ·
                refine ⟨10960670721127613076587927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7307113814085075384391951 10960670721127613076587927)
                ·
                  refine ⟨16441006081691419614881891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10960670721127613076587927 16441006081691419614881891)
                  ·
                    refine ⟨24661509122537129422322837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16441006081691419614881891 24661509122537129422322837)
                    ·
                      refine ⟨1156008240118927941671383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24661509122537129422322837 1156008240118927941671383)
                      ·
                        rfl

theorem cell23_2251318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2251318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251318 prefixEnd_2251318 := by exact prefixLift 2251318
  have htrace : WordTrace (prefixWord ++ tailWord_2251318) baseStart_2251318 baseEnd_2251318 := by
    simpa [prefixWord, tailWord_2251318, baseEnd_2251318] using wordTrace_append hprefix tailTrace_2251318
  have hstable : (prefixWord ++ tailWord_2251318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251318).length < 2 ^ (prefixWord ++ tailWord_2251318).sum := by decide
  have hdescent : baseEnd_2251318 < baseStart_2251318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251325 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2251325 : Nat := 118140960795 + 2251325 * 2 ^ 59
def prefixEnd_2251325 : Nat := 4983230072969 + 3 ^ 40 * 2251325 * 2
def baseEnd_2251325 : Nat := 1156011834483509414283851

theorem tailTrace_2251325 : CollatzResearch.WordTrace tailWord_2251325 prefixEnd_2251325 1156011834483509414283851 := by
  unfold tailWord_2251325
  simp only [CollatzResearch.WordTrace]
  refine ⟨82112568568841495543843429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54741712379227663695895619 82112568568841495543843429)
  ·
    refine ⟨15396106606657780414470643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82112568568841495543843429 15396106606657780414470643)
    ·
      refine ⟨23094159909986670621705965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15396106606657780414470643 23094159909986670621705965)
      ·
        refine ⟨8660309966245001483139737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23094159909986670621705965 8660309966245001483139737)
        ·
          refine ⟨6495232474683751112354803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8660309966245001483139737 6495232474683751112354803)
          ·
            refine ⟨9742848712025626668532205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495232474683751112354803 9742848712025626668532205)
            ·
              refine ⟨3653568267009610000699577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9742848712025626668532205 3653568267009610000699577)
              ·
                refine ⟨2740176200257207500524683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3653568267009610000699577 2740176200257207500524683)
                ·
                  refine ⟨4110264300385811250787025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740176200257207500524683 4110264300385811250787025)
                  ·
                    refine ⟨3082698225289358438090269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110264300385811250787025 3082698225289358438090269)
                    ·
                      refine ⟨1156011834483509414283851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082698225289358438090269 1156011834483509414283851)
                      ·
                        rfl

theorem cell23_2251325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2251325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251325 prefixEnd_2251325 := by exact prefixLift 2251325
  have htrace : WordTrace (prefixWord ++ tailWord_2251325) baseStart_2251325 baseEnd_2251325 := by
    simpa [prefixWord, tailWord_2251325, baseEnd_2251325] using wordTrace_append hprefix tailTrace_2251325
  have hstable : (prefixWord ++ tailWord_2251325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251325).length < 2 ^ (prefixWord ++ tailWord_2251325).sum := by decide
  have hdescent : baseEnd_2251325 < baseStart_2251325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251332 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2251332 : Nat := 118140960795 + 2251332 * 2 ^ 59
def prefixEnd_2251332 : Nat := 4983230072969 + 3 ^ 40 * 2251332 * 2
def baseEnd_2251332 : Nat := 385338476282696962298773

theorem tailTrace_2251332 : CollatzResearch.WordTrace tailWord_2251332 prefixEnd_2251332 385338476282696962298773 := by
  unfold tailWord_2251332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41056411939908067869674125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54741882586544090492898833 41056411939908067869674125)
  ·
    refine ⟨15396154477465525451127797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41056411939908067869674125 15396154477465525451127797)
    ·
      refine ⟨1443389482262393011043231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15396154477465525451127797 1443389482262393011043231)
      ·
        refine ⟨2165084223393589516564847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443389482262393011043231 2165084223393589516564847)
        ·
          refine ⟨3247626335090384274847271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2165084223393589516564847 3247626335090384274847271)
          ·
            refine ⟨4871439502635576412270907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247626335090384274847271 4871439502635576412270907)
            ·
              refine ⟨7307159253953364618406361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4871439502635576412270907 7307159253953364618406361)
              ·
                refine ⟨5480369440465023463804771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7307159253953364618406361 5480369440465023463804771)
                ·
                  refine ⟨8220554160697535195707157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480369440465023463804771 8220554160697535195707157)
                  ·
                    refine ⟨385338476282696962298773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8220554160697535195707157 385338476282696962298773)
                    ·
                      rfl

theorem cell23_2251332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2251332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251332 prefixEnd_2251332 := by exact prefixLift 2251332
  have htrace : WordTrace (prefixWord ++ tailWord_2251332) baseStart_2251332 baseEnd_2251332 := by
    simpa [prefixWord, tailWord_2251332, baseEnd_2251332] using wordTrace_append hprefix tailTrace_2251332
  have hstable : (prefixWord ++ tailWord_2251332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251332).length < 2 ^ (prefixWord ++ tailWord_2251332).sum := by decide
  have hdescent : baseEnd_2251332 < baseStart_2251332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251338 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_2251338 : Nat := 118140960795 + 2251338 * 2 ^ 59
def prefixEnd_2251338 : Nat := 4983230072969 + 3 ^ 40 * 2251338 * 2
def baseEnd_2251338 : Nat := 1156018509732017863421291

theorem tailTrace_2251338 : CollatzResearch.WordTrace tailWord_2251338 prefixEnd_2251338 1156018509732017863421291 := by
  unfold tailWord_2251338
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528260679448599691016667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54742028478529599176044445 20528260679448599691016667)
  ·
    refine ⟨30792391019172899536525001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20528260679448599691016667 30792391019172899536525001)
    ·
      refine ⟨23094293264379674652393751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30792391019172899536525001 23094293264379674652393751)
      ·
        refine ⟨34641439896569511978590627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23094293264379674652393751 34641439896569511978590627)
        ·
          refine ⟨51962159844854267967885941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34641439896569511978590627 51962159844854267967885941)
          ·
            refine ⟨4871452485455087621989307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51962159844854267967885941 4871452485455087621989307)
            ·
              refine ⟨7307178728182631432983961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4871452485455087621989307 7307178728182631432983961)
              ·
                refine ⟨5480384046136973574737971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7307178728182631432983961 5480384046136973574737971)
                ·
                  refine ⟨8220576069205460362106957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480384046136973574737971 8220576069205460362106957)
                  ·
                    refine ⟨3082716025952047635790109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8220576069205460362106957 3082716025952047635790109)
                    ·
                      refine ⟨1156018509732017863421291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082716025952047635790109 1156018509732017863421291)
                      ·
                        rfl

theorem cell23_2251338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_2251338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251338 prefixEnd_2251338 := by exact prefixLift 2251338
  have htrace : WordTrace (prefixWord ++ tailWord_2251338) baseStart_2251338 baseEnd_2251338 := by
    simpa [prefixWord, tailWord_2251338, baseEnd_2251338] using wordTrace_append hprefix tailTrace_2251338
  have hstable : (prefixWord ++ tailWord_2251338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251338).length < 2 ^ (prefixWord ++ tailWord_2251338).sum := by decide
  have hdescent : baseEnd_2251338 < baseStart_2251338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251361 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_2251361 : Nat := 118140960795 + 2251361 * 2 ^ 59
def prefixEnd_2251361 : Nat := 4983230072969 + 3 ^ 40 * 2251361 * 2
def baseEnd_2251361 : Nat := 1156030319787071273433685

theorem tailTrace_2251361 : CollatzResearch.WordTrace tailWord_2251361 prefixEnd_2251361 1156030319787071273433685 := by
  unfold tailWord_2251361
  simp only [CollatzResearch.WordTrace]
  refine ⟨82113881596711073692153937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54742587731140715794769291 82113881596711073692153937)
  ·
    refine ⟨61585411197533305269115453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82113881596711073692153937 61585411197533305269115453)
    ·
      refine ⟨23094529199074989475918295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61585411197533305269115453 23094529199074989475918295)
      ·
        refine ⟨34641793798612484213877443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23094529199074989475918295 34641793798612484213877443)
        ·
          refine ⟨51962690697918726320816165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34641793798612484213877443 51962690697918726320816165)
          ·
            refine ⟨9743004505859761185153031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51962690697918726320816165 9743004505859761185153031)
            ·
              refine ⟨14614506758789641777729547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9743004505859761185153031 14614506758789641777729547)
              ·
                refine ⟨21921760138184462666594321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14614506758789641777729547 21921760138184462666594321)
                ·
                  refine ⟨16441320103638346999945741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21921760138184462666594321 16441320103638346999945741)
                  ·
                    refine ⟨6165495038864380124979653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16441320103638346999945741 6165495038864380124979653)
                    ·
                      refine ⟨1156030319787071273433685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6165495038864380124979653 1156030319787071273433685)
                      ·
                        rfl

theorem cell23_2251361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_2251361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251361 prefixEnd_2251361 := by exact prefixLift 2251361
  have htrace : WordTrace (prefixWord ++ tailWord_2251361) baseStart_2251361 baseEnd_2251361 := by
    simpa [prefixWord, tailWord_2251361, baseEnd_2251361] using wordTrace_append hprefix tailTrace_2251361
  have hstable : (prefixWord ++ tailWord_2251361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251361).length < 2 ^ (prefixWord ++ tailWord_2251361).sum := by decide
  have hdescent : baseEnd_2251361 < baseStart_2251361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251362 : List Nat := [3, 3, 2, 3, 2, 1, 1, 8]
def baseStart_2251362 : Nat := 118140960795 + 2251362 * 2 ^ 59
def prefixEnd_2251362 : Nat := 4983230072969 + 3 ^ 40 * 2251362 * 2
def baseEnd_2251362 : Nat := 42815956787693547019303

theorem tailTrace_2251362 : CollatzResearch.WordTrace tailWord_2251362 prefixEnd_2251362 42815956787693547019303 := by
  unfold tailWord_2251362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528479517426862715735085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54742612046471633908626893 20528479517426862715735085)
  ·
    refine ⟨7698179819035073518400657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20528479517426862715735085 7698179819035073518400657)
    ·
      refine ⟨5773634864276305138800493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7698179819035073518400657 5773634864276305138800493)
      ·
        refine ⟨2165113074103614427050185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5773634864276305138800493 2165113074103614427050185)
        ·
          refine ⟨1623834805577710820287639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2165113074103614427050185 1623834805577710820287639)
          ·
            refine ⟨2435752208366566230431459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623834805577710820287639 2435752208366566230431459)
            ·
              refine ⟨3653628312549849345647189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435752208366566230431459 3653628312549849345647189)
              ·
                refine ⟨42815956787693547019303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3653628312549849345647189 42815956787693547019303)
                ·
                  rfl

theorem cell23_2251362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 8].length) (baseStart_2251362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251362 prefixEnd_2251362 := by exact prefixLift 2251362
  have htrace : WordTrace (prefixWord ++ tailWord_2251362) baseStart_2251362 baseEnd_2251362 := by
    simpa [prefixWord, tailWord_2251362, baseEnd_2251362] using wordTrace_append hprefix tailTrace_2251362
  have hstable : (prefixWord ++ tailWord_2251362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251362).length < 2 ^ (prefixWord ++ tailWord_2251362).sum := by decide
  have hdescent : baseEnd_2251362 < baseStart_2251362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251411 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 3]
def baseStart_2251411 : Nat := 118140960795 + 2251411 * 2 ^ 59
def prefixEnd_2251411 : Nat := 4983230072969 + 3 ^ 40 * 2251411 * 2
def baseEnd_2251411 : Nat := 1156055993819796077808455

theorem tailTrace_2251411 : CollatzResearch.WordTrace tailWord_2251411 prefixEnd_2251411 1156055993819796077808455 := by
  unfold tailWord_2251411
  simp only [CollatzResearch.WordTrace]
  refine ⟨82115705246529932231474087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54743803497686621487649391 82115705246529932231474087)
  ·
    refine ⟨123173557869794898347211131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82115705246529932231474087 123173557869794898347211131)
    ·
      refine ⟨184760336804692347520816697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123173557869794898347211131 184760336804692347520816697)
      ·
        refine ⟨138570252603519260640612523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184760336804692347520816697 138570252603519260640612523)
        ·
          refine ⟨207855378905278890960918785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138570252603519260640612523 207855378905278890960918785)
          ·
            refine ⟨155891534178959168220689089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207855378905278890960918785 155891534178959168220689089)
            ·
              refine ⟨116918650634219376165516817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155891534178959168220689089 116918650634219376165516817)
              ·
                refine ⟨87688987975664532124137613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116918650634219376165516817 87688987975664532124137613)
                ·
                  refine ⟨32883370490874199546551605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87688987975664532124137613 32883370490874199546551605)
                  ·
                    refine ⟨3082815983519456207489213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32883370490874199546551605 3082815983519456207489213)
                    ·
                      refine ⟨1156055993819796077808455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082815983519456207489213 1156055993819796077808455)
                      ·
                        rfl

theorem cell23_2251411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_2251411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251411 prefixEnd_2251411 := by exact prefixLift 2251411
  have htrace : WordTrace (prefixWord ++ tailWord_2251411) baseStart_2251411 baseEnd_2251411 := by
    simpa [prefixWord, tailWord_2251411, baseEnd_2251411] using wordTrace_append hprefix tailTrace_2251411
  have hstable : (prefixWord ++ tailWord_2251411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251411).length < 2 ^ (prefixWord ++ tailWord_2251411).sum := by decide
  have hdescent : baseEnd_2251411 < baseStart_2251411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251428 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_2251428 : Nat := 118140960795 + 2251428 * 2 ^ 59
def prefixEnd_2251428 : Nat := 4983230072969 + 3 ^ 40 * 2251428 * 2
def baseEnd_2251428 : Nat := 1156064722990922511295877

theorem tailTrace_2251428 : CollatzResearch.WordTrace tailWord_2251428 prefixEnd_2251428 1156064722990922511295877 := by
  unfold tailWord_2251428
  simp only [CollatzResearch.WordTrace]
  refine ⟨41058162643734172067421469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54744216858312229423228625 41058162643734172067421469)
  ·
    refine ⟨15396810991400314525283051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41058162643734172067421469 15396810991400314525283051)
    ·
      refine ⟨23095216487100471787924577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15396810991400314525283051 23095216487100471787924577)
      ·
        refine ⟨17321412365325353840943433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23095216487100471787924577 17321412365325353840943433)
        ·
          refine ⟨12991059273994015380707575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17321412365325353840943433 12991059273994015380707575)
          ·
            refine ⟨19486588910991023071061363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12991059273994015380707575 19486588910991023071061363)
            ·
              refine ⟨29229883366486534606592045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19486588910991023071061363 29229883366486534606592045)
              ·
                refine ⟨10961206262432450477472017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29229883366486534606592045 10961206262432450477472017)
                ·
                  refine ⟨8220904696824337858104013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10961206262432450477472017 8220904696824337858104013)
                  ·
                    refine ⟨3082839261309126696789005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8220904696824337858104013 3082839261309126696789005)
                    ·
                      refine ⟨1156064722990922511295877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082839261309126696789005 1156064722990922511295877)
                      ·
                        rfl

theorem cell23_2251428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_2251428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251428 prefixEnd_2251428 := by exact prefixLift 2251428
  have htrace : WordTrace (prefixWord ++ tailWord_2251428) baseStart_2251428 baseEnd_2251428 := by
    simpa [prefixWord, tailWord_2251428, baseEnd_2251428] using wordTrace_append hprefix tailTrace_2251428
  have hstable : (prefixWord ++ tailWord_2251428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251428).length < 2 ^ (prefixWord ++ tailWord_2251428).sum := by decide
  have hdescent : baseEnd_2251428 < baseStart_2251428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251469 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2251469 : Nat := 118140960795 + 2251469 * 2 ^ 59
def prefixEnd_2251469 : Nat := 4983230072969 + 3 ^ 40 * 2251469 * 2
def baseEnd_2251469 : Nat := 128453975077528538987021

theorem tailTrace_2251469 : CollatzResearch.WordTrace tailWord_2251469 prefixEnd_2251469 128453975077528538987021 := by
  unfold tailWord_2251469
  simp only [CollatzResearch.WordTrace]
  refine ⟨82117820680319808137085461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54745213786879872091390307 82117820680319808137085461)
  ·
    refine ⟨3849272844389991006425881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82117820680319808137085461 3849272844389991006425881)
    ·
      refine ⟨2886954633292493254819411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3849272844389991006425881 2886954633292493254819411)
      ·
        refine ⟨4330431949938739882229117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886954633292493254819411 4330431949938739882229117)
        ·
          refine ⟨1623911981227027455835919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4330431949938739882229117 1623911981227027455835919)
          ·
            refine ⟨2435867971840541183753879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623911981227027455835919 2435867971840541183753879)
            ·
              refine ⟨3653801957760811775630819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435867971840541183753879 3653801957760811775630819)
              ·
                refine ⟨5480702936641217663446229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653801957760811775630819 5480702936641217663446229)
                ·
                  refine ⟨128453975077528538987021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5480702936641217663446229 128453975077528538987021)
                  ·
                    rfl

theorem cell23_2251469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2251469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251469 prefixEnd_2251469 := by exact prefixLift 2251469
  have htrace : WordTrace (prefixWord ++ tailWord_2251469) baseStart_2251469 baseEnd_2251469 := by
    simpa [prefixWord, tailWord_2251469, baseEnd_2251469] using wordTrace_append hprefix tailTrace_2251469
  have hstable : (prefixWord ++ tailWord_2251469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251469).length < 2 ^ (prefixWord ++ tailWord_2251469).sum := by decide
  have hdescent : baseEnd_2251469 < baseStart_2251469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251488 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3]
def baseStart_2251488 : Nat := 118140960795 + 2251488 * 2 ^ 59
def prefixEnd_2251488 : Nat := 4983230072969 + 3 ^ 40 * 2251488 * 2
def baseEnd_2251488 : Nat := 1156095531830192276545601

theorem tailTrace_2251488 : CollatzResearch.WordTrace tailWord_2251488 prefixEnd_2251488 1156095531830192276545601 := by
  unfold tailWord_2251488
  simp only [CollatzResearch.WordTrace]
  refine ⟨41059256833625487191013559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54745675778167316254684745 41059256833625487191013559)
  ·
    refine ⟨61588885250438230786520339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41059256833625487191013559 61588885250438230786520339)
    ·
      refine ⟨92383327875657346179780509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61588885250438230786520339 92383327875657346179780509)
      ·
        refine ⟨34643747953371504817417691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92383327875657346179780509 34643747953371504817417691)
        ·
          refine ⟨51965621930057257226126537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34643747953371504817417691 51965621930057257226126537)
          ·
            refine ⟨38974216447542942919594903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51965621930057257226126537 38974216447542942919594903)
            ·
              refine ⟨58461324671314414379392355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38974216447542942919594903 58461324671314414379392355)
              ·
                refine ⟨87691987006971621569088533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58461324671314414379392355 87691987006971621569088533)
                ·
                  refine ⟨4110561890951794761051025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87691987006971621569088533 4110561890951794761051025)
                  ·
                    refine ⟨3082921418213846070788269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110561890951794761051025 3082921418213846070788269)
                    ·
                      refine ⟨1156095531830192276545601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082921418213846070788269 1156095531830192276545601)
                      ·
                        rfl

theorem cell23_2251488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_2251488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251488 prefixEnd_2251488 := by exact prefixLift 2251488
  have htrace : WordTrace (prefixWord ++ tailWord_2251488) baseStart_2251488 baseEnd_2251488 := by
    simpa [prefixWord, tailWord_2251488, baseEnd_2251488] using wordTrace_append hprefix tailTrace_2251488
  have hstable : (prefixWord ++ tailWord_2251488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251488).length < 2 ^ (prefixWord ++ tailWord_2251488).sum := by decide
  have hdescent : baseEnd_2251488 < baseStart_2251488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251505 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_2251505 : Nat := 118140960795 + 2251505 * 2 ^ 59
def prefixEnd_2251505 : Nat := 4983230072969 + 3 ^ 40 * 2251505 * 2
def baseEnd_2251505 : Nat := 1156104261001318710033023

theorem tailTrace_2251505 : CollatzResearch.WordTrace tailWord_2251505 prefixEnd_2251505 1156104261001318710033023 := by
  unfold tailWord_2251505
  simp only [CollatzResearch.WordTrace]
  refine ⟨82119133708189386285395969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54746089138792924190263979 82119133708189386285395969)
  ·
    refine ⟨61589350281142039714046977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82119133708189386285395969 61589350281142039714046977)
    ·
      refine ⟨46192012710856529785535233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61589350281142039714046977 46192012710856529785535233)
      ·
        refine ⟨34644009533142397339151425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46192012710856529785535233 34644009533142397339151425)
        ·
          refine ⟨25983007149856798004363569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34644009533142397339151425 25983007149856798004363569)
          ·
            refine ⟨19487255362392598503272677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25983007149856798004363569 19487255362392598503272677)
            ·
              refine ⟨3653860380448612219363627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19487255362392598503272677 3653860380448612219363627)
              ·
                refine ⟨5480790570672918329045441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653860380448612219363627 5480790570672918329045441)
                ·
                  refine ⟨4110592928004688746784081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5480790570672918329045441 4110592928004688746784081)
                  ·
                    refine ⟨3082944696003516560088061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110592928004688746784081 3082944696003516560088061)
                    ·
                      refine ⟨1156104261001318710033023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082944696003516560088061 1156104261001318710033023)
                      ·
                        rfl

theorem cell23_2251505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_2251505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251505 prefixEnd_2251505 := by exact prefixLift 2251505
  have htrace : WordTrace (prefixWord ++ tailWord_2251505) baseStart_2251505 baseEnd_2251505 := by
    simpa [prefixWord, tailWord_2251505, baseEnd_2251505] using wordTrace_append hprefix tailTrace_2251505
  have hstable : (prefixWord ++ tailWord_2251505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251505).length < 2 ^ (prefixWord ++ tailWord_2251505).sum := by decide
  have hdescent : baseEnd_2251505 < baseStart_2251505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251511 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_2251511 : Nat := 118140960795 + 2251511 * 2 ^ 59
def prefixEnd_2251511 : Nat := 4983230072969 + 3 ^ 40 * 2251511 * 2
def baseEnd_2251511 : Nat := 1156107341885245686557995

theorem tailTrace_2251511 : CollatzResearch.WordTrace tailWord_2251511 prefixEnd_2251511 1156107341885245686557995 := by
  unfold tailWord_2251511
  simp only [CollatzResearch.WordTrace]
  refine ⟨82119352546167649310114387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54746235030778432873409591 82119352546167649310114387)
  ·
    refine ⟨123179028819251473965171581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82119352546167649310114387 123179028819251473965171581)
    ·
      refine ⟨46192135807219302736939343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123179028819251473965171581 46192135807219302736939343)
      ·
        refine ⟨69288203710828954105409015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46192135807219302736939343 69288203710828954105409015)
        ·
          refine ⟨103932305566243431158113523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69288203710828954105409015 103932305566243431158113523)
          ·
            refine ⟨155898458349365146737170285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103932305566243431158113523 155898458349365146737170285)
            ·
              refine ⟨58461921881011930026438857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155898458349365146737170285 58461921881011930026438857)
              ·
                refine ⟨43846441410758947519829143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58461921881011930026438857 43846441410758947519829143)
                ·
                  refine ⟨65769662116138421279743715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43846441410758947519829143 65769662116138421279743715)
                  ·
                    refine ⟨98654493174207631919615573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65769662116138421279743715 98654493174207631919615573)
                    ·
                      refine ⟨1156107341885245686557995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 98654493174207631919615573 1156107341885245686557995)
                      ·
                        rfl

theorem cell23_2251511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_2251511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251511 prefixEnd_2251511 := by exact prefixLift 2251511
  have htrace : WordTrace (prefixWord ++ tailWord_2251511) baseStart_2251511 baseEnd_2251511 := by
    simpa [prefixWord, tailWord_2251511, baseEnd_2251511] using wordTrace_append hprefix tailTrace_2251511
  have hstable : (prefixWord ++ tailWord_2251511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251511).length < 2 ^ (prefixWord ++ tailWord_2251511).sum := by decide
  have hdescent : baseEnd_2251511 < baseStart_2251511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251522 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2251522 : Nat := 118140960795 + 2251522 * 2 ^ 59
def prefixEnd_2251522 : Nat := 4983230072969 + 3 ^ 40 * 2251522 * 2
def baseEnd_2251522 : Nat := 1156112990172445143520445

theorem tailTrace_2251522 : CollatzResearch.WordTrace tailWord_2251522 prefixEnd_2251522 1156112990172445143520445 := by
  unfold tailWord_2251522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20529938437281949547191205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54746502499418532125843213 20529938437281949547191205)
  ·
    refine ⟨3849363456990365540098351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20529938437281949547191205 3849363456990365540098351)
    ·
      refine ⟨5774045185485548310147527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3849363456990365540098351 5774045185485548310147527)
      ·
        refine ⟨8661067778228322465221291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5774045185485548310147527 8661067778228322465221291)
        ·
          refine ⟨12991601667342483697831937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8661067778228322465221291 12991601667342483697831937)
          ·
            refine ⟨9743701250506862773373953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12991601667342483697831937 9743701250506862773373953)
            ·
              refine ⟨7307775937880147080030465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9743701250506862773373953 7307775937880147080030465)
              ·
                refine ⟨5480831953410110310022849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7307775937880147080030465 5480831953410110310022849)
                ·
                  refine ⟨4110623965057582732517137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5480831953410110310022849 4110623965057582732517137)
                  ·
                    refine ⟨3082967973793187049387853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110623965057582732517137 3082967973793187049387853)
                    ·
                      refine ⟨1156112990172445143520445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082967973793187049387853 1156112990172445143520445)
                      ·
                        rfl

theorem cell23_2251522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2251522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251522 prefixEnd_2251522 := by exact prefixLift 2251522
  have htrace : WordTrace (prefixWord ++ tailWord_2251522) baseStart_2251522 baseEnd_2251522 := by
    simpa [prefixWord, tailWord_2251522, baseEnd_2251522] using wordTrace_append hprefix tailTrace_2251522
  have hstable : (prefixWord ++ tailWord_2251522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251522).length < 2 ^ (prefixWord ++ tailWord_2251522).sum := by decide
  have hdescent : baseEnd_2251522 < baseStart_2251522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251535 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 3]
def baseStart_2251535 : Nat := 118140960795 + 2251535 * 2 ^ 59
def prefixEnd_2251535 : Nat := 4983230072969 + 3 ^ 40 * 2251535 * 2
def baseEnd_2251535 : Nat := 1156119665420953592657885

theorem tailTrace_2251535 : CollatzResearch.WordTrace tailWord_2251535 prefixEnd_2251535 1156119665420953592657885 := by
  unfold tailWord_2251535
  simp only [CollatzResearch.WordTrace]
  refine ⟨82120227898080701408988059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54746818598720467605992039 82120227898080701408988059)
  ·
    refine ⟨123180341847121052113482089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82120227898080701408988059 123180341847121052113482089)
    ·
      refine ⟨92385256385340789085111567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123180341847121052113482089 92385256385340789085111567)
      ·
        refine ⟨138577884578011183627667351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92385256385340789085111567 138577884578011183627667351)
        ·
          refine ⟨207866826867016775441501027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138577884578011183627667351 207866826867016775441501027)
          ·
            refine ⟨311800240300525163162251541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207866826867016775441501027 311800240300525163162251541)
            ·
              refine ⟨14615636264087117023230541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 311800240300525163162251541 14615636264087117023230541)
              ·
                refine ⟨5480863599032668883711453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14615636264087117023230541 5480863599032668883711453)
                ·
                  refine ⟨2055323849637250831391795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5480863599032668883711453 2055323849637250831391795)
                  ·
                    refine ⟨3082985774455876247087693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055323849637250831391795 3082985774455876247087693)
                    ·
                      refine ⟨1156119665420953592657885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3082985774455876247087693 1156119665420953592657885)
                      ·
                        rfl

theorem cell23_2251535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 3].length) (baseStart_2251535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251535 prefixEnd_2251535 := by exact prefixLift 2251535
  have htrace : WordTrace (prefixWord ++ tailWord_2251535) baseStart_2251535 baseEnd_2251535 := by
    simpa [prefixWord, tailWord_2251535, baseEnd_2251535] using wordTrace_append hprefix tailTrace_2251535
  have hstable : (prefixWord ++ tailWord_2251535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251535).length < 2 ^ (prefixWord ++ tailWord_2251535).sum := by decide
  have hdescent : baseEnd_2251535 < baseStart_2251535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251552 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2251552 : Nat := 118140960795 + 2251552 * 2 ^ 59
def prefixEnd_2251552 : Nat := 4983230072969 + 3 ^ 40 * 2251552 * 2
def baseEnd_2251552 : Nat := 1156128394592080026145307

theorem tailTrace_2251552 : CollatzResearch.WordTrace tailWord_2251552 prefixEnd_2251552 1156128394592080026145307 := by
  unfold tailWord_2251552
  simp only [CollatzResearch.WordTrace]
  refine ⟨41060423969509556656178455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54747231959346075541571273 41060423969509556656178455)
  ·
    refine ⟨61590635954264334984267683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41060423969509556656178455 61590635954264334984267683)
    ·
      refine ⟨92385953931396502476401525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61590635954264334984267683 92385953931396502476401525)
      ·
        refine ⟨8661183181068422107162643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92385953931396502476401525 8661183181068422107162643)
        ·
          refine ⟨12991774771602633160743965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8661183181068422107162643 12991774771602633160743965)
          ·
            refine ⟨4871915539350987435278987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12991774771602633160743965 4871915539350987435278987)
            ·
              refine ⟨7307873309026481152918481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4871915539350987435278987 7307873309026481152918481)
              ·
                refine ⟨5480904981769860864688861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7307873309026481152918481 5480904981769860864688861)
                ·
                  refine ⟨2055339368163697824258323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5480904981769860864688861 2055339368163697824258323)
                  ·
                    refine ⟨3083009052245546736387485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055339368163697824258323 3083009052245546736387485)
                    ·
                      refine ⟨1156128394592080026145307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083009052245546736387485 1156128394592080026145307)
                      ·
                        rfl

theorem cell23_2251552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2251552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251552 prefixEnd_2251552 := by exact prefixLift 2251552
  have htrace : WordTrace (prefixWord ++ tailWord_2251552) baseStart_2251552 baseEnd_2251552 := by
    simpa [prefixWord, tailWord_2251552, baseEnd_2251552] using wordTrace_append hprefix tailTrace_2251552
  have hstable : (prefixWord ++ tailWord_2251552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251552).length < 2 ^ (prefixWord ++ tailWord_2251552).sum := by decide
  have hdescent : baseEnd_2251552 < baseStart_2251552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251569 : List Nat := [1, 2, 2, 3, 2, 1, 4, 3, 1, 1, 3]
def baseStart_2251569 : Nat := 118140960795 + 2251569 * 2 ^ 59
def prefixEnd_2251569 : Nat := 4983230072969 + 3 ^ 40 * 2251569 * 2
def baseEnd_2251569 : Nat := 1156137123763206459632729

theorem tailTrace_2251569 : CollatzResearch.WordTrace tailWord_2251569 prefixEnd_2251569 1156137123763206459632729 := by
  unfold tailWord_2251569
  simp only [CollatzResearch.WordTrace]
  refine ⟨82121467979957525215725761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54747645319971683477150507 82121467979957525215725761)
  ·
    refine ⟨61591100984968143911794321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82121467979957525215725761 61591100984968143911794321)
    ·
      refine ⟨46193325738726107933845741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61591100984968143911794321 46193325738726107933845741)
      ·
        refine ⟨17322497152022290475192153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46193325738726107933845741 17322497152022290475192153)
        ·
          refine ⟨12991872864016717856394115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17322497152022290475192153 12991872864016717856394115)
          ·
            refine ⟨19487809296025076784591173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12991872864016717856394115 19487809296025076784591173)
            ·
              refine ⟨3653964243004701897110845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19487809296025076784591173 3653964243004701897110845)
              ·
                refine ⟨1370236591126763211416567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3653964243004701897110845 1370236591126763211416567)
                ·
                  refine ⟨2055354886690144817124851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370236591126763211416567 2055354886690144817124851)
                  ·
                    refine ⟨3083032330035217225687277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055354886690144817124851 3083032330035217225687277)
                    ·
                      refine ⟨1156137123763206459632729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083032330035217225687277 1156137123763206459632729)
                      ·
                        rfl

theorem cell23_2251569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_2251569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251569 prefixEnd_2251569 := by exact prefixLift 2251569
  have htrace : WordTrace (prefixWord ++ tailWord_2251569) baseStart_2251569 baseEnd_2251569 := by
    simpa [prefixWord, tailWord_2251569, baseEnd_2251569] using wordTrace_append hprefix tailTrace_2251569
  have hstable : (prefixWord ++ tailWord_2251569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251569).length < 2 ^ (prefixWord ++ tailWord_2251569).sum := by decide
  have hdescent : baseEnd_2251569 < baseStart_2251569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251575 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_2251575 : Nat := 118140960795 + 2251575 * 2 ^ 59
def prefixEnd_2251575 : Nat := 4983230072969 + 3 ^ 40 * 2251575 * 2
def baseEnd_2251575 : Nat := 1156140204647133436157701

theorem tailTrace_2251575 : CollatzResearch.WordTrace tailWord_2251575 prefixEnd_2251575 1156140204647133436157701 := by
  unfold tailWord_2251575
  simp only [CollatzResearch.WordTrace]
  refine ⟨82121686817935788240444179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54747791211957192160296119 82121686817935788240444179)
  ·
    refine ⟨123182530226903682360666269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82121686817935788240444179 123182530226903682360666269)
    ·
      refine ⟨46193448835088880885249851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123182530226903682360666269 46193448835088880885249851)
      ·
        refine ⟨69290173252633321327874777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46193448835088880885249851 69290173252633321327874777)
        ·
          refine ⟨51967629939474990995906083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69290173252633321327874777 51967629939474990995906083)
          ·
            refine ⟨77951444909212486493859125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51967629939474990995906083 77951444909212486493859125)
            ·
              refine ⟨7307947960238670608799293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77951444909212486493859125 7307947960238670608799293)
              ·
                refine ⟨2740480485089501478299735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7307947960238670608799293 2740480485089501478299735)
                ·
                  refine ⟨4110720727634252217449603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740480485089501478299735 4110720727634252217449603)
                  ·
                    refine ⟨6166081091451378326174405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4110720727634252217449603 6166081091451378326174405)
                    ·
                      refine ⟨1156140204647133436157701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6166081091451378326174405 1156140204647133436157701)
                      ·
                        rfl

theorem cell23_2251575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_2251575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251575 prefixEnd_2251575 := by exact prefixLift 2251575
  have htrace : WordTrace (prefixWord ++ tailWord_2251575) baseStart_2251575 baseEnd_2251575 := by
    simpa [prefixWord, tailWord_2251575, baseEnd_2251575] using wordTrace_append hprefix tailTrace_2251575
  have hstable : (prefixWord ++ tailWord_2251575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251575).length < 2 ^ (prefixWord ++ tailWord_2251575).sum := by decide
  have hdescent : baseEnd_2251575 < baseStart_2251575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251642 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_2251642 : Nat := 118140960795 + 2251642 * 2 ^ 59
def prefixEnd_2251642 : Nat := 4983230072969 + 3 ^ 40 * 2251642 * 2
def baseEnd_2251642 : Nat := 1156174607850984674019893

theorem tailTrace_2251642 : CollatzResearch.WordTrace tailWord_2251642 prefixEnd_2251642 1156174607850984674019893 := by
  unfold tailWord_2251642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20531032627173264670783295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54749420339128705788755453 20531032627173264670783295)
  ·
    refine ⟨30796548940759897006174943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20531032627173264670783295 30796548940759897006174943)
    ·
      refine ⟨46194823411139845509262415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30796548940759897006174943 46194823411139845509262415)
      ·
        refine ⟨69292235116709768263893623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46194823411139845509262415 69292235116709768263893623)
        ·
          refine ⟨103938352675064652395840435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69292235116709768263893623 103938352675064652395840435)
          ·
            refine ⟨155907529012596978593760653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103938352675064652395840435 155907529012596978593760653)
            ·
              refine ⟨58465323379723866972660245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155907529012596978593760653 58465323379723866972660245)
              ·
                refine ⟨2740562033424556264343449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58465323379723866972660245 2740562033424556264343449)
                ·
                  refine ⟨2055421525068417198257587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2740562033424556264343449 2055421525068417198257587)
                  ·
                    refine ⟨3083132287602625797386381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055421525068417198257587 3083132287602625797386381)
                    ·
                      refine ⟨1156174607850984674019893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083132287602625797386381 1156174607850984674019893)
                      ·
                        rfl

theorem cell23_2251642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_2251642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251642 prefixEnd_2251642 := by exact prefixLift 2251642
  have htrace : WordTrace (prefixWord ++ tailWord_2251642) baseStart_2251642 baseEnd_2251642 := by
    simpa [prefixWord, tailWord_2251642, baseEnd_2251642] using wordTrace_append hprefix tailTrace_2251642
  have hstable : (prefixWord ++ tailWord_2251642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251642).length < 2 ^ (prefixWord ++ tailWord_2251642).sum := by decide
  have hdescent : baseEnd_2251642 < baseStart_2251642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251652 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_2251652 : Nat := 118140960795 + 2251652 * 2 ^ 59
def prefixEnd_2251652 : Nat := 4983230072969 + 3 ^ 40 * 2251652 * 2
def baseEnd_2251652 : Nat := 1156179742657529634894847

theorem tailTrace_2251652 : CollatzResearch.WordTrace tailWord_2251652 prefixEnd_2251652 1156179742657529634894847 := by
  unfold tailWord_2251652
  simp only [CollatzResearch.WordTrace]
  refine ⟨41062247619328415195498605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54749663492437886927331473 41062247619328415195498605)
  ·
    refine ⟨15398342857248155698311977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41062247619328415195498605 15398342857248155698311977)
    ·
      refine ⟨11548757142936116773733983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15398342857248155698311977 11548757142936116773733983)
      ·
        refine ⟨17323135714404175160600975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11548757142936116773733983 17323135714404175160600975)
        ·
          refine ⟨25984703571606262740901463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17323135714404175160600975 25984703571606262740901463)
          ·
            refine ⟨38977055357409394111352195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25984703571606262740901463 38977055357409394111352195)
            ·
              refine ⟨58465583036114091167028293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38977055357409394111352195 58465583036114091167028293)
              ·
                refine ⟨10962296819271392093817805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58465583036114091167028293 10962296819271392093817805)
                ·
                  refine ⟨4110861307226772035181677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10962296819271392093817805 4110861307226772035181677)
                  ·
                    refine ⟨1541572990210039513193129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4110861307226772035181677 1541572990210039513193129)
                    ·
                      refine ⟨1156179742657529634894847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541572990210039513193129 1156179742657529634894847)
                      ·
                        rfl

theorem cell23_2251652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_2251652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251652 prefixEnd_2251652 := by exact prefixLift 2251652
  have htrace : WordTrace (prefixWord ++ tailWord_2251652) baseStart_2251652 baseEnd_2251652 := by
    simpa [prefixWord, tailWord_2251652, baseEnd_2251652] using wordTrace_append hprefix tailTrace_2251652
  have hstable : (prefixWord ++ tailWord_2251652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251652).length < 2 ^ (prefixWord ++ tailWord_2251652).sum := by decide
  have hdescent : baseEnd_2251652 < baseStart_2251652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251659 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 2, 1, 3]
def baseStart_2251659 : Nat := 118140960795 + 2251659 * 2 ^ 59
def prefixEnd_2251659 : Nat := 4983230072969 + 3 ^ 40 * 2251659 * 2
def baseEnd_2251659 : Nat := 1156183337022111107507315

theorem tailTrace_2251659 : CollatzResearch.WordTrace tailWord_2251659 prefixEnd_2251659 1156183337022111107507315 := by
  unfold tailWord_2251659
  simp only [CollatzResearch.WordTrace]
  refine ⟨82124750549631470586502031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54749833699754313724334687 82124750549631470586502031)
  ·
    refine ⟨123187125824447205879753047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82124750549631470586502031 123187125824447205879753047)
    ·
      refine ⟨184780688736670808819629571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123187125824447205879753047 184780688736670808819629571)
      ·
        refine ⟨277171033105006213229444357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184780688736670808819629571 277171033105006213229444357)
        ·
          refine ⟨51969568707188664980520817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277171033105006213229444357 51969568707188664980520817)
          ·
            refine ⟨38977176530391498735390613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51969568707188664980520817 38977176530391498735390613)
            ·
              refine ⟨1827055149862101503221435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38977176530391498735390613 1827055149862101503221435)
              ·
                refine ⟨2740582724793152254832153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827055149862101503221435 2740582724793152254832153)
                ·
                  refine ⟨2055437043594864191124115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2740582724793152254832153 2055437043594864191124115)
                  ·
                    refine ⟨3083155565392296286686173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055437043594864191124115 3083155565392296286686173)
                    ·
                      refine ⟨1156183337022111107507315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083155565392296286686173 1156183337022111107507315)
                      ·
                        rfl

theorem cell23_2251659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 1, 3].length) (baseStart_2251659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251659 prefixEnd_2251659 := by exact prefixLift 2251659
  have htrace : WordTrace (prefixWord ++ tailWord_2251659) baseStart_2251659 baseEnd_2251659 := by
    simpa [prefixWord, tailWord_2251659, baseEnd_2251659] using wordTrace_append hprefix tailTrace_2251659
  have hstable : (prefixWord ++ tailWord_2251659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251659).length < 2 ^ (prefixWord ++ tailWord_2251659).sum := by decide
  have hdescent : baseEnd_2251659 < baseStart_2251659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251669 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_2251669 : Nat := 118140960795 + 2251669 * 2 ^ 59
def prefixEnd_2251669 : Nat := 4983230072969 + 3 ^ 40 * 2251669 * 2
def baseEnd_2251669 : Nat := 1156188471828656068382269

theorem tailTrace_2251669 : CollatzResearch.WordTrace tailWord_2251669 prefixEnd_2251669 1156188471828656068382269 := by
  unfold tailWord_2251669
  simp only [CollatzResearch.WordTrace]
  refine ⟨82125115279595242294366061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54750076853063494862910707 82125115279595242294366061)
  ·
    refine ⟨30796918229848215860387273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82125115279595242294366061 30796918229848215860387273)
    ·
      refine ⟨23097688672386161895290455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30796918229848215860387273 23097688672386161895290455)
      ·
        refine ⟨34646533008579242842935683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23097688672386161895290455 34646533008579242842935683)
        ·
          refine ⟨51969799512868864264403525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34646533008579242842935683 51969799512868864264403525)
          ·
            refine ⟨9744337408662912049575661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51969799512868864264403525 9744337408662912049575661)
            ·
              refine ⟨3654126528248592018590873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9744337408662912049575661 3654126528248592018590873)
              ·
                refine ⟨2740594896186444013943155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3654126528248592018590873 2740594896186444013943155)
                ·
                  refine ⟨4110892344279666020914733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740594896186444013943155 4110892344279666020914733)
                  ·
                    refine ⟨1541584629104874757843025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4110892344279666020914733 1541584629104874757843025)
                    ·
                      refine ⟨1156188471828656068382269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541584629104874757843025 1156188471828656068382269)
                      ·
                        rfl

theorem cell23_2251669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_2251669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251669 prefixEnd_2251669 := by exact prefixLift 2251669
  have htrace : WordTrace (prefixWord ++ tailWord_2251669) baseStart_2251669 baseEnd_2251669 := by
    simpa [prefixWord, tailWord_2251669, baseEnd_2251669] using wordTrace_append hprefix tailTrace_2251669
  have hstable : (prefixWord ++ tailWord_2251669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251669).length < 2 ^ (prefixWord ++ tailWord_2251669).sum := by decide
  have hdescent : baseEnd_2251669 < baseStart_2251669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251693 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2251693 : Nat := 118140960795 + 2251693 * 2 ^ 59
def prefixEnd_2251693 : Nat := 4983230072969 + 3 ^ 40 * 2251693 * 2
def baseEnd_2251693 : Nat := 1156200795364363974482159

theorem tailTrace_2251693 : CollatzResearch.WordTrace tailWord_2251693 prefixEnd_2251693 1156200795364363974482159 := by
  unfold tailWord_2251693
  simp only [CollatzResearch.WordTrace]
  refine ⟨82125990631508294393239733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54750660421005529595493155 82125990631508294393239733)
  ·
    refine ⟨7699311621703902599366225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82125990631508294393239733 7699311621703902599366225)
    ·
      refine ⟨5774483716277926949524669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7699311621703902599366225 5774483716277926949524669)
      ·
        refine ⟨2165431393604222606071751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5774483716277926949524669 2165431393604222606071751)
        ·
          refine ⟨3248147090406333909107627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2165431393604222606071751 3248147090406333909107627)
          ·
            refine ⟨4872220635609500863661441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248147090406333909107627 4872220635609500863661441)
            ·
              refine ⟨3654165476707125647746081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4872220635609500863661441 3654165476707125647746081)
              ·
                refine ⟨2740624107530344235809561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3654165476707125647746081 2740624107530344235809561)
                ·
                  refine ⟨2055468080647758176857171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2740624107530344235809561 2055468080647758176857171)
                  ·
                    refine ⟨3083202120971637265285757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055468080647758176857171 3083202120971637265285757)
                    ·
                      refine ⟨1156200795364363974482159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083202120971637265285757 1156200795364363974482159)
                      ·
                        rfl

theorem cell23_2251693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2251693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251693 prefixEnd_2251693 := by exact prefixLift 2251693
  have htrace : WordTrace (prefixWord ++ tailWord_2251693) baseStart_2251693 baseEnd_2251693 := by
    simpa [prefixWord, tailWord_2251693, baseEnd_2251693] using wordTrace_append hprefix tailTrace_2251693
  have hstable : (prefixWord ++ tailWord_2251693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251693).length < 2 ^ (prefixWord ++ tailWord_2251693).sum := by decide
  have hdescent : baseEnd_2251693 < baseStart_2251693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251715 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 3]
def baseStart_2251715 : Nat := 118140960795 + 2251715 * 2 ^ 59
def prefixEnd_2251715 : Nat := 4983230072969 + 3 ^ 40 * 2251715 * 2
def baseEnd_2251715 : Nat := 1156212091938762888407057

theorem tailTrace_2251715 : CollatzResearch.WordTrace tailWord_2251715 prefixEnd_2251715 1156212091938762888407057 := by
  unfold tailWord_2251715
  simp only [CollatzResearch.WordTrace]
  refine ⟨82126793037428592150540599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54751195358285728100360399 82126793037428592150540599)
  ·
    refine ⟨123190189556142888225810899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82126793037428592150540599 123190189556142888225810899)
    ·
      refine ⟨184785284334214332338716349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123190189556142888225810899 184785284334214332338716349)
      ·
        refine ⟨69294481625330374627018631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184785284334214332338716349 69294481625330374627018631)
        ·
          refine ⟨103941722437995561940527947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69294481625330374627018631 103941722437995561940527947)
          ·
            refine ⟨155912583656993342910791921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103941722437995561940527947 155912583656993342910791921)
            ·
              refine ⟨116934437742745007183093941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155912583656993342910791921 116934437742745007183093941)
              ·
                refine ⟨10962603538382344423415057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116934437742745007183093941 10962603538382344423415057)
                ·
                  refine ⟨8221952653786758317561293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10962603538382344423415057 8221952653786758317561293)
                  ·
                    refine ⟨3083232245170034369085485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8221952653786758317561293 3083232245170034369085485)
                    ·
                      refine ⟨1156212091938762888407057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083232245170034369085485 1156212091938762888407057)
                      ·
                        rfl

theorem cell23_2251715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_2251715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251715 prefixEnd_2251715 := by exact prefixLift 2251715
  have htrace : WordTrace (prefixWord ++ tailWord_2251715) baseStart_2251715 baseEnd_2251715 := by
    simpa [prefixWord, tailWord_2251715, baseEnd_2251715] using wordTrace_append hprefix tailTrace_2251715
  have hstable : (prefixWord ++ tailWord_2251715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251715).length < 2 ^ (prefixWord ++ tailWord_2251715).sum := by decide
  have hdescent : baseEnd_2251715 < baseStart_2251715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251735 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 2, 5]
def baseStart_2251735 : Nat := 118140960795 + 2251735 * 2 ^ 59
def prefixEnd_2251735 : Nat := 4983230072969 + 3 ^ 40 * 2251735 * 2
def baseEnd_2251735 : Nat := 385407453850617603385655

theorem tailTrace_2251735 : CollatzResearch.WordTrace tailWord_2251735 prefixEnd_2251735 385407453850617603385655 := by
  unfold tailWord_2251735
  simp only [CollatzResearch.WordTrace]
  refine ⟨82127522497356135566268659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54751681664904090377512439 82127522497356135566268659)
  ·
    refine ⟨123191283746034203349402989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82127522497356135566268659 123191283746034203349402989)
    ·
      refine ⟨46196731404762826256026121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123191283746034203349402989 46196731404762826256026121)
      ·
        refine ⟨34647548553572119692019591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46196731404762826256026121 34647548553572119692019591)
        ·
          refine ⟨51971322830358179538029387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34647548553572119692019591 51971322830358179538029387)
          ·
            refine ⟨77956984245537269307044081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51971322830358179538029387 77956984245537269307044081)
            ·
              refine ⟨58467738184152951980283061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77956984245537269307044081 58467738184152951980283061)
              ·
                refine ⟨5481350454764339248151537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58467738184152951980283061 5481350454764339248151537)
                ·
                  refine ⟨4111012841073254436113653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5481350454764339248151537 4111012841073254436113653)
                  ·
                    refine ⟨385407453850617603385655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4111012841073254436113653 385407453850617603385655)
                    ·
                      rfl

theorem cell23_2251735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_2251735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251735 prefixEnd_2251735 := by exact prefixLift 2251735
  have htrace : WordTrace (prefixWord ++ tailWord_2251735) baseStart_2251735 baseEnd_2251735 := by
    simpa [prefixWord, tailWord_2251735, baseEnd_2251735] using wordTrace_append hprefix tailTrace_2251735
  have hstable : (prefixWord ++ tailWord_2251735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251735).length < 2 ^ (prefixWord ++ tailWord_2251735).sum := by decide
  have hdescent : baseEnd_2251735 < baseStart_2251735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251809 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2251809 : Nat := 118140960795 + 2251809 * 2 ^ 59
def prefixEnd_2251809 : Nat := 4983230072969 + 3 ^ 40 * 2251809 * 2
def baseEnd_2251809 : Nat := 1156260359120285520631625

theorem tailTrace_2251809 : CollatzResearch.WordTrace tailWord_2251809 prefixEnd_2251809 1156260359120285520631625 := by
  unfold tailWord_2251809
  simp only [CollatzResearch.WordTrace]
  refine ⟨82130221499088046204462481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54753480999392030802974987 82130221499088046204462481)
  ·
    refine ⟨61597666124316034653346861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82130221499088046204462481 61597666124316034653346861)
    ·
      refine ⟨23099124796618512995005073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61597666124316034653346861 23099124796618512995005073)
      ·
        refine ⟨17324343597463884746253805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23099124796618512995005073 17324343597463884746253805)
        ·
          refine ⟨6496628849048956779845177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17324343597463884746253805 6496628849048956779845177)
          ·
            refine ⟨4872471636786717584883883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6496628849048956779845177 4872471636786717584883883)
            ·
              refine ⟨7308707455180076377325825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4872471636786717584883883 7308707455180076377325825)
              ·
                refine ⟨5481530591385057282994369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7308707455180076377325825 5481530591385057282994369)
                ·
                  refine ⟨4111147943538792962245777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5481530591385057282994369 4111147943538792962245777)
                  ·
                    refine ⟨3083360957654094721684333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111147943538792962245777 3083360957654094721684333)
                    ·
                      refine ⟨1156260359120285520631625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083360957654094721684333 1156260359120285520631625)
                      ·
                        rfl

theorem cell23_2251809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2251809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251809 prefixEnd_2251809 := by exact prefixLift 2251809
  have htrace : WordTrace (prefixWord ++ tailWord_2251809) baseStart_2251809 baseEnd_2251809 := by
    simpa [prefixWord, tailWord_2251809, baseEnd_2251809] using wordTrace_append hprefix tailTrace_2251809
  have hstable : (prefixWord ++ tailWord_2251809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251809).length < 2 ^ (prefixWord ++ tailWord_2251809).sum := by decide
  have hdescent : baseEnd_2251809 < baseStart_2251809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251812 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 8]
def baseStart_2251812 : Nat := 118140960795 + 2251812 * 2 ^ 59
def prefixEnd_2251812 : Nat := 4983230072969 + 3 ^ 40 * 2251812 * 2
def baseEnd_2251812 : Nat := 128473544395805445432679

theorem tailTrace_2251812 : CollatzResearch.WordTrace tailWord_2251812 prefixEnd_2251812 128473544395805445432679 := by
  unfold tailWord_2251812
  simp only [CollatzResearch.WordTrace]
  refine ⟨41065165459038588858410845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54753553945384785144547793 41065165459038588858410845)
  ·
    refine ⟨15399437047139470821904067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41065165459038588858410845 15399437047139470821904067)
    ·
      refine ⟨23099155570709206232856101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15399437047139470821904067 23099155570709206232856101)
      ·
        refine ⟨4331091669507976168660519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23099155570709206232856101 4331091669507976168660519)
        ·
          refine ⟨6496637504261964252990779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331091669507976168660519 6496637504261964252990779)
          ·
            refine ⟨9744956256392946379486169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496637504261964252990779 9744956256392946379486169)
            ·
              refine ⟨7308717192294709784614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9744956256392946379486169 7308717192294709784614627)
              ·
                refine ⟨10963075788442064676921941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7308717192294709784614627 10963075788442064676921941)
                ·
                  refine ⟨128473544395805445432679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10963075788442064676921941 128473544395805445432679)
                  ·
                    rfl

theorem cell23_2251812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_2251812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251812 prefixEnd_2251812 := by exact prefixLift 2251812
  have htrace : WordTrace (prefixWord ++ tailWord_2251812) baseStart_2251812 baseEnd_2251812 := by
    simpa [prefixWord, tailWord_2251812, baseEnd_2251812] using wordTrace_append hprefix tailTrace_2251812
  have hstable : (prefixWord ++ tailWord_2251812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251812).length < 2 ^ (prefixWord ++ tailWord_2251812).sum := by decide
  have hdescent : baseEnd_2251812 < baseStart_2251812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251873 : List Nat := [1, 2, 3, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_2251873 : Nat := 118140960795 + 2251873 * 2 ^ 59
def prefixEnd_2251873 : Nat := 4983230072969 + 3 ^ 40 * 2251873 * 2
def baseEnd_2251873 : Nat := 1156293221882173270231331

theorem tailTrace_2251873 : CollatzResearch.WordTrace tailWord_2251873 prefixEnd_2251873 1156293221882173270231331 := by
  unfold tailWord_2251873
  simp only [CollatzResearch.WordTrace]
  refine ⟨82132555770856185134792273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54755037180570790089861515 82132555770856185134792273)
  ·
    refine ⟨61599416828142138851094205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82132555770856185134792273 61599416828142138851094205)
    ·
      refine ⟨23099781310553302069160327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61599416828142138851094205 23099781310553302069160327)
      ·
        refine ⟨34649671965829953103740491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23099781310553302069160327 34649671965829953103740491)
        ·
          refine ⟨51974507948744929655610737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34649671965829953103740491 51974507948744929655610737)
          ·
            refine ⟨38980880961558697241708053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51974507948744929655610737 38980880961558697241708053)
            ·
              refine ⟨1827228795073063933205065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38980880961558697241708053 1827228795073063933205065)
              ·
                refine ⟨1370421596304797949903799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827228795073063933205065 1370421596304797949903799)
                ·
                  refine ⟨2055632394457196924855699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370421596304797949903799 2055632394457196924855699)
                  ·
                    refine ⟨3083448591685795387283549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055632394457196924855699 3083448591685795387283549)
                    ·
                      refine ⟨1156293221882173270231331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083448591685795387283549 1156293221882173270231331)
                      ·
                        rfl

theorem cell23_2251873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_2251873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251873 prefixEnd_2251873 := by exact prefixLift 2251873
  have htrace : WordTrace (prefixWord ++ tailWord_2251873) baseStart_2251873 baseEnd_2251873 := by
    simpa [prefixWord, tailWord_2251873, baseEnd_2251873] using wordTrace_append hprefix tailTrace_2251873
  have hstable : (prefixWord ++ tailWord_2251873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251873).length < 2 ^ (prefixWord ++ tailWord_2251873).sum := by decide
  have hdescent : baseEnd_2251873 < baseStart_2251873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251913 : List Nat := [1, 2, 1, 1, 4, 3, 1, 5, 1, 2, 2]
def baseStart_2251913 : Nat := 118140960795 + 2251913 * 2 ^ 59
def prefixEnd_2251913 : Nat := 4983230072969 + 3 ^ 40 * 2251913 * 2
def baseEnd_2251913 : Nat := 1156313761108353113731147

theorem tailTrace_2251913 : CollatzResearch.WordTrace tailWord_2251913 prefixEnd_2251913 1156313761108353113731147 := by
  unfold tailWord_2251913
  simp only [CollatzResearch.WordTrace]
  refine ⟨82134014690711271966248393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54756009793807514644165595 82134014690711271966248393)
  ·
    refine ⟨61600511018033453974686295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82134014690711271966248393 61600511018033453974686295)
    ·
      refine ⟨92400766527050180962029443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61600511018033453974686295 92400766527050180962029443)
      ·
        refine ⟨138601149790575271443044165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92400766527050180962029443 138601149790575271443044165)
        ·
          refine ⟨25987715585732863395570781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138601149790575271443044165 25987715585732863395570781)
          ·
            refine ⟨9745393344649823773339043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25987715585732863395570781 9745393344649823773339043)
            ·
              refine ⟨14618090016974735660008565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9745393344649823773339043 14618090016974735660008565)
              ·
                refine ⟨1370445939091381468125803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14618090016974735660008565 1370445939091381468125803)
                ·
                  refine ⟨2055668908637072202188705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370445939091381468125803 2055668908637072202188705)
                  ·
                    refine ⟨1541751681477804151641529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2055668908637072202188705 1541751681477804151641529)
                    ·
                      refine ⟨1156313761108353113731147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541751681477804151641529 1156313761108353113731147)
                      ·
                        rfl

theorem cell23_2251913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 2, 2].length) (baseStart_2251913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251913 prefixEnd_2251913 := by exact prefixLift 2251913
  have htrace : WordTrace (prefixWord ++ tailWord_2251913) baseStart_2251913 baseEnd_2251913 := by
    simpa [prefixWord, tailWord_2251913, baseEnd_2251913] using wordTrace_append hprefix tailTrace_2251913
  have hstable : (prefixWord ++ tailWord_2251913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251913).length < 2 ^ (prefixWord ++ tailWord_2251913).sum := by decide
  have hdescent : baseEnd_2251913 < baseStart_2251913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251930 : List Nat := [3, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2251930 : Nat := 118140960795 + 2251930 * 2 ^ 59
def prefixEnd_2251930 : Nat := 4983230072969 + 3 ^ 40 * 2251930 * 2
def baseEnd_2251930 : Nat := 1156322490279479547218569

theorem tailTrace_2251930 : CollatzResearch.WordTrace tailWord_2251930 prefixEnd_2251930 1156322490279479547218569 := by
  unfold tailWord_2251930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20533658682912420967404311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54756423154433122579744829 20533658682912420967404311)
  ·
    refine ⟨30800488024368631451106467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20533658682912420967404311 30800488024368631451106467)
    ·
      refine ⟨46200732036552947176659701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30800488024368631451106467 46200732036552947176659701)
      ·
        refine ⟨4331318628426838797811847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46200732036552947176659701 4331318628426838797811847)
        ·
          refine ⟨6496977942640258196717771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331318628426838797811847 6496977942640258196717771)
          ·
            refine ⟨9745466913960387295076657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496977942640258196717771 9745466913960387295076657)
            ·
              refine ⟨7309100185470290471307493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9745466913960387295076657 7309100185470290471307493)
              ·
                refine ⟨1370456284775679463370155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7309100185470290471307493 1370456284775679463370155)
                ·
                  refine ⟨2055684427163519195055233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370456284775679463370155 2055684427163519195055233)
                  ·
                    refine ⟨1541763320372639396291425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2055684427163519195055233 1541763320372639396291425)
                    ·
                      refine ⟨1156322490279479547218569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541763320372639396291425 1156322490279479547218569)
                      ·
                        rfl

theorem cell23_2251930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2251930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251930 prefixEnd_2251930 := by exact prefixLift 2251930
  have htrace : WordTrace (prefixWord ++ tailWord_2251930) baseStart_2251930 baseEnd_2251930 := by
    simpa [prefixWord, tailWord_2251930, baseEnd_2251930] using wordTrace_append hprefix tailTrace_2251930
  have hstable : (prefixWord ++ tailWord_2251930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251930).length < 2 ^ (prefixWord ++ tailWord_2251930).sum := by decide
  have hdescent : baseEnd_2251930 < baseStart_2251930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251939 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 5, 3, 2]
def baseStart_2251939 : Nat := 118140960795 + 2251939 * 2 ^ 59
def prefixEnd_2251939 : Nat := 4983230072969 + 3 ^ 40 * 2251939 * 2
def baseEnd_2251939 : Nat := 1156327111605370012006027

theorem tailTrace_2251939 : CollatzResearch.WordTrace tailWord_2251939 prefixEnd_2251939 1156327111605370012006027 := by
  unfold tailWord_2251939
  simp only [CollatzResearch.WordTrace]
  refine ⟨82134962988617078406694871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54756641992411385604463247 82134962988617078406694871)
  ·
    refine ⟨123202444482925617610042307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82134962988617078406694871 123202444482925617610042307)
    ·
      refine ⟨184803666724388426415063461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123202444482925617610042307 184803666724388426415063461)
      ·
        refine ⟨34650687510822829952824399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184803666724388426415063461 34650687510822829952824399)
        ·
          refine ⟨51976031266234244929236599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34650687510822829952824399 51976031266234244929236599)
          ·
            refine ⟨77964046899351367393854899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51976031266234244929236599 77964046899351367393854899)
            ·
              refine ⟨116946070349027051090782349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77964046899351367393854899 116946070349027051090782349)
              ·
                refine ⟨43854776380885144159043381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116946070349027051090782349 43854776380885144159043381)
                ·
                  refine ⟨4111385285707982264910317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43854776380885144159043381 4111385285707982264910317)
                  ·
                    refine ⟨1541769482140493349341369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4111385285707982264910317 1541769482140493349341369)
                    ·
                      refine ⟨1156327111605370012006027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541769482140493349341369 1156327111605370012006027)
                      ·
                        rfl

theorem cell23_2251939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_2251939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251939 prefixEnd_2251939 := by exact prefixLift 2251939
  have htrace : WordTrace (prefixWord ++ tailWord_2251939) baseStart_2251939 baseEnd_2251939 := by
    simpa [prefixWord, tailWord_2251939, baseEnd_2251939] using wordTrace_append hprefix tailTrace_2251939
  have hstable : (prefixWord ++ tailWord_2251939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251939).length < 2 ^ (prefixWord ++ tailWord_2251939).sum := by decide
  have hdescent : baseEnd_2251939 < baseStart_2251939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251981 : List Nat := [1, 6, 2, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_2251981 : Nat := 118140960795 + 2251981 * 2 ^ 59
def prefixEnd_2251981 : Nat := 4983230072969 + 3 ^ 40 * 2251981 * 2
def baseEnd_2251981 : Nat := 1156348677792858847680835

theorem tailTrace_2251981 : CollatzResearch.WordTrace tailWord_2251981 prefixEnd_2251981 1156348677792858847680835 := by
  unfold tailWord_2251981
  simp only [CollatzResearch.WordTrace]
  refine ⟨82136494854464919579723797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54757663236309946386482531 82136494854464919579723797)
  ·
    refine ⟨3850148196303043105299553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82136494854464919579723797 3850148196303043105299553)
    ·
      refine ⟨2887611147227282328974665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3850148196303043105299553 2887611147227282328974665)
      ·
        refine ⟨2165708360420461746730999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2887611147227282328974665 2165708360420461746730999)
        ·
          refine ⟨3248562540630692620096499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2165708360420461746730999 3248562540630692620096499)
          ·
            refine ⟨4872843810946038930144749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248562540630692620096499 4872843810946038930144749)
            ·
              refine ⟨1827316429104764598804281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4872843810946038930144749 1827316429104764598804281)
              ·
                refine ⟨1370487321828573449103211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827316429104764598804281 1370487321828573449103211)
                ·
                  refine ⟨2055730982742860173654817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370487321828573449103211 2055730982742860173654817)
                  ·
                    refine ⟨1541798237057145130241113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2055730982742860173654817 1541798237057145130241113)
                    ·
                      refine ⟨1156348677792858847680835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541798237057145130241113 1156348677792858847680835)
                      ·
                        rfl

theorem cell23_2251981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_2251981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251981 prefixEnd_2251981 := by exact prefixLift 2251981
  have htrace : WordTrace (prefixWord ++ tailWord_2251981) baseStart_2251981 baseEnd_2251981 := by
    simpa [prefixWord, tailWord_2251981, baseEnd_2251981] using wordTrace_append hprefix tailTrace_2251981
  have hstable : (prefixWord ++ tailWord_2251981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251981).length < 2 ^ (prefixWord ++ tailWord_2251981).sum := by decide
  have hdescent : baseEnd_2251981 < baseStart_2251981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2251997 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2251997 : Nat := 118140960795 + 2251997 * 2 ^ 59
def prefixEnd_2251997 : Nat := 4983230072969 + 3 ^ 40 * 2251997 * 2
def baseEnd_2251997 : Nat := 1156356893483330785080761

theorem tailTrace_2251997 : CollatzResearch.WordTrace tailWord_2251997 prefixEnd_2251997 1156356893483330785080761 := by
  unfold tailWord_2251997
  simp only [CollatzResearch.WordTrace]
  refine ⟨82137078422406954312306245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54758052281604636208204163 82137078422406954312306245)
  ·
    refine ⟨15400702204201303933557421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82137078422406954312306245 15400702204201303933557421)
    ·
      refine ⟨5775263326575488975084033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15400702204201303933557421 5775263326575488975084033)
      ·
        refine ⟨4331447494931616731313025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5775263326575488975084033 4331447494931616731313025)
        ·
          refine ⟨3248585621198712548484769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4331447494931616731313025 3248585621198712548484769)
          ·
            refine ⟨2436439215899034411363577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3248585621198712548484769 2436439215899034411363577)
            ·
              refine ⟨1827329411924275808522683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436439215899034411363577 1827329411924275808522683)
              ·
                refine ⟨2740994117886413712784025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827329411924275808522683 2740994117886413712784025)
                ·
                  refine ⟨2055745588414810284588019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2740994117886413712784025 2055745588414810284588019)
                  ·
                    refine ⟨3083618382622215426882029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055745588414810284588019 3083618382622215426882029)
                    ·
                      refine ⟨1156356893483330785080761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3083618382622215426882029 1156356893483330785080761)
                      ·
                        rfl

theorem cell23_2251997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2251997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2251997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2251997 prefixEnd_2251997 := by exact prefixLift 2251997
  have htrace : WordTrace (prefixWord ++ tailWord_2251997) baseStart_2251997 baseEnd_2251997 := by
    simpa [prefixWord, tailWord_2251997, baseEnd_2251997] using wordTrace_append hprefix tailTrace_2251997
  have hstable : (prefixWord ++ tailWord_2251997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2251997).length < 2 ^ (prefixWord ++ tailWord_2251997).sum := by decide
  have hdescent : baseEnd_2251997 < baseStart_2251997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2251997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252007 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2252007 : Nat := 118140960795 + 2252007 * 2 ^ 59
def prefixEnd_2252007 : Nat := 4983230072969 + 3 ^ 40 * 2252007 * 2
def baseEnd_2252007 : Nat := 1156362028289875745955715

theorem tailTrace_2252007 : CollatzResearch.WordTrace tailWord_2252007 prefixEnd_2252007 1156362028289875745955715 := by
  unfold tailWord_2252007
  simp only [CollatzResearch.WordTrace]
  refine ⟨82137443152370726020170275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54758295434913817346780183 82137443152370726020170275)
  ·
    refine ⟨123206164728556089030255413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82137443152370726020170275 123206164728556089030255413)
    ·
      refine ⟨11550577943302133346586445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123206164728556089030255413 11550577943302133346586445)
      ·
        refine ⟨4331466728738300004969917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11550577943302133346586445 4331466728738300004969917)
        ·
          refine ⟨1624300023276862501863719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4331466728738300004969917 1624300023276862501863719)
          ·
            refine ⟨2436450034915293752795579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624300023276862501863719 2436450034915293752795579)
            ·
              refine ⟨3654675052372940629193369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436450034915293752795579 3654675052372940629193369)
              ·
                refine ⟨2741006289279705471895027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3654675052372940629193369 2741006289279705471895027)
                ·
                  refine ⟨4111509433919558207842541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741006289279705471895027 4111509433919558207842541)
                  ·
                    refine ⟨1541816037719834327940953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4111509433919558207842541 1541816037719834327940953)
                    ·
                      refine ⟨1156362028289875745955715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541816037719834327940953 1156362028289875745955715)
                      ·
                        rfl

theorem cell23_2252007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2252007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252007 prefixEnd_2252007 := by exact prefixLift 2252007
  have htrace : WordTrace (prefixWord ++ tailWord_2252007) baseStart_2252007 baseEnd_2252007 := by
    simpa [prefixWord, tailWord_2252007, baseEnd_2252007] using wordTrace_append hprefix tailTrace_2252007
  have hstable : (prefixWord ++ tailWord_2252007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252007).length < 2 ^ (prefixWord ++ tailWord_2252007).sum := by decide
  have hdescent : baseEnd_2252007 < baseStart_2252007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252043 : List Nat := [1, 1, 1, 1, 5, 5, 2, 2, 5]
def baseStart_2252043 : Nat := 118140960795 + 2252043 * 2 ^ 59
def prefixEnd_2252043 : Nat := 4983230072969 + 3 ^ 40 * 2252043 * 2
def baseEnd_2252043 : Nat := 128486723732604178345061

theorem tailTrace_2252043 : CollatzResearch.WordTrace tailWord_2252043 prefixEnd_2252043 128486723732604178345061 := by
  unfold tailWord_2252043
  simp only [CollatzResearch.WordTrace]
  refine ⟨82138756180240304168480783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54759170786826869445653855 82138756180240304168480783)
  ·
    refine ⟨123208134270360456252721175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82138756180240304168480783 123208134270360456252721175)
    ·
      refine ⟨184812201405540684379081763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123208134270360456252721175 184812201405540684379081763)
      ·
        refine ⟨277218302108311026568622645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184812201405540684379081763 277218302108311026568622645)
        ·
          refine ⟨25989215822654158740808373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 277218302108311026568622645 25989215822654158740808373)
          ·
            refine ⟨2436488983373827381950785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25989215822654158740808373 2436488983373827381950785)
            ·
              refine ⟨1827366737530370536463089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436488983373827381950785 1827366737530370536463089)
              ·
                refine ⟨1370525053147777902347317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827366737530370536463089 1370525053147777902347317)
                ·
                  refine ⟨128486723732604178345061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1370525053147777902347317 128486723732604178345061)
                  ·
                    rfl

theorem cell23_2252043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 5].length) (baseStart_2252043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252043 prefixEnd_2252043 := by exact prefixLift 2252043
  have htrace : WordTrace (prefixWord ++ tailWord_2252043) baseStart_2252043 baseEnd_2252043 := by
    simpa [prefixWord, tailWord_2252043, baseEnd_2252043] using wordTrace_append hprefix tailTrace_2252043
  have hstable : (prefixWord ++ tailWord_2252043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252043).length < 2 ^ (prefixWord ++ tailWord_2252043).sum := by decide
  have hdescent : baseEnd_2252043 < baseStart_2252043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252046 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_2252046 : Nat := 118140960795 + 2252046 * 2 ^ 59
def prefixEnd_2252046 : Nat := 4983230072969 + 3 ^ 40 * 2252046 * 2
def baseEnd_2252046 : Nat := 1156382054035401093368035

theorem tailTrace_2252046 : CollatzResearch.WordTrace tailWord_2252046 prefixEnd_2252046 1156382054035401093368035 := by
  unfold tailWord_2252046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267358199903679460104999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54759243732819623787226661 10267358199903679460104999)
  ·
    refine ⟨15401037299855519190157499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10267358199903679460104999 15401037299855519190157499)
    ·
      refine ⟨23101555949783278785236249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15401037299855519190157499 23101555949783278785236249)
      ·
        refine ⟨17326166962337459088927187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23101555949783278785236249 17326166962337459088927187)
        ·
          refine ⟨25989250443506188633390781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17326166962337459088927187 25989250443506188633390781)
          ·
            refine ⟨9745968916314820737521543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25989250443506188633390781 9745968916314820737521543)
            ·
              refine ⟨14618953374472231106282315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9745968916314820737521543 14618953374472231106282315)
              ·
                refine ⟨21928430061708346659423473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14618953374472231106282315 21928430061708346659423473)
                ·
                  refine ⟨16446322546281259994567605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21928430061708346659423473 16446322546281259994567605)
                  ·
                    refine ⟨1541842738713868124490713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16446322546281259994567605 1541842738713868124490713)
                    ·
                      refine ⟨1156382054035401093368035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541842738713868124490713 1156382054035401093368035)
                      ·
                        rfl

theorem cell23_2252046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_2252046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252046 prefixEnd_2252046 := by exact prefixLift 2252046
  have htrace : WordTrace (prefixWord ++ tailWord_2252046) baseStart_2252046 baseEnd_2252046 := by
    simpa [prefixWord, tailWord_2252046, baseEnd_2252046] using wordTrace_append hprefix tailTrace_2252046
  have hstable : (prefixWord ++ tailWord_2252046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252046).length < 2 ^ (prefixWord ++ tailWord_2252046).sum := by decide
  have hdescent : baseEnd_2252046 < baseStart_2252046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252103 : List Nat := [1, 1, 4, 1, 2, 3, 2, 4, 1, 4]
def baseStart_2252103 : Nat := 118140960795 + 2252103 * 2 ^ 59
def prefixEnd_2252103 : Nat := 4983230072969 + 3 ^ 40 * 2252103 * 2
def baseEnd_2252103 : Nat := 385470440810902456785091

theorem tailTrace_2252103 : CollatzResearch.WordTrace tailWord_2252103 prefixEnd_2252103 385470440810902456785091 := by
  unfold tailWord_2252103
  simp only [CollatzResearch.WordTrace]
  refine ⟨82140944560022934415664963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54760629706681956277109975 82140944560022934415664963)
  ·
    refine ⟨123211416840034401623497445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82140944560022934415664963 123211416840034401623497445)
    ·
      refine ⟨23102140657506450304405771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123211416840034401623497445 23102140657506450304405771)
      ·
        refine ⟨34653210986259675456608657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23102140657506450304405771 34653210986259675456608657)
        ·
          refine ⟨25989908239694756592456493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34653210986259675456608657 25989908239694756592456493)
          ·
            refine ⟨9746215589885533722171185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25989908239694756592456493 9746215589885533722171185)
            ·
              refine ⟨7309661692414150291628389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9746215589885533722171185 7309661692414150291628389)
              ·
                refine ⟨1370561567327653179680323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7309661692414150291628389 1370561567327653179680323)
                ·
                  refine ⟨2055842350991479769520485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370561567327653179680323 2055842350991479769520485)
                  ·
                    refine ⟨385470440810902456785091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2055842350991479769520485 385470440810902456785091)
                    ·
                      rfl

theorem cell23_2252103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_2252103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252103 prefixEnd_2252103 := by exact prefixLift 2252103
  have htrace : WordTrace (prefixWord ++ tailWord_2252103) baseStart_2252103 baseEnd_2252103 := by
    simpa [prefixWord, tailWord_2252103, baseEnd_2252103] using wordTrace_append hprefix tailTrace_2252103
  have hstable : (prefixWord ++ tailWord_2252103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252103).length < 2 ^ (prefixWord ++ tailWord_2252103).sum := by decide
  have hdescent : baseEnd_2252103 < baseStart_2252103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252129 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2252129 : Nat := 118140960795 + 2252129 * 2 ^ 59
def prefixEnd_2252129 : Nat := 4983230072969 + 3 ^ 40 * 2252129 * 2
def baseEnd_2252129 : Nat := 385474890976574756210051

theorem tailTrace_2252129 : CollatzResearch.WordTrace tailWord_2252129 prefixEnd_2252129 385474890976574756210051 := by
  unfold tailWord_2252129
  simp only [CollatzResearch.WordTrace]
  refine ⟨82141892857928740856111441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54761261905285827237407627 82141892857928740856111441)
  ·
    refine ⟨61606419643446555642083581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82141892857928740856111441 61606419643446555642083581)
    ·
      refine ⟨23102407366292458365781343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61606419643446555642083581 23102407366292458365781343)
      ·
        refine ⟨34653611049438687548672015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23102407366292458365781343 34653611049438687548672015)
        ·
          refine ⟨51980416574158031323008023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34653611049438687548672015 51980416574158031323008023)
          ·
            refine ⟨77970624861237046984512035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51980416574158031323008023 77970624861237046984512035)
            ·
              refine ⟨116955937291855570476768053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77970624861237046984512035 116955937291855570476768053)
              ·
                refine ⟨10964619121111459732197005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116955937291855570476768053 10964619121111459732197005)
                ·
                  refine ⟨4111732170416797399573877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10964619121111459732197005 4111732170416797399573877)
                  ·
                    refine ⟨385474890976574756210051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4111732170416797399573877 385474890976574756210051)
                    ·
                      rfl

theorem cell23_2252129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2252129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252129 prefixEnd_2252129 := by exact prefixLift 2252129
  have htrace : WordTrace (prefixWord ++ tailWord_2252129) baseStart_2252129 baseEnd_2252129 := by
    simpa [prefixWord, tailWord_2252129, baseEnd_2252129] using wordTrace_append hprefix tailTrace_2252129
  have hstable : (prefixWord ++ tailWord_2252129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252129).length < 2 ^ (prefixWord ++ tailWord_2252129).sum := by decide
  have hdescent : baseEnd_2252129 < baseStart_2252129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252146 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_2252146 : Nat := 118140960795 + 2252146 * 2 ^ 59
def prefixEnd_2252146 : Nat := 4983230072969 + 3 ^ 40 * 2252146 * 2
def baseEnd_2252146 : Nat := 385477800700283567372525

theorem tailTrace_2252146 : CollatzResearch.WordTrace tailWord_2252146 prefixEnd_2252146 385477800700283567372525 := by
  unfold tailWord_2252146
  simp only [CollatzResearch.WordTrace]
  refine ⟨20535628224716788189870073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54761675265911435172986861 20535628224716788189870073)
  ·
    refine ⟨15401721168537591142402555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20535628224716788189870073 15401721168537591142402555)
    ·
      refine ⟨23102581752806386713603833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15401721168537591142402555 23102581752806386713603833)
      ·
        refine ⟨17326936314604790035202875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23102581752806386713603833 17326936314604790035202875)
        ·
          refine ⟨25990404471907185052804313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17326936314604790035202875 25990404471907185052804313)
          ·
            refine ⟨19492803353930388789603235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25990404471907185052804313 19492803353930388789603235)
            ·
              refine ⟨29239205030895583184404853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19492803353930388789603235 29239205030895583184404853)
              ·
                refine ⟨2741175471646460923537955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29239205030895583184404853 2741175471646460923537955)
                ·
                  refine ⟨4111763207469691385306933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741175471646460923537955 4111763207469691385306933)
                  ·
                    refine ⟨385477800700283567372525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4111763207469691385306933 385477800700283567372525)
                    ·
                      rfl

theorem cell23_2252146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_2252146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252146 prefixEnd_2252146 := by exact prefixLift 2252146
  have htrace : WordTrace (prefixWord ++ tailWord_2252146) baseStart_2252146 baseEnd_2252146 := by
    simpa [prefixWord, tailWord_2252146, baseEnd_2252146] using wordTrace_append hprefix tailTrace_2252146
  have hstable : (prefixWord ++ tailWord_2252146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252146).length < 2 ^ (prefixWord ++ tailWord_2252146).sum := by decide
  have hdescent : baseEnd_2252146 < baseStart_2252146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252179 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4]
def baseStart_2252179 : Nat := 118140960795 + 2252179 * 2 ^ 59
def prefixEnd_2252179 : Nat := 4983230072969 + 3 ^ 40 * 2252179 * 2
def baseEnd_2252179 : Nat := 1156450346962449073004923

theorem tailTrace_2252179 : CollatzResearch.WordTrace tailWord_2252179 prefixEnd_2252179 1156450346962449073004923 := by
  unfold tailWord_2252179
  simp only [CollatzResearch.WordTrace]
  refine ⟨82143716507747599395431591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54762477671831732930287727 82143716507747599395431591)
  ·
    refine ⟨123215574761621399093147387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82143716507747599395431591 123215574761621399093147387)
    ·
      refine ⟨184823362142432098639721081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123215574761621399093147387 184823362142432098639721081)
      ·
        refine ⟨138617521606824073979790811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184823362142432098639721081 138617521606824073979790811)
        ·
          refine ⟨207926282410236110969686217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138617521606824073979790811 207926282410236110969686217)
          ·
            refine ⟨155944711807677083227264663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207926282410236110969686217 155944711807677083227264663)
            ·
              refine ⟨233917067711515624840896995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155944711807677083227264663 233917067711515624840896995)
              ·
                refine ⟨350875601567273437261345493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233917067711515624840896995 350875601567273437261345493)
                ·
                  refine ⟨8223646911732971185812785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 350875601567273437261345493 8223646911732971185812785)
                  ·
                    refine ⟨6167735183799728389359589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8223646911732971185812785 6167735183799728389359589)
                    ·
                      refine ⟨1156450346962449073004923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6167735183799728389359589 1156450346962449073004923)
                      ·
                        rfl

theorem cell23_2252179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_2252179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252179 prefixEnd_2252179 := by exact prefixLift 2252179
  have htrace : WordTrace (prefixWord ++ tailWord_2252179) baseStart_2252179 baseEnd_2252179 := by
    simpa [prefixWord, tailWord_2252179, baseEnd_2252179] using wordTrace_append hprefix tailTrace_2252179
  have hstable : (prefixWord ++ tailWord_2252179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252179).length < 2 ^ (prefixWord ++ tailWord_2252179).sum := by decide
  have hdescent : baseEnd_2252179 < baseStart_2252179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252180 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2252180 : Nat := 118140960795 + 2252180 * 2 ^ 59
def prefixEnd_2252180 : Nat := 4983230072969 + 3 ^ 40 * 2252180 * 2
def baseEnd_2252180 : Nat := 385483620147701189697473

theorem tailTrace_2252180 : CollatzResearch.WordTrace tailWord_2252180 prefixEnd_2252180 385483620147701189697473 := by
  unfold tailWord_2252180
  simp only [CollatzResearch.WordTrace]
  refine ⟨41071876490371988283108997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54762501987162651044145329 41071876490371988283108997)
  ·
    refine ⟨7700976841944747803082937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41071876490371988283108997 7700976841944747803082937)
    ·
      refine ⟨5775732631458560852312203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7700976841944747803082937 5775732631458560852312203)
      ·
        refine ⟨8663598947187841278468305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5775732631458560852312203 8663598947187841278468305)
        ·
          refine ⟨6497699210390880958851229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8663598947187841278468305 6497699210390880958851229)
          ·
            refine ⟨2436637203896580359569211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6497699210390880958851229 2436637203896580359569211)
            ·
              refine ⟨3654955805844870539353817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436637203896580359569211 3654955805844870539353817)
              ·
                refine ⟨2741216854383652904515363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3654955805844870539353817 2741216854383652904515363)
                ·
                  refine ⟨4111825281575479356773045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741216854383652904515363 4111825281575479356773045)
                  ·
                    refine ⟨385483620147701189697473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4111825281575479356773045 385483620147701189697473)
                    ·
                      rfl

theorem cell23_2252180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2252180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252180 prefixEnd_2252180 := by exact prefixLift 2252180
  have htrace : WordTrace (prefixWord ++ tailWord_2252180) baseStart_2252180 baseEnd_2252180 := by
    simpa [prefixWord, tailWord_2252180, baseEnd_2252180] using wordTrace_append hprefix tailTrace_2252180
  have hstable : (prefixWord ++ tailWord_2252180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252180).length < 2 ^ (prefixWord ++ tailWord_2252180).sum := by decide
  have hdescent : baseEnd_2252180 < baseStart_2252180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252183 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 5, 2, 2]
def baseStart_2252183 : Nat := 118140960795 + 2252183 * 2 ^ 59
def prefixEnd_2252183 : Nat := 4983230072969 + 3 ^ 40 * 2252183 * 2
def baseEnd_2252183 : Nat := 1156452400885067057354905

theorem tailTrace_2252183 : CollatzResearch.WordTrace tailWord_2252183 prefixEnd_2252183 1156452400885067057354905 := by
  unfold tailWord_2252183
  simp only [CollatzResearch.WordTrace]
  refine ⟨82143862399733108078577203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54762574933155405385718135 82143862399733108078577203)
  ·
    refine ⟨123215793599599662117865805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82143862399733108078577203 123215793599599662117865805)
    ·
      refine ⟨46205922599849873294199677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123215793599599662117865805 46205922599849873294199677)
      ·
        refine ⟨17327220974943702485324879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46205922599849873294199677 17327220974943702485324879)
        ·
          refine ⟨25990831462415553727987319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17327220974943702485324879 25990831462415553727987319)
          ·
            refine ⟨38986247193623330591980979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25990831462415553727987319 38986247193623330591980979)
            ·
              refine ⟨58479370790434995887971469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38986247193623330591980979 58479370790434995887971469)
              ·
                refine ⟨21929764046413123457989301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58479370790434995887971469 21929764046413123457989301)
                ·
                  refine ⟨2055915379351230324186497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21929764046413123457989301 2055915379351230324186497)
                  ·
                    refine ⟨1541936534513422743139873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2055915379351230324186497 1541936534513422743139873)
                    ·
                      refine ⟨1156452400885067057354905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1541936534513422743139873 1156452400885067057354905)
                      ·
                        rfl

theorem cell23_2252183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_2252183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252183 prefixEnd_2252183 := by exact prefixLift 2252183
  have htrace : WordTrace (prefixWord ++ tailWord_2252183) baseStart_2252183 baseEnd_2252183 := by
    simpa [prefixWord, tailWord_2252183, baseEnd_2252183] using wordTrace_append hprefix tailTrace_2252183
  have hstable : (prefixWord ++ tailWord_2252183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252183).length < 2 ^ (prefixWord ++ tailWord_2252183).sum := by decide
  have hdescent : baseEnd_2252183 < baseStart_2252183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252296 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 7]
def baseStart_2252296 : Nat := 118140960795 + 2252296 * 2 ^ 59
def prefixEnd_2252296 : Nat := 4983230072969 + 3 ^ 40 * 2252296 * 2
def baseEnd_2252296 : Nat := 128501158244336123915765

theorem tailTrace_2252296 : CollatzResearch.WordTrace tailWord_2252296 prefixEnd_2252296 128501158244336123915765 := by
  unfold tailWord_2252296
  simp only [CollatzResearch.WordTrace]
  refine ⟨41073991924161864188720371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54765322565549152251627161 41073991924161864188720371)
  ·
    refine ⟨61610987886242796283080557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41073991924161864188720371 61610987886242796283080557)
    ·
      refine ⟨23104120457341048606155209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61610987886242796283080557 23104120457341048606155209)
      ·
        refine ⟨17328090343005786454616407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23104120457341048606155209 17328090343005786454616407)
        ·
          refine ⟨25992135514508679681924611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17328090343005786454616407 25992135514508679681924611)
          ·
            refine ⟨38988203271763019522886917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25992135514508679681924611 38988203271763019522886917)
            ·
              refine ⟨7310288113455566160541297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38988203271763019522886917 7310288113455566160541297)
              ·
                refine ⟨5482716085091674620405973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7310288113455566160541297 5482716085091674620405973)
                ·
                  refine ⟨128501158244336123915765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5482716085091674620405973 128501158244336123915765)
                  ·
                    rfl

theorem cell23_2252296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 7].length) (baseStart_2252296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252296 prefixEnd_2252296 := by exact prefixLift 2252296
  have htrace : WordTrace (prefixWord ++ tailWord_2252296) baseStart_2252296 baseEnd_2252296 := by
    simpa [prefixWord, tailWord_2252296, baseEnd_2252296] using wordTrace_append hprefix tailTrace_2252296
  have hstable : (prefixWord ++ tailWord_2252296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252296).length < 2 ^ (prefixWord ++ tailWord_2252296).sum := by decide
  have hdescent : baseEnd_2252296 < baseStart_2252296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252363 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 4, 4, 2]
def baseStart_2252363 : Nat := 118140960795 + 2252363 * 2 ^ 59
def prefixEnd_2252363 : Nat := 4983230072969 + 3 ^ 40 * 2252363 * 2
def baseEnd_2252363 : Nat := 1156544827402876353104077

theorem tailTrace_2252363 : CollatzResearch.WordTrace tailWord_2252363 prefixEnd_2252363 1156544827402876353104077 := by
  unfold tailWord_2252363
  simp only [CollatzResearch.WordTrace]
  refine ⟨82150427539080998820129743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54766951692720665880086495 82150427539080998820129743)
  ·
    refine ⟨123225641308621498230194615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82150427539080998820129743 123225641308621498230194615)
    ·
      refine ⟨184838461962932247345291923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123225641308621498230194615 184838461962932247345291923)
      ·
        refine ⟨277257692944398371017937885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184838461962932247345291923 277257692944398371017937885)
        ·
          refine ⟨103971634854149389131726707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277257692944398371017937885 103971634854149389131726707)
          ·
            refine ⟨155957452281224083697590061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103971634854149389131726707 155957452281224083697590061)
            ·
              refine ⟨58484044605459031386596273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155957452281224083697590061 58484044605459031386596273)
              ·
                refine ⟨43863033454094273539947205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58484044605459031386596273 43863033454094273539947205)
                ·
                  refine ⟨8224318772642676288740101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43863033454094273539947205 8224318772642676288740101)
                  ·
                    refine ⟨1542059769870501804138769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8224318772642676288740101 1542059769870501804138769)
                    ·
                      refine ⟨1156544827402876353104077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542059769870501804138769 1156544827402876353104077)
                      ·
                        rfl

theorem cell23_2252363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4, 2].length) (baseStart_2252363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252363 prefixEnd_2252363 := by exact prefixLift 2252363
  have htrace : WordTrace (prefixWord ++ tailWord_2252363) baseStart_2252363 baseEnd_2252363 := by
    simpa [prefixWord, tailWord_2252363, baseEnd_2252363] using wordTrace_append hprefix tailTrace_2252363
  have hstable : (prefixWord ++ tailWord_2252363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252363).length < 2 ^ (prefixWord ++ tailWord_2252363).sum := by decide
  have hdescent : baseEnd_2252363 < baseStart_2252363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252376 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2252376 : Nat := 118140960795 + 2252376 * 2 ^ 59
def prefixEnd_2252376 : Nat := 4983230072969 + 3 ^ 40 * 2252376 * 2
def baseEnd_2252376 : Nat := 1156551502651384802241517

theorem tailTrace_2252376 : CollatzResearch.WordTrace tailWord_2252376 prefixEnd_2252376 1156551502651384802241517 := by
  unfold tailWord_2252376
  simp only [CollatzResearch.WordTrace]
  refine ⟨41075450844016951020176491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54767267792022601360235321 41075450844016951020176491)
  ·
    refine ⟨61613176266025426530264737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41075450844016951020176491 61613176266025426530264737)
    ·
      refine ⟨46209882199519069897698553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61613176266025426530264737 46209882199519069897698553)
      ·
        refine ⟨34657411649639302423273915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46209882199519069897698553 34657411649639302423273915)
        ·
          refine ⟨51986117474458953634910873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34657411649639302423273915 51986117474458953634910873)
          ·
            refine ⟨38989588105844215226183155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51986117474458953634910873 38989588105844215226183155)
            ·
              refine ⟨58484382158766322839274733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38989588105844215226183155 58484382158766322839274733)
              ·
                refine ⟨21931643309537371064728025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58484382158766322839274733 21931643309537371064728025)
                ·
                  refine ⟨16448732482153028298546019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21931643309537371064728025 16448732482153028298546019)
                  ·
                    refine ⟨24673098723229542447819029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16448732482153028298546019 24673098723229542447819029)
                    ·
                      refine ⟨1156551502651384802241517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24673098723229542447819029 1156551502651384802241517)
                      ·
                        rfl

theorem cell23_2252376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2252376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252376 prefixEnd_2252376 := by exact prefixLift 2252376
  have htrace : WordTrace (prefixWord ++ tailWord_2252376) baseStart_2252376 baseEnd_2252376 := by
    simpa [prefixWord, tailWord_2252376, baseEnd_2252376] using wordTrace_append hprefix tailTrace_2252376
  have hstable : (prefixWord ++ tailWord_2252376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252376).length < 2 ^ (prefixWord ++ tailWord_2252376).sum := by decide
  have hdescent : baseEnd_2252376 < baseStart_2252376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252380 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2252380 : Nat := 118140960795 + 2252380 * 2 ^ 59
def prefixEnd_2252380 : Nat := 4983230072969 + 3 ^ 40 * 2252380 * 2
def baseEnd_2252380 : Nat := 1156553556574002786591499

theorem tailTrace_2252380 : CollatzResearch.WordTrace tailWord_2252380 prefixEnd_2252380 1156553556574002786591499 := by
  unfold tailWord_2252380
  simp only [CollatzResearch.WordTrace]
  refine ⟨41075523790009705361749297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54767365053346273815665729 41075523790009705361749297)
  ·
    refine ⟨30806642842507279021311973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41075523790009705361749297 30806642842507279021311973)
    ·
      refine ⟨5776245532970114816495995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30806642842507279021311973 5776245532970114816495995)
      ·
        refine ⟨8664368299455172224743993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5776245532970114816495995 8664368299455172224743993)
        ·
          refine ⟨6498276224591379168557995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8664368299455172224743993 6498276224591379168557995)
          ·
            refine ⟨9747414336887068752836993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6498276224591379168557995 9747414336887068752836993)
            ·
              refine ⟨7310560752665301564627745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9747414336887068752836993 7310560752665301564627745)
              ·
                refine ⟨5482920564498976173470809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7310560752665301564627745 5482920564498976173470809)
                ·
                  refine ⟨4112190423374232130103107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5482920564498976173470809 4112190423374232130103107)
                  ·
                    refine ⟨6168285635061348195154661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4112190423374232130103107 6168285635061348195154661)
                    ·
                      refine ⟨1156553556574002786591499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6168285635061348195154661 1156553556574002786591499)
                      ·
                        rfl

theorem cell23_2252380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2252380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252380 prefixEnd_2252380 := by exact prefixLift 2252380
  have htrace : WordTrace (prefixWord ++ tailWord_2252380) baseStart_2252380 baseEnd_2252380 := by
    simpa [prefixWord, tailWord_2252380, baseEnd_2252380] using wordTrace_append hprefix tailTrace_2252380
  have hstable : (prefixWord ++ tailWord_2252380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252380).length < 2 ^ (prefixWord ++ tailWord_2252380).sum := by decide
  have hdescent : baseEnd_2252380 < baseStart_2252380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252381 : List Nat := [1, 4, 4, 2, 1, 2, 2, 2, 5]
def baseStart_2252381 : Nat := 118140960795 + 2252381 * 2 ^ 59
def prefixEnd_2252381 : Nat := 4983230072969 + 3 ^ 40 * 2252381 * 2
def baseEnd_2252381 : Nat := 128506007783850809186555

theorem tailTrace_2252381 : CollatzResearch.WordTrace tailWord_2252381 prefixEnd_2252381 128506007783850809186555 := by
  unfold tailWord_2252381
  simp only [CollatzResearch.WordTrace]
  refine ⟨82151084053015787894284997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54767389368677191929523331 82151084053015787894284997)
  ·
    refine ⟨15403328259940460230178437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82151084053015787894284997 15403328259940460230178437)
    ·
      refine ⟨2888124048738836293158457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15403328259940460230178437 2888124048738836293158457)
      ·
        refine ⟨2166093036554127219868843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2888124048738836293158457 2166093036554127219868843)
        ·
          refine ⟨3249139554831190829803265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166093036554127219868843 3249139554831190829803265)
          ·
            refine ⟨2436854666123393122352449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249139554831190829803265 2436854666123393122352449)
            ·
              refine ⟨1827640999592544841764337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436854666123393122352449 1827640999592544841764337)
              ·
                refine ⟨1370730749694408631323253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827640999592544841764337 1370730749694408631323253)
                ·
                  refine ⟨128506007783850809186555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1370730749694408631323253 128506007783850809186555)
                  ·
                    rfl

theorem cell23_2252381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_2252381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252381 prefixEnd_2252381 := by exact prefixLift 2252381
  have htrace : WordTrace (prefixWord ++ tailWord_2252381) baseStart_2252381 baseEnd_2252381 := by
    simpa [prefixWord, tailWord_2252381, baseEnd_2252381] using wordTrace_append hprefix tailTrace_2252381
  have hstable : (prefixWord ++ tailWord_2252381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252381).length < 2 ^ (prefixWord ++ tailWord_2252381).sum := by decide
  have hdescent : baseEnd_2252381 < baseStart_2252381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252397 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_2252397 : Nat := 118140960795 + 2252397 * 2 ^ 59
def prefixEnd_2252397 : Nat := 4983230072969 + 3 ^ 40 * 2252397 * 2
def baseEnd_2252397 : Nat := 1156562285745129220078921

theorem tailTrace_2252397 : CollatzResearch.WordTrace tailWord_2252397 prefixEnd_2252397 1156562285745129220078921 := by
  unfold tailWord_2252397
  simp only [CollatzResearch.WordTrace]
  refine ⟨82151667620957822626867445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54767778413971881751244963 82151667620957822626867445)
  ·
    refine ⟨7701718839464795871268823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82151667620957822626867445 7701718839464795871268823)
    ·
      refine ⟨11552578259197193806903235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7701718839464795871268823 11552578259197193806903235)
      ·
        refine ⟨17328867388795790710354853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11552578259197193806903235 17328867388795790710354853)
        ·
          refine ⟨3249162635399210758191535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17328867388795790710354853 3249162635399210758191535)
          ·
            refine ⟨4873743953098816137287303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249162635399210758191535 4873743953098816137287303)
            ·
              refine ⟨7310615929648224205930955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4873743953098816137287303 7310615929648224205930955)
              ·
                refine ⟨10965923894472336308896433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7310615929648224205930955 10965923894472336308896433)
                ·
                  refine ⟨8224442920854252231672325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10965923894472336308896433 8224442920854252231672325)
                  ·
                    refine ⟨1542083047660172293438561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8224442920854252231672325 1542083047660172293438561)
                    ·
                      refine ⟨1156562285745129220078921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542083047660172293438561 1156562285745129220078921)
                      ·
                        rfl

theorem cell23_2252397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_2252397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252397 prefixEnd_2252397 := by exact prefixLift 2252397
  have htrace : WordTrace (prefixWord ++ tailWord_2252397) baseStart_2252397 baseEnd_2252397 := by
    simpa [prefixWord, tailWord_2252397, baseEnd_2252397] using wordTrace_append hprefix tailTrace_2252397
  have hstable : (prefixWord ++ tailWord_2252397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252397).length < 2 ^ (prefixWord ++ tailWord_2252397).sum := by decide
  have hdescent : baseEnd_2252397 < baseStart_2252397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
