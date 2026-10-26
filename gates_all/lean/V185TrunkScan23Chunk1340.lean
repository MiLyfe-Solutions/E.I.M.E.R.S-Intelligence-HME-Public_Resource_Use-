import V185TrunkScan23Chunk1339

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7936239 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 3, 5]
def baseStart_7936239 : Nat := 118140960795 + 7936239 * 2 ^ 59
def prefixEnd_7936239 : Nat := 4983230072969 + 3 ^ 40 * 7936239 * 2
def baseEnd_7936239 : Nat := 1358368398652493387371469

theorem tailTrace_7936239 : CollatzResearch.WordTrace tailWord_7936239 prefixEnd_7936239 1358368398652493387371469 := by
  unfold tailWord_7936239
  simp only [CollatzResearch.WordTrace]
  refine ⟨289458416295368979557267771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192972277530245986371511847 289458416295368979557267771)
  ·
    refine ⟨434187624443053469335901657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289458416295368979557267771 434187624443053469335901657)
    ·
      refine ⟨325640718332290102001926243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434187624443053469335901657 325640718332290102001926243)
      ·
        refine ⟨488461077498435153002889365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325640718332290102001926243 488461077498435153002889365)
        ·
          refine ⟨22896613007739147797010439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 488461077498435153002889365 22896613007739147797010439)
          ·
            refine ⟨34344919511608721695515659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22896613007739147797010439 34344919511608721695515659)
            ·
              refine ⟨51517379267413082543273489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34344919511608721695515659 51517379267413082543273489)
              ·
                refine ⟨38638034450559811907455117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51517379267413082543273489 38638034450559811907455117)
                ·
                  refine ⟨14489262918959929465295669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38638034450559811907455117 14489262918959929465295669)
                  ·
                    refine ⟨1358368398652493387371469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14489262918959929465295669 1358368398652493387371469)
                    ·
                      rfl

theorem cell23_7936239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_7936239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936239 prefixEnd_7936239 := by exact prefixLift 7936239
  have htrace : WordTrace (prefixWord ++ tailWord_7936239) baseStart_7936239 baseEnd_7936239 := by
    simpa [prefixWord, tailWord_7936239, baseEnd_7936239] using wordTrace_append hprefix tailTrace_7936239
  have hstable : (prefixWord ++ tailWord_7936239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936239).length < 2 ^ (prefixWord ++ tailWord_7936239).sum := by decide
  have hdescent : baseEnd_7936239 < baseStart_7936239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936259 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 4]
def baseStart_7936259 : Nat := 118140960795 + 7936259 * 2 ^ 59
def prefixEnd_7936259 : Nat := 4983230072969 + 3 ^ 40 * 7936259 * 2
def baseEnd_7936259 : Nat := 4075115465570570083864315

theorem tailTrace_7936259 : CollatzResearch.WordTrace tailWord_7936259 prefixEnd_7936259 4075115465570570083864315 := by
  unfold tailWord_7936259
  simp only [CollatzResearch.WordTrace]
  refine ⟨289459145755296522972995831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192972763836864348648663887 289459145755296522972995831)
  ·
    refine ⟨434188718632944784459493747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289459145755296522972995831 434188718632944784459493747)
    ·
      refine ⟨651283077949417176689240621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434188718632944784459493747 651283077949417176689240621)
      ·
        refine ⟨244231154231031441258465233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651283077949417176689240621 244231154231031441258465233)
        ·
          refine ⟨183173365673273580943848925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244231154231031441258465233 183173365673273580943848925)
          ·
            refine ⟨68690012127477592853943347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183173365673273580943848925 68690012127477592853943347)
            ·
              refine ⟨103035018191216389280915021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68690012127477592853943347 103035018191216389280915021)
              ·
                refine ⟨38638131821706145980343133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103035018191216389280915021 38638131821706145980343133)
                ·
                  refine ⟨14489299433139804742628675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38638131821706145980343133 14489299433139804742628675)
                  ·
                    refine ⟨21733949149709707113943013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14489299433139804742628675 21733949149709707113943013)
                    ·
                      refine ⟨4075115465570570083864315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21733949149709707113943013 4075115465570570083864315)
                      ·
                        rfl

theorem cell23_7936259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_7936259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936259 prefixEnd_7936259 := by exact prefixLift 7936259
  have htrace : WordTrace (prefixWord ++ tailWord_7936259) baseStart_7936259 baseEnd_7936259 := by
    simpa [prefixWord, tailWord_7936259, baseEnd_7936259] using wordTrace_append hprefix tailTrace_7936259
  have hstable : (prefixWord ++ tailWord_7936259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936259).length < 2 ^ (prefixWord ++ tailWord_7936259).sum := by decide
  have hdescent : baseEnd_7936259 < baseStart_7936259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936270 : List Nat := [4, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_7936270 : Nat := 118140960795 + 7936270 * 2 ^ 59
def prefixEnd_7936270 : Nat := 4983230072969 + 3 ^ 40 * 7936270 * 2
def baseEnd_7936270 : Nat := 4075121113857769540826765

theorem tailTrace_7936270 : CollatzResearch.WordTrace tailWord_7936270 prefixEnd_7936270 4075121113857769540826765 := by
  unfold tailWord_7936270
  simp only [CollatzResearch.WordTrace]
  refine ⟨36182443369782083981455783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192973031305504447901097509 36182443369782083981455783)
  ·
    refine ⟨54273665054673125972183675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36182443369782083981455783 54273665054673125972183675)
    ·
      refine ⟨81410497582009688958275513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54273665054673125972183675 81410497582009688958275513)
      ·
        refine ⟨61057873186507266718706635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81410497582009688958275513 61057873186507266718706635)
        ·
          refine ⟨91586809779760900078059953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61057873186507266718706635 91586809779760900078059953)
          ·
            refine ⟨68690107334820675058544965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91586809779760900078059953 68690107334820675058544965)
            ·
              refine ⟨12879395125278876573477181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68690107334820675058544965 12879395125278876573477181)
              ·
                refine ⟨4829773171979578715053943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12879395125278876573477181 4829773171979578715053943)
                ·
                  refine ⟨7244659757969368072580915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829773171979578715053943 7244659757969368072580915)
                  ·
                    refine ⟨10866989636954052108871373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7244659757969368072580915 10866989636954052108871373)
                    ·
                      refine ⟨4075121113857769540826765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10866989636954052108871373 4075121113857769540826765)
                      ·
                        rfl

theorem cell23_7936270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_7936270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936270 prefixEnd_7936270 := by exact prefixLift 7936270
  have htrace : WordTrace (prefixWord ++ tailWord_7936270) baseStart_7936270 baseEnd_7936270 := by
    simpa [prefixWord, tailWord_7936270, baseEnd_7936270] using wordTrace_append hprefix tailTrace_7936270
  have hstable : (prefixWord ++ tailWord_7936270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936270).length < 2 ^ (prefixWord ++ tailWord_7936270).sum := by decide
  have hdescent : baseEnd_7936270 < baseStart_7936270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936273 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 1, 5]
def baseStart_7936273 : Nat := 118140960795 + 7936273 * 2 ^ 59
def prefixEnd_7936273 : Nat := 4983230072969 + 3 ^ 40 * 7936273 * 2
def baseEnd_7936273 : Nat := 1358374218099911009696417

theorem tailTrace_7936273 : CollatzResearch.WordTrace tailWord_7936273 prefixEnd_7936273 1358374218099911009696417 := by
  unfold tailWord_7936273
  simp only [CollatzResearch.WordTrace]
  refine ⟨289459656377245803364005473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192973104251497202242670315 289459656377245803364005473)
  ·
    refine ⟨217094742282934352523004105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289459656377245803364005473 217094742282934352523004105)
    ·
      refine ⟨162821056712200764392253079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217094742282934352523004105 162821056712200764392253079)
      ·
        refine ⟨244231585068301146588379619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162821056712200764392253079 244231585068301146588379619)
        ·
          refine ⟨366347377602451719882569429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244231585068301146588379619 366347377602451719882569429)
          ·
            refine ⟨8586266662557462184747721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 366347377602451719882569429 8586266662557462184747721)
            ·
              refine ⟨6439699996918096638560791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8586266662557462184747721 6439699996918096638560791)
              ·
                refine ⟨9659549995377144957841187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439699996918096638560791 9659549995377144957841187)
                ·
                  refine ⟨14489324993065717436761781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659549995377144957841187 14489324993065717436761781)
                  ·
                    refine ⟨1358374218099911009696417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14489324993065717436761781 1358374218099911009696417)
                    ·
                      rfl

theorem cell23_7936273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_7936273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936273 prefixEnd_7936273 := by exact prefixLift 7936273
  have htrace : WordTrace (prefixWord ++ tailWord_7936273) baseStart_7936273 baseEnd_7936273 := by
    simpa [prefixWord, tailWord_7936273, baseEnd_7936273] using wordTrace_append hprefix tailTrace_7936273
  have hstable : (prefixWord ++ tailWord_7936273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936273).length < 2 ^ (prefixWord ++ tailWord_7936273).sum := by decide
  have hdescent : baseEnd_7936273 < baseStart_7936273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936289 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7936289 : Nat := 118140960795 + 7936289 * 2 ^ 59
def prefixEnd_7936289 : Nat := 4983230072969 + 3 ^ 40 * 7936289 * 2
def baseEnd_7936289 : Nat := 4075130869990204966489177

theorem tailTrace_7936289 : CollatzResearch.WordTrace tailWord_7936289 prefixEnd_7936289 4075130869990204966489177 := by
  unfold tailWord_7936289
  simp only [CollatzResearch.WordTrace]
  refine ⟨289460239945187838096587921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192973493296791892064391947 289460239945187838096587921)
  ·
    refine ⟨217095179958890878572440941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289460239945187838096587921 217095179958890878572440941)
    ·
      refine ⟨81410692484584079464665353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217095179958890878572440941 81410692484584079464665353)
      ·
        refine ⟨61058019363438059598499015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81410692484584079464665353 61058019363438059598499015)
        ·
          refine ⟨91587029045157089397748523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61058019363438059598499015 91587029045157089397748523)
          ·
            refine ⟨137380543567735634096622785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91587029045157089397748523 137380543567735634096622785)
            ·
              refine ⟨103035407675801725572467089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137380543567735634096622785 103035407675801725572467089)
              ·
                refine ⟨77276555756851294179350317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103035407675801725572467089 77276555756851294179350317)
                ·
                  refine ⟨28978708408819235317256369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77276555756851294179350317 28978708408819235317256369)
                  ·
                    refine ⟨21734031306614426487942277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28978708408819235317256369 21734031306614426487942277)
                    ·
                      refine ⟨4075130869990204966489177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21734031306614426487942277 4075130869990204966489177)
                      ·
                        rfl

theorem cell23_7936289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7936289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936289 prefixEnd_7936289 := by exact prefixLift 7936289
  have htrace : WordTrace (prefixWord ++ tailWord_7936289) baseStart_7936289 baseEnd_7936289 := by
    simpa [prefixWord, tailWord_7936289, baseEnd_7936289] using wordTrace_append hprefix tailTrace_7936289
  have hstable : (prefixWord ++ tailWord_7936289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936289).length < 2 ^ (prefixWord ++ tailWord_7936289).sum := by decide
  have hdescent : baseEnd_7936289 < baseStart_7936289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936306 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_7936306 : Nat := 118140960795 + 7936306 * 2 ^ 59
def prefixEnd_7936306 : Nat := 4983230072969 + 3 ^ 40 * 7936306 * 2
def baseEnd_7936306 : Nat := 4075139599161331399976599

theorem tailTrace_7936306 : CollatzResearch.WordTrace tailWord_7936306 prefixEnd_7936306 4075139599161331399976599 := by
  unfold tailWord_7936306
  simp only [CollatzResearch.WordTrace]
  refine ⟨72365214996531562499989193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192973906657417499999971181 72365214996531562499989193)
  ·
    refine ⟨54273911247398671874991895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72365214996531562499989193 54273911247398671874991895)
    ·
      refine ⟨81410866871098007812487843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54273911247398671874991895 81410866871098007812487843)
      ·
        refine ⟨122116300306647011718731765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81410866871098007812487843 122116300306647011718731765)
        ·
          refine ⟨11448403153748157348631103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122116300306647011718731765 11448403153748157348631103)
          ·
            refine ⟨17172604730622236022946655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448403153748157348631103 17172604730622236022946655)
            ·
              refine ⟨25758907095933354034419983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17172604730622236022946655 25758907095933354034419983)
              ·
                refine ⟨38638360643900031051629975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25758907095933354034419983 38638360643900031051629975)
                ·
                  refine ⟨57957540965850046577444963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38638360643900031051629975 57957540965850046577444963)
                  ·
                    refine ⟨86936311448775069866167445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57957540965850046577444963 86936311448775069866167445)
                    ·
                      refine ⟨4075139599161331399976599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86936311448775069866167445 4075139599161331399976599)
                      ·
                        rfl

theorem cell23_7936306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_7936306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936306 prefixEnd_7936306 := by exact prefixLift 7936306
  have htrace : WordTrace (prefixWord ++ tailWord_7936306) baseStart_7936306 baseEnd_7936306 := by
    simpa [prefixWord, tailWord_7936306, baseEnd_7936306] using wordTrace_append hprefix tailTrace_7936306
  have hstable : (prefixWord ++ tailWord_7936306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936306).length < 2 ^ (prefixWord ++ tailWord_7936306).sum := by decide
  have hdescent : baseEnd_7936306 < baseStart_7936306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936313 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7936313 : Nat := 118140960795 + 7936313 * 2 ^ 59
def prefixEnd_7936313 : Nat := 4983230072969 + 3 ^ 40 * 7936313 * 2
def baseEnd_7936313 : Nat := 4075143193525912872589067

theorem tailTrace_7936313 : CollatzResearch.WordTrace tailWord_7936313 prefixEnd_7936313 4075143193525912872589067 := by
  unfold tailWord_7936313
  simp only [CollatzResearch.WordTrace]
  refine ⟨289461115297100890195461593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192974076864733926796974395 289461115297100890195461593)
  ·
    refine ⟨217095836472825667646596195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289461115297100890195461593 217095836472825667646596195)
    ·
      refine ⟨325643754709238501469894293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217095836472825667646596195 325643754709238501469894293)
      ·
        refine ⟨15264551001995554756401295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325643754709238501469894293 15264551001995554756401295)
        ·
          refine ⟨22896826502993332134601943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15264551001995554756401295 22896826502993332134601943)
          ·
            refine ⟨34345239754489998201902915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22896826502993332134601943 34345239754489998201902915)
            ·
              refine ⟨51517859631734997302854373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34345239754489998201902915 51517859631734997302854373)
              ·
                refine ⟨9659598680950311994285195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51517859631734997302854373 9659598680950311994285195)
                ·
                  refine ⟨14489398021425467991427793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659598680950311994285195 14489398021425467991427793)
                  ·
                    refine ⟨10867048516069100993570845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14489398021425467991427793 10867048516069100993570845)
                    ·
                      refine ⟨4075143193525912872589067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10867048516069100993570845 4075143193525912872589067)
                      ·
                        rfl

theorem cell23_7936313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7936313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936313 prefixEnd_7936313 := by exact prefixLift 7936313
  have htrace : WordTrace (prefixWord ++ tailWord_7936313) baseStart_7936313 baseEnd_7936313 := by
    simpa [prefixWord, tailWord_7936313, baseEnd_7936313] using wordTrace_append hprefix tailTrace_7936313
  have hstable : (prefixWord ++ tailWord_7936313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936313).length < 2 ^ (prefixWord ++ tailWord_7936313).sum := by decide
  have hdescent : baseEnd_7936313 < baseStart_7936313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936343 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_7936343 : Nat := 118140960795 + 7936343 * 2 ^ 59
def prefixEnd_7936343 : Nat := 4983230072969 + 3 ^ 40 * 7936343 * 2
def baseEnd_7936343 : Nat := 4075158597945547755213929

theorem tailTrace_7936343 : CollatzResearch.WordTrace tailWord_7936343 prefixEnd_7936343 4075158597945547755213929 := by
  unfold tailWord_7936343
  simp only [CollatzResearch.WordTrace]
  refine ⟨289462209486992205319053683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192974806324661470212702455 289462209486992205319053683)
  ·
    refine ⟨434193314230488307978580525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289462209486992205319053683 434193314230488307978580525)
    ·
      refine ⟨162822492836433115491967697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434193314230488307978580525 162822492836433115491967697)
      ·
        refine ⟨122116869627324836618975773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162822492836433115491967697 122116869627324836618975773)
        ·
          refine ⟨45793826110246813732115915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122116869627324836618975773 45793826110246813732115915)
          ·
            refine ⟨68690739165370220598173873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45793826110246813732115915 68690739165370220598173873)
            ·
              refine ⟨51518054374027665448630405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68690739165370220598173873 51518054374027665448630405)
              ·
                refine ⟨9659635195130187271618201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51518054374027665448630405 9659635195130187271618201)
                ·
                  refine ⟨7244726396347640453713651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659635195130187271618201 7244726396347640453713651)
                  ·
                    refine ⟨10867089594521460680570477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7244726396347640453713651 10867089594521460680570477)
                    ·
                      refine ⟨4075158597945547755213929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10867089594521460680570477 4075158597945547755213929)
                      ·
                        rfl

theorem cell23_7936343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_7936343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936343 prefixEnd_7936343 := by exact prefixLift 7936343
  have htrace : WordTrace (prefixWord ++ tailWord_7936343) baseStart_7936343 baseEnd_7936343 := by
    simpa [prefixWord, tailWord_7936343, baseEnd_7936343] using wordTrace_append hprefix tailTrace_7936343
  have hstable : (prefixWord ++ tailWord_7936343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936343).length < 2 ^ (prefixWord ++ tailWord_7936343).sum := by decide
  have hdescent : baseEnd_7936343 < baseStart_7936343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936360 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7936360 : Nat := 118140960795 + 7936360 * 2 ^ 59
def prefixEnd_7936360 : Nat := 4983230072969 + 3 ^ 40 * 7936360 * 2
def baseEnd_7936360 : Nat := 4075167327116674188701351

theorem tailTrace_7936360 : CollatzResearch.WordTrace tailWord_7936360 prefixEnd_7936360 4075167327116674188701351 := by
  unfold tailWord_7936360
  simp only [CollatzResearch.WordTrace]
  refine ⟨144731414763965308611211267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192975219685287078148281689 144731414763965308611211267)
  ·
    refine ⟨217097122145947962916816901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144731414763965308611211267 217097122145947962916816901)
    ·
      refine ⟨40705710402365243046903169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217097122145947962916816901 40705710402365243046903169)
      ·
        refine ⟨30529282801773932285177377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40705710402365243046903169 30529282801773932285177377)
        ·
          refine ⟨22896962101330449213883033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30529282801773932285177377 22896962101330449213883033)
          ·
            refine ⟨17172721575997836910412275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22896962101330449213883033 17172721575997836910412275)
            ·
              refine ⟨25759082363996755365618413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17172721575997836910412275 25759082363996755365618413)
              ·
                refine ⟨9659655886498783262106905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25759082363996755365618413 9659655886498783262106905)
                ·
                  refine ⟨7244741914874087446580179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659655886498783262106905 7244741914874087446580179)
                  ·
                    refine ⟨10867112872311131169870269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7244741914874087446580179 10867112872311131169870269)
                    ·
                      refine ⟨4075167327116674188701351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10867112872311131169870269 4075167327116674188701351)
                      ·
                        rfl

theorem cell23_7936360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7936360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936360 prefixEnd_7936360 := by exact prefixLift 7936360
  have htrace : WordTrace (prefixWord ++ tailWord_7936360) baseStart_7936360 baseEnd_7936360 := by
    simpa [prefixWord, tailWord_7936360, baseEnd_7936360] using wordTrace_append hprefix tailTrace_7936360
  have hstable : (prefixWord ++ tailWord_7936360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936360).length < 2 ^ (prefixWord ++ tailWord_7936360).sum := by decide
  have hdescent : baseEnd_7936360 < baseStart_7936360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936370 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_7936370 : Nat := 118140960795 + 7936370 * 2 ^ 59
def prefixEnd_7936370 : Nat := 4983230072969 + 3 ^ 40 * 7936370 * 2
def baseEnd_7936370 : Nat := 4075172461923219149576305

theorem tailTrace_7936370 : CollatzResearch.WordTrace tailWord_7936370 prefixEnd_7936370 4075172461923219149576305 := by
  unfold tailWord_7936370
  simp only [CollatzResearch.WordTrace]
  refine ⟨72365798564473597232571641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192975462838596259286857709 72365798564473597232571641)
  ·
    refine ⟨54274348923355197924428731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72365798564473597232571641 54274348923355197924428731)
    ·
      refine ⟨81411523385032796886643097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54274348923355197924428731 81411523385032796886643097)
      ·
        refine ⟨61058642538774597664982323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81411523385032796886643097 61058642538774597664982323)
        ·
          refine ⟨91587963808161896497473485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61058642538774597664982323 91587963808161896497473485)
          ·
            refine ⟨34345486428060711186552557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91587963808161896497473485 34345486428060711186552557)
            ·
              refine ⟨12879557410522766694957209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34345486428060711186552557 12879557410522766694957209)
              ·
                refine ⟨9659668057892075021217907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12879557410522766694957209 9659668057892075021217907)
                ·
                  refine ⟨14489502086838112531826861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659668057892075021217907 14489502086838112531826861)
                  ·
                    refine ⟨5433563282564292199435073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14489502086838112531826861 5433563282564292199435073)
                    ·
                      refine ⟨4075172461923219149576305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433563282564292199435073 4075172461923219149576305)
                      ·
                        rfl

theorem cell23_7936370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_7936370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936370 prefixEnd_7936370 := by exact prefixLift 7936370
  have htrace : WordTrace (prefixWord ++ tailWord_7936370) baseStart_7936370 baseEnd_7936370 := by
    simpa [prefixWord, tailWord_7936370, baseEnd_7936370] using wordTrace_append hprefix tailTrace_7936370
  have hstable : (prefixWord ++ tailWord_7936370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936370).length < 2 ^ (prefixWord ++ tailWord_7936370).sum := by decide
  have hdescent : baseEnd_7936370 < baseStart_7936370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936387 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 1, 3, 2]
def baseStart_7936387 : Nat := 118140960795 + 7936387 * 2 ^ 59
def prefixEnd_7936387 : Nat := 4983230072969 + 3 ^ 40 * 7936387 * 2
def baseEnd_7936387 : Nat := 4075181191094345583063727

theorem tailTrace_7936387 : CollatzResearch.WordTrace tailWord_7936387 prefixEnd_7936387 4075181191094345583063727 := by
  unfold tailWord_7936387
  simp only [CollatzResearch.WordTrace]
  refine ⟨289463814298832800833655415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192975876199221867222436943 289463814298832800833655415)
  ·
    refine ⟨434195721448249201250483123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289463814298832800833655415 434195721448249201250483123)
    ·
      refine ⟨651293582172373801875724685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434195721448249201250483123 651293582172373801875724685)
      ·
        refine ⟨244235093314640175703396757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651293582172373801875724685 244235093314640175703396757)
        ·
          refine ⟨11448519999123758236096723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244235093314640175703396757 11448519999123758236096723)
          ·
            refine ⟨17172779998685637354145085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448519999123758236096723 17172779998685637354145085)
            ·
              refine ⟨6439792499507114007804407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17172779998685637354145085 6439792499507114007804407)
              ·
                refine ⟨9659688749260671011706611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439792499507114007804407 9659688749260671011706611)
                ·
                  refine ⟨14489533123891006517559917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659688749260671011706611 14489533123891006517559917)
                  ·
                    refine ⟨5433574921459127444084969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14489533123891006517559917 5433574921459127444084969)
                    ·
                      refine ⟨4075181191094345583063727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433574921459127444084969 4075181191094345583063727)
                      ·
                        rfl

theorem cell23_7936387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_7936387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936387 prefixEnd_7936387 := by exact prefixLift 7936387
  have htrace : WordTrace (prefixWord ++ tailWord_7936387) baseStart_7936387 baseEnd_7936387 := by
    simpa [prefixWord, tailWord_7936387, baseEnd_7936387] using wordTrace_append hprefix tailTrace_7936387
  have hstable : (prefixWord ++ tailWord_7936387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936387).length < 2 ^ (prefixWord ++ tailWord_7936387).sum := by decide
  have hdescent : baseEnd_7936387 < baseStart_7936387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936413 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_7936413 : Nat := 118140960795 + 7936413 * 2 ^ 59
def prefixEnd_7936413 : Nat := 4983230072969 + 3 ^ 40 * 7936413 * 2
def baseEnd_7936413 : Nat := 4075194541591362481338607

theorem tailTrace_7936413 : CollatzResearch.WordTrace tailWord_7936413 prefixEnd_7936413 4075194541591362481338607 := by
  unfold tailWord_7936413
  simp only [CollatzResearch.WordTrace]
  refine ⟨289464762596738607274101893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192976508397825738182734595 289464762596738607274101893)
  ·
    refine ⟨54274642986888488863894105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289464762596738607274101893 54274642986888488863894105)
    ·
      refine ⟨40705982240166366647920579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54274642986888488863894105 40705982240166366647920579)
      ·
        refine ⟨61058973360249549971880869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40705982240166366647920579 61058973360249549971880869)
        ·
          refine ⟨11448557505046790619727663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61058973360249549971880869 11448557505046790619727663)
          ·
            refine ⟨17172836257570185929591495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448557505046790619727663 17172836257570185929591495)
            ·
              refine ⟨25759254386355278894387243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17172836257570185929591495 25759254386355278894387243)
              ·
                refine ⟨38638881579532918341580865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25759254386355278894387243 38638881579532918341580865)
                ·
                  refine ⟨28979161184649688756185649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38638881579532918341580865 28979161184649688756185649)
                  ·
                    refine ⟨21734370888487266567139237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28979161184649688756185649 21734370888487266567139237)
                    ·
                      refine ⟨4075194541591362481338607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21734370888487266567139237 4075194541591362481338607)
                      ·
                        rfl

theorem cell23_7936413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_7936413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936413 prefixEnd_7936413 := by exact prefixLift 7936413
  have htrace : WordTrace (prefixWord ++ tailWord_7936413) baseStart_7936413 baseEnd_7936413 := by
    simpa [prefixWord, tailWord_7936413, baseEnd_7936413] using wordTrace_append hprefix tailTrace_7936413
  have hstable : (prefixWord ++ tailWord_7936413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936413).length < 2 ^ (prefixWord ++ tailWord_7936413).sum := by decide
  have hdescent : baseEnd_7936413 < baseStart_7936413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936416 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3]
def baseStart_7936416 : Nat := 118140960795 + 7936416 * 2 ^ 59
def prefixEnd_7936416 : Nat := 4983230072969 + 3 ^ 40 * 7936416 * 2
def baseEnd_7936416 : Nat := 4075196082033325969601093

theorem tailTrace_7936416 : CollatzResearch.WordTrace tailWord_7936416 prefixEnd_7936416 4075196082033325969601093 := by
  unfold tailWord_7936416
  simp only [CollatzResearch.WordTrace]
  refine ⟨144732436007863869393230551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192976581343818492524307401 144732436007863869393230551)
  ·
    refine ⟨217098654011795804089845827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144732436007863869393230551 217098654011795804089845827)
    ·
      refine ⟨325647981017693706134768741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217098654011795804089845827 325647981017693706134768741)
      ·
        refine ⟨61058996440817569900269139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325647981017693706134768741 61058996440817569900269139)
        ·
          refine ⟨91588494661226354850403709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61058996440817569900269139 91588494661226354850403709)
          ·
            refine ⟨34345685497959883068901391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91588494661226354850403709 34345685497959883068901391)
            ·
              refine ⟨51518528246939824603352087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34345685497959883068901391 51518528246939824603352087)
              ·
                refine ⟨77277792370409736905028131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51518528246939824603352087 77277792370409736905028131)
                ·
                  refine ⟨115916688555614605357542197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77277792370409736905028131 115916688555614605357542197)
                  ·
                    refine ⟨10867189552088869252269581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115916688555614605357542197 10867189552088869252269581)
                    ·
                      refine ⟨4075196082033325969601093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10867189552088869252269581 4075196082033325969601093)
                      ·
                        rfl

theorem cell23_7936416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_7936416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936416 prefixEnd_7936416 := by exact prefixLift 7936416
  have htrace : WordTrace (prefixWord ++ tailWord_7936416) baseStart_7936416 baseEnd_7936416 := by
    simpa [prefixWord, tailWord_7936416, baseEnd_7936416] using wordTrace_append hprefix tailTrace_7936416
  have hstable : (prefixWord ++ tailWord_7936416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936416).length < 2 ^ (prefixWord ++ tailWord_7936416).sum := by decide
  have hdescent : baseEnd_7936416 < baseStart_7936416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936417 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7936417 : Nat := 118140960795 + 7936417 * 2 ^ 59
def prefixEnd_7936417 : Nat := 4983230072969 + 3 ^ 40 * 7936417 * 2
def baseEnd_7936417 : Nat := 4075196595513980465688589

theorem tailTrace_7936417 : CollatzResearch.WordTrace tailWord_7936417 prefixEnd_7936417 4075196595513980465688589 := by
  unfold tailWord_7936417
  simp only [CollatzResearch.WordTrace]
  refine ⟨289464908488724115957247505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192976605659149410638165003 289464908488724115957247505)
  ·
    refine ⟨217098681366543086967935629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289464908488724115957247505 217098681366543086967935629)
    ·
      refine ⟨81412005512453657612975861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217098681366543086967935629 81412005512453657612975861)
      ·
        refine ⟨7632375516792530401216487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81412005512453657612975861 7632375516792530401216487)
        ·
          refine ⟨11448563275188795601824731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632375516792530401216487 11448563275188795601824731)
          ·
            refine ⟨17172844912783193402737097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448563275188795601824731 17172844912783193402737097)
            ·
              refine ⟨12879633684587395052052823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17172844912783193402737097 12879633684587395052052823)
              ·
                refine ⟨19319450526881092578079235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12879633684587395052052823 19319450526881092578079235)
                ·
                  refine ⟨28979175790321638867118853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19319450526881092578079235 28979175790321638867118853)
                  ·
                    refine ⟨5433595460685307287584785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28979175790321638867118853 5433595460685307287584785)
                    ·
                      refine ⟨4075196595513980465688589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433595460685307287584785 4075196595513980465688589)
                      ·
                        rfl

theorem cell23_7936417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7936417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936417 prefixEnd_7936417 := by exact prefixLift 7936417
  have htrace : WordTrace (prefixWord ++ tailWord_7936417) baseStart_7936417 baseEnd_7936417 := by
    simpa [prefixWord, tailWord_7936417, baseEnd_7936417] using wordTrace_append hprefix tailTrace_7936417
  have hstable : (prefixWord ++ tailWord_7936417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936417).length < 2 ^ (prefixWord ++ tailWord_7936417).sum := by decide
  have hdescent : baseEnd_7936417 < baseStart_7936417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936446 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7936446 : Nat := 118140960795 + 7936446 * 2 ^ 59
def prefixEnd_7936446 : Nat := 4983230072969 + 3 ^ 40 * 7936446 * 2
def baseEnd_7936446 : Nat := 4075211486452960852225955

theorem tailTrace_7936446 : CollatzResearch.WordTrace tailWord_7936446 prefixEnd_7936446 4075211486452960852225955 := by
  unfold tailWord_7936446
  simp only [CollatzResearch.WordTrace]
  refine ⟨36183245775702381738756649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192977310803746035940035461 36183245775702381738756649)
  ·
    refine ⟨27137434331776786304067487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36183245775702381738756649 27137434331776786304067487)
    ·
      refine ⟨40706151497665179456101231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27137434331776786304067487 40706151497665179456101231)
      ·
        refine ⟨61059227246497769184151847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40706151497665179456101231 61059227246497769184151847)
        ·
          refine ⟨91588840869746653776227771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61059227246497769184151847 91588840869746653776227771)
          ·
            refine ⟨137383261304619980664341657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91588840869746653776227771 137383261304619980664341657)
            ·
              refine ⟨103037445978464985498256243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137383261304619980664341657 103037445978464985498256243)
              ·
                refine ⟨154556168967697478247384365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103037445978464985498256243 154556168967697478247384365)
                ·
                  refine ⟨57958563362886554342769137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154556168967697478247384365 57958563362886554342769137)
                  ·
                    refine ⟨43468922522164915757076853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57958563362886554342769137 43468922522164915757076853)
                    ·
                      refine ⟨4075211486452960852225955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43468922522164915757076853 4075211486452960852225955)
                      ·
                        rfl

theorem cell23_7936446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7936446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936446 prefixEnd_7936446 := by exact prefixLift 7936446
  have htrace : WordTrace (prefixWord ++ tailWord_7936446) baseStart_7936446 baseEnd_7936446 := by
    simpa [prefixWord, tailWord_7936446, baseEnd_7936446] using wordTrace_append hprefix tailTrace_7936446
  have hstable : (prefixWord ++ tailWord_7936446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936446).length < 2 ^ (prefixWord ++ tailWord_7936446).sum := by decide
  have hdescent : baseEnd_7936446 < baseStart_7936446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936473 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 2, 4, 2]
def baseStart_7936473 : Nat := 118140960795 + 7936473 * 2 ^ 59
def prefixEnd_7936473 : Nat := 4983230072969 + 3 ^ 40 * 7936473 * 2
def baseEnd_7936473 : Nat := 4075225350430632246588331

theorem tailTrace_7936473 : CollatzResearch.WordTrace tailWord_7936473 prefixEnd_7936473 4075225350430632246588331 := by
  unfold tailWord_7936473
  simp only [CollatzResearch.WordTrace]
  refine ⟨289466950976521237521286073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192977967317680825014190715 289466950976521237521286073)
  ·
    refine ⟨217100213232390928140964555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289466950976521237521286073 217100213232390928140964555)
    ·
      refine ⟨325650319848586392211446833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217100213232390928140964555 325650319848586392211446833)
      ·
        refine ⟨244237739886439794158585125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325650319848586392211446833 244237739886439794158585125)
        ·
          refine ⟨45794576228707461404734711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244237739886439794158585125 45794576228707461404734711)
          ·
            refine ⟨68691864343061192107102067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45794576228707461404734711 68691864343061192107102067)
            ·
              refine ⟨103037796514591788160653101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68691864343061192107102067 103037796514591788160653101)
              ·
                refine ⟨38639173692971920560244913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103037796514591788160653101 38639173692971920560244913)
                ·
                  refine ⟨28979380269728940420183685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38639173692971920560244913 28979380269728940420183685)
                  ·
                    refine ⟨5433633800574176328784441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28979380269728940420183685 5433633800574176328784441)
                    ·
                      refine ⟨4075225350430632246588331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433633800574176328784441 4075225350430632246588331)
                      ·
                        rfl

theorem cell23_7936473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_7936473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936473 prefixEnd_7936473 := by exact prefixLift 7936473
  have htrace : WordTrace (prefixWord ++ tailWord_7936473) baseStart_7936473 baseEnd_7936473 := by
    simpa [prefixWord, tailWord_7936473, baseEnd_7936473] using wordTrace_append hprefix tailTrace_7936473
  have hstable : (prefixWord ++ tailWord_7936473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936473).length < 2 ^ (prefixWord ++ tailWord_7936473).sum := by decide
  have hdescent : baseEnd_7936473 < baseStart_7936473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936576 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_7936576 : Nat := 118140960795 + 7936576 * 2 ^ 59
def prefixEnd_7936576 : Nat := 4983230072969 + 3 ^ 40 * 7936576 * 2
def baseEnd_7936576 : Nat := 4075278238938045343600357

theorem tailTrace_7936576 : CollatzResearch.WordTrace tailWord_7936576 prefixEnd_7936576 4075278238938045343600357 := by
  unfold tailWord_7936576
  simp only [CollatzResearch.WordTrace]
  refine ⟨144735353847574043056142791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192980471796765390741523721 144735353847574043056142791)
  ·
    refine ⟨217103030771361064584214187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144735353847574043056142791 217103030771361064584214187)
    ·
      refine ⟨325654546157041596876321281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217103030771361064584214187 325654546157041596876321281)
      ·
        refine ⟨244240909617781197657240961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325654546157041596876321281 244240909617781197657240961)
        ·
          refine ⟨183180682213335898242930721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244240909617781197657240961 183180682213335898242930721)
          ·
            refine ⟨137385511660001923682198041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183180682213335898242930721 137385511660001923682198041)
            ·
              refine ⟨103039133745001442761648531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137385511660001923682198041 103039133745001442761648531)
              ·
                refine ⟨154558700617502164142472797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103039133745001442761648531 154558700617502164142472797)
                ·
                  refine ⟨57959512731563311553427299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154558700617502164142472797 57959512731563311553427299)
                  ·
                    refine ⟨86939269097344967330140949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57959512731563311553427299 86939269097344967330140949)
                    ·
                      refine ⟨4075278238938045343600357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86939269097344967330140949 4075278238938045343600357)
                      ·
                        rfl

theorem cell23_7936576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_7936576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936576 prefixEnd_7936576 := by exact prefixLift 7936576
  have htrace : WordTrace (prefixWord ++ tailWord_7936576) baseStart_7936576 baseEnd_7936576 := by
    simpa [prefixWord, tailWord_7936576, baseEnd_7936576] using wordTrace_append hprefix tailTrace_7936576
  have hstable : (prefixWord ++ tailWord_7936576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936576).length < 2 ^ (prefixWord ++ tailWord_7936576).sum := by decide
  have hdescent : baseEnd_7936576 < baseStart_7936576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936590 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_7936590 : Nat := 118140960795 + 7936590 * 2 ^ 59
def prefixEnd_7936590 : Nat := 4983230072969 + 3 ^ 40 * 7936590 * 2
def baseEnd_7936590 : Nat := 1358428475889069429608431

theorem tailTrace_7936590 : CollatzResearch.WordTrace tailWord_7936590 prefixEnd_7936590 1358428475889069429608431 := by
  unfold tailWord_7936590
  simp only [CollatzResearch.WordTrace]
  refine ⟨36183902289637170812911903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192980812211398244335530149 36183902289637170812911903)
  ·
    refine ⟨54275853434455756219367855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36183902289637170812911903 54275853434455756219367855)
    ·
      refine ⟨81413780151683634329051783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54275853434455756219367855 81413780151683634329051783)
      ·
        refine ⟨122120670227525451493577675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81413780151683634329051783 122120670227525451493577675)
        ·
          refine ⟨183181005341288177240366513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122120670227525451493577675 183181005341288177240366513)
          ·
            refine ⟨137385754005966132930274885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183181005341288177240366513 137385754005966132930274885)
            ·
              refine ⟨25759828876118649924426541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137385754005966132930274885 25759828876118649924426541)
              ·
                refine ⟨9659935828544493721659953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25759828876118649924426541 9659935828544493721659953)
                ·
                  refine ⟨7244951871408370291244965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659935828544493721659953 7244951871408370291244965)
                  ·
                    refine ⟨1358428475889069429608431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7244951871408370291244965 1358428475889069429608431)
                    ·
                      rfl

theorem cell23_7936590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_7936590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936590 prefixEnd_7936590 := by exact prefixLift 7936590
  have htrace : WordTrace (prefixWord ++ tailWord_7936590) baseStart_7936590 baseEnd_7936590 := by
    simpa [prefixWord, tailWord_7936590, baseEnd_7936590] using wordTrace_append hprefix tailTrace_7936590
  have hstable : (prefixWord ++ tailWord_7936590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936590).length < 2 ^ (prefixWord ++ tailWord_7936590).sum := by decide
  have hdescent : baseEnd_7936590 < baseStart_7936590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936593 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_7936593 : Nat := 118140960795 + 7936593 * 2 ^ 59
def prefixEnd_7936593 : Nat := 4983230072969 + 3 ^ 40 * 7936593 * 2
def baseEnd_7936593 : Nat := 4075286968109171777087779

theorem tailTrace_7936593 : CollatzResearch.WordTrace tailWord_7936593 prefixEnd_7936593 4075286968109171777087779 := by
  unfold tailWord_7936593
  simp only [CollatzResearch.WordTrace]
  refine ⟨289471327736086498015654433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192980885157390998677102955 289471327736086498015654433)
  ·
    refine ⟨217103495802064873511740825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289471327736086498015654433 217103495802064873511740825)
    ·
      refine ⟨162827621851548655133805619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217103495802064873511740825 162827621851548655133805619)
      ·
        refine ⟨244241432777322982700708429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162827621851548655133805619 244241432777322982700708429)
        ·
          refine ⟨91590537291496118512765661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244241432777322982700708429 91590537291496118512765661)
          ·
            refine ⟨34346451484311044442287123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91590537291496118512765661 34346451484311044442287123)
            ·
              refine ⟨51519677226466566663430685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34346451484311044442287123 51519677226466566663430685)
              ·
                refine ⟨19319878959924962498786507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51519677226466566663430685 19319878959924962498786507)
                ·
                  refine ⟨28979818439887443748179761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19319878959924962498786507 28979818439887443748179761)
                  ·
                    refine ⟨21734863829915582811134821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28979818439887443748179761 21734863829915582811134821)
                    ·
                      refine ⟨4075286968109171777087779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21734863829915582811134821 4075286968109171777087779)
                      ·
                        rfl

theorem cell23_7936593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_7936593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936593 prefixEnd_7936593 := by exact prefixLift 7936593
  have htrace : WordTrace (prefixWord ++ tailWord_7936593) baseStart_7936593 baseEnd_7936593 := by
    simpa [prefixWord, tailWord_7936593, baseEnd_7936593] using wordTrace_append hprefix tailTrace_7936593
  have hstable : (prefixWord ++ tailWord_7936593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936593).length < 2 ^ (prefixWord ++ tailWord_7936593).sum := by decide
  have hdescent : baseEnd_7936593 < baseStart_7936593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936624 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 2, 4]
def baseStart_7936624 : Nat := 118140960795 + 7936624 * 2 ^ 59
def prefixEnd_7936624 : Nat := 4983230072969 + 3 ^ 40 * 7936624 * 2
def baseEnd_7936624 : Nat := 1358434295336487051933379

theorem tailTrace_7936624 : CollatzResearch.WordTrace tailWord_7936624 prefixEnd_7936624 1358434295336487051933379 := by
  unfold tailWord_7936624
  simp only [CollatzResearch.WordTrace]
  refine ⟨144736229199487095155016463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192981638932649460206688617 144736229199487095155016463)
  ·
    refine ⟨217104343799230642732524695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144736229199487095155016463 217104343799230642732524695)
    ·
      refine ⟨325656515698845964098787043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217104343799230642732524695 325656515698845964098787043)
      ·
        refine ⟨488484773548268946148180565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325656515698845964098787043 488484773548268946148180565)
        ·
          refine ⟨5724430940018776712673991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 488484773548268946148180565 5724430940018776712673991)
          ·
            refine ⟨8586646410028165069010987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724430940018776712673991 8586646410028165069010987)
            ·
              refine ⟨12879969615042247603516481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8586646410028165069010987 12879969615042247603516481)
              ·
                refine ⟨9659977211281685702637361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12879969615042247603516481 9659977211281685702637361)
                ·
                  refine ⟨7244982908461264276978021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659977211281685702637361 7244982908461264276978021)
                  ·
                    refine ⟨1358434295336487051933379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7244982908461264276978021 1358434295336487051933379)
                    ·
                      rfl

theorem cell23_7936624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 4].length) (baseStart_7936624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936624 prefixEnd_7936624 := by exact prefixLift 7936624
  have htrace : WordTrace (prefixWord ++ tailWord_7936624) baseStart_7936624 baseEnd_7936624 := by
    simpa [prefixWord, tailWord_7936624, baseEnd_7936624] using wordTrace_append hprefix tailTrace_7936624
  have hstable : (prefixWord ++ tailWord_7936624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936624).length < 2 ^ (prefixWord ++ tailWord_7936624).sum := by decide
  have hdescent : baseEnd_7936624 < baseStart_7936624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936660 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7936660 : Nat := 118140960795 + 7936660 * 2 ^ 59
def prefixEnd_7936660 : Nat := 4983230072969 + 3 ^ 40 * 7936660 * 2
def baseEnd_7936660 : Nat := 4075321371313023014949971

theorem tailTrace_7936660 : CollatzResearch.WordTrace tailWord_7936660 prefixEnd_7936660 4075321371313023014949971 := by
  unfold tailWord_7936660
  simp only [CollatzResearch.WordTrace]
  refine ⟨144736885713421884229171717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192982514284562512305562289 144736885713421884229171717)
  ·
    refine ⟨27138166071266603292969697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144736885713421884229171717 27138166071266603292969697)
    ·
      refine ⟨20353624553449952469727273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27138166071266603292969697 20353624553449952469727273)
      ·
        refine ⟨15265218415087464352295455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20353624553449952469727273 15265218415087464352295455)
        ·
          refine ⟨22897827622631196528443183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15265218415087464352295455 22897827622631196528443183)
          ·
            refine ⟨34346741433946794792664775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22897827622631196528443183 34346741433946794792664775)
            ·
              refine ⟨51520112150920192188997163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34346741433946794792664775 51520112150920192188997163)
              ·
                refine ⟨77280168226380288283495745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51520112150920192188997163 77280168226380288283495745)
                ·
                  refine ⟨57960126169785216212621809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77280168226380288283495745 57960126169785216212621809)
                  ·
                    refine ⟨43470094627338912159466357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57960126169785216212621809 43470094627338912159466357)
                    ·
                      refine ⟨4075321371313023014949971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43470094627338912159466357 4075321371313023014949971)
                      ·
                        rfl

theorem cell23_7936660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7936660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936660 prefixEnd_7936660 := by exact prefixLift 7936660
  have htrace : WordTrace (prefixWord ++ tailWord_7936660) baseStart_7936660 baseEnd_7936660 := by
    simpa [prefixWord, tailWord_7936660, baseEnd_7936660] using wordTrace_append hprefix tailTrace_7936660
  have hstable : (prefixWord ++ tailWord_7936660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936660).length < 2 ^ (prefixWord ++ tailWord_7936660).sum := by decide
  have hdescent : baseEnd_7936660 < baseStart_7936660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936687 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 4, 2, 2]
def baseStart_7936687 : Nat := 118140960795 + 7936687 * 2 ^ 59
def prefixEnd_7936687 : Nat := 4983230072969 + 3 ^ 40 * 7936687 * 2
def baseEnd_7936687 : Nat := 4075335235290694409312347

theorem tailTrace_7936687 : CollatzResearch.WordTrace tailWord_7936687 prefixEnd_7936687 4075335235290694409312347 := by
  unfold tailWord_7936687
  simp only [CollatzResearch.WordTrace]
  refine ⟨289474756197745952069576315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192983170798497301379717543 289474756197745952069576315)
  ·
    refine ⟨434212134296618928104364473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289474756197745952069576315 434212134296618928104364473)
    ·
      refine ⟨325659100722464196078273355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434212134296618928104364473 325659100722464196078273355)
      ·
        refine ⟨488488651083696294117410033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325659100722464196078273355 488488651083696294117410033)
        ·
          refine ⟨366366488312772220588057525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488488651083696294117410033 366366488312772220588057525)
          ·
            refine ⟨34346858279322395680130393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366366488312772220588057525 34346858279322395680130393)
            ·
              refine ⟨25760143709491796760097795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34346858279322395680130393 25760143709491796760097795)
              ·
                refine ⟨38640215564237695140146693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25760143709491796760097795 38640215564237695140146693)
                ·
                  refine ⟨7245040418294567838777505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38640215564237695140146693 7245040418294567838777505)
                  ·
                    refine ⟨5433780313720925879083129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7245040418294567838777505 5433780313720925879083129)
                    ·
                      refine ⟨4075335235290694409312347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433780313720925879083129 4075335235290694409312347)
                      ·
                        rfl

theorem cell23_7936687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 2, 2].length) (baseStart_7936687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936687 prefixEnd_7936687 := by exact prefixLift 7936687
  have htrace : WordTrace (prefixWord ++ tailWord_7936687) baseStart_7936687 baseEnd_7936687 := by
    simpa [prefixWord, tailWord_7936687, baseEnd_7936687] using wordTrace_append hprefix tailTrace_7936687
  have hstable : (prefixWord ++ tailWord_7936687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936687).length < 2 ^ (prefixWord ++ tailWord_7936687).sum := by decide
  have hdescent : baseEnd_7936687 < baseStart_7936687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936704 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 2, 2, 2]
def baseStart_7936704 : Nat := 118140960795 + 7936704 * 2 ^ 59
def prefixEnd_7936704 : Nat := 4983230072969 + 3 ^ 40 * 7936704 * 2
def baseEnd_7936704 : Nat := 4075343964461820842799769

theorem tailTrace_7936704 : CollatzResearch.WordTrace tailWord_7936704 prefixEnd_7936704 4075343964461820842799769 := by
  unfold tailWord_7936704
  simp only [CollatzResearch.WordTrace]
  refine ⟨144737688119342181986472583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192983584159122909315296777 144737688119342181986472583)
  ·
    refine ⟨217106532179013272979708875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144737688119342181986472583 217106532179013272979708875)
    ·
      refine ⟨325659798268519909469563313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217106532179013272979708875 325659798268519909469563313)
      ·
        refine ⟨244244848701389932102172485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325659798268519909469563313 244244848701389932102172485)
        ·
          refine ⟨45795909131510612269157341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244244848701389932102172485 45795909131510612269157341)
          ·
            refine ⟨17173465924316479600934003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45795909131510612269157341 17173465924316479600934003)
            ·
              refine ⟨25760198886474719401401005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17173465924316479600934003 25760198886474719401401005)
              ·
                refine ⟨9660074582428019775525377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25760198886474719401401005 9660074582428019775525377)
                ·
                  refine ⟨7245055936821014831644033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9660074582428019775525377 7245055936821014831644033)
                  ·
                    refine ⟨5433791952615761123733025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7245055936821014831644033 5433791952615761123733025)
                    ·
                      refine ⟨4075343964461820842799769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433791952615761123733025 4075343964461820842799769)
                      ·
                        rfl

theorem cell23_7936704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_7936704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936704 prefixEnd_7936704 := by exact prefixLift 7936704
  have htrace : WordTrace (prefixWord ++ tailWord_7936704) baseStart_7936704 baseEnd_7936704 := by
    simpa [prefixWord, tailWord_7936704, baseEnd_7936704] using wordTrace_append hprefix tailTrace_7936704
  have hstable : (prefixWord ++ tailWord_7936704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936704).length < 2 ^ (prefixWord ++ tailWord_7936704).sum := by decide
  have hdescent : baseEnd_7936704 < baseStart_7936704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936740 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_7936740 : Nat := 118140960795 + 7936740 * 2 ^ 59
def prefixEnd_7936740 : Nat := 4983230072969 + 3 ^ 40 * 7936740 * 2
def baseEnd_7936740 : Nat := 1358454149921794233983201

theorem tailTrace_7936740 : CollatzResearch.WordTrace tailWord_7936740 prefixEnd_7936740 1358454149921794233983201 := by
  unfold tailWord_7936740
  simp only [CollatzResearch.WordTrace]
  refine ⟨144738344633276971060627837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192984459511035961414170449 144738344633276971060627837)
  ·
    refine ⟨54276879237478864147735439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144738344633276971060627837 54276879237478864147735439)
    ·
      refine ⟨81415318856218296221603159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54276879237478864147735439 81415318856218296221603159)
      ·
        refine ⟨122122978284327444332404739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81415318856218296221603159 122122978284327444332404739)
        ·
          refine ⟨183184467426491166498607109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122122978284327444332404739 183184467426491166498607109)
          ·
            refine ⟨34347087642467093718488833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183184467426491166498607109 34347087642467093718488833)
            ·
              refine ⟨25760315731850320288866625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34347087642467093718488833 25760315731850320288866625)
              ·
                refine ⟨19320236798887740216649969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25760315731850320288866625 19320236798887740216649969)
                ·
                  refine ⟨14490177599165805162487477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19320236798887740216649969 14490177599165805162487477)
                  ·
                    refine ⟨1358454149921794233983201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14490177599165805162487477 1358454149921794233983201)
                    ·
                      rfl

theorem cell23_7936740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_7936740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936740 prefixEnd_7936740 := by exact prefixLift 7936740
  have htrace : WordTrace (prefixWord ++ tailWord_7936740) baseStart_7936740 baseEnd_7936740 := by
    simpa [prefixWord, tailWord_7936740, baseEnd_7936740] using wordTrace_append hprefix tailTrace_7936740
  have hstable : (prefixWord ++ tailWord_7936740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936740).length < 2 ^ (prefixWord ++ tailWord_7936740).sum := by decide
  have hdescent : baseEnd_7936740 < baseStart_7936740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936750 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7936750 : Nat := 118140960795 + 7936750 * 2 ^ 59
def prefixEnd_7936750 : Nat := 4983230072969 + 3 ^ 40 * 7936750 * 2
def baseEnd_7936750 : Nat := 4075367584571927662824557

theorem tailTrace_7936750 : CollatzResearch.WordTrace tailWord_7936750 prefixEnd_7936750 4075367584571927662824557 := by
  unfold tailWord_7936750
  simp only [CollatzResearch.WordTrace]
  refine ⟨36184631749564714228639963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192984702664345142552746469 36184631749564714228639963)
  ·
    refine ⟨54276947624347071342959945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36184631749564714228639963 54276947624347071342959945)
    ·
      refine ⟨40707710718260303507219959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54276947624347071342959945 40707710718260303507219959)
      ·
        refine ⟨61061566077390455260829939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40707710718260303507219959 61061566077390455260829939)
        ·
          refine ⟨91592349116085682891244909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61061566077390455260829939 91592349116085682891244909)
          ·
            refine ⟨34347130918532131084216841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91592349116085682891244909 34347130918532131084216841)
            ·
              refine ⟨25760348188899098313162631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34347130918532131084216841 25760348188899098313162631)
              ·
                refine ⟨38640522283348647469743947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25760348188899098313162631 38640522283348647469743947)
                ·
                  refine ⟨57960783425022971204615921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38640522283348647469743947 57960783425022971204615921)
                  ·
                    refine ⟨43470587568767228403461941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57960783425022971204615921 43470587568767228403461941)
                    ·
                      refine ⟨4075367584571927662824557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43470587568767228403461941 4075367584571927662824557)
                      ·
                        rfl

theorem cell23_7936750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7936750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936750 prefixEnd_7936750 := by exact prefixLift 7936750
  have htrace : WordTrace (prefixWord ++ tailWord_7936750) baseStart_7936750 baseEnd_7936750 := by
    simpa [prefixWord, tailWord_7936750, baseEnd_7936750] using wordTrace_append hprefix tailTrace_7936750
  have hstable : (prefixWord ++ tailWord_7936750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936750).length < 2 ^ (prefixWord ++ tailWord_7936750).sum := by decide
  have hdescent : baseEnd_7936750 < baseStart_7936750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936773 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_7936773 : Nat := 118140960795 + 7936773 * 2 ^ 59
def prefixEnd_7936773 : Nat := 4983230072969 + 3 ^ 40 * 7936773 * 2
def baseEnd_7936773 : Nat := 4075379394626981072836951

theorem tailTrace_7936773 : CollatzResearch.WordTrace tailWord_7936773 prefixEnd_7936773 4075379394626981072836951 := by
  unfold tailWord_7936773
  simp only [CollatzResearch.WordTrace]
  refine ⟨289477892875434388757206973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192985261916956259171471315 289477892875434388757206973)
  ·
    refine ⟨108554209828287895783952615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289477892875434388757206973 108554209828287895783952615)
    ·
      refine ⟨162831314742431843675928923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108554209828287895783952615 162831314742431843675928923)
      ·
        refine ⟨244246972113647765513893385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162831314742431843675928923 244246972113647765513893385)
        ·
          refine ⟨183185229085235824135420039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244246972113647765513893385 183185229085235824135420039)
          ·
            refine ⟨274777843627853736203130059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183185229085235824135420039 274777843627853736203130059)
            ·
              refine ⟨412166765441780604304695089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274777843627853736203130059 412166765441780604304695089)
              ·
                refine ⟨309125074081335453228521317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412166765441780604304695089 309125074081335453228521317)
                ·
                  refine ⟨57960951390250397480347747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309125074081335453228521317 57960951390250397480347747)
                  ·
                    refine ⟨86941427085375596220521621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57960951390250397480347747 86941427085375596220521621)
                    ·
                      refine ⟨4075379394626981072836951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86941427085375596220521621 4075379394626981072836951)
                      ·
                        rfl

theorem cell23_7936773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_7936773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936773 prefixEnd_7936773 := by exact prefixLift 7936773
  have htrace : WordTrace (prefixWord ++ tailWord_7936773) baseStart_7936773 baseEnd_7936773 := by
    simpa [prefixWord, tailWord_7936773, baseEnd_7936773] using wordTrace_append hprefix tailTrace_7936773
  have hstable : (prefixWord ++ tailWord_7936773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936773).length < 2 ^ (prefixWord ++ tailWord_7936773).sum := by decide
  have hdescent : baseEnd_7936773 < baseStart_7936773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936783 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 8]
def baseStart_7936783 : Nat := 118140960795 + 7936783 * 2 ^ 59
def prefixEnd_7936783 : Nat := 4983230072969 + 3 ^ 40 * 7936783 * 2
def baseEnd_7936783 : Nat := 452820503270391781523545

theorem tailTrace_7936783 : CollatzResearch.WordTrace tailWord_7936783 prefixEnd_7936783 452820503270391781523545 := by
  unfold tailWord_7936783
  simp only [CollatzResearch.WordTrace]
  refine ⟨289478257605398160465071003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192985505070265440310047335 289478257605398160465071003)
  ·
    refine ⟨434217386408097240697606505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289478257605398160465071003 434217386408097240697606505)
    ·
      refine ⟨325663039806072930523204879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434217386408097240697606505 325663039806072930523204879)
      ·
        refine ⟨488494559709109395784807319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325663039806072930523204879 488494559709109395784807319)
        ·
          refine ⟨732741839563664093677210979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488494559709109395784807319 732741839563664093677210979)
          ·
            refine ⟨1099112759345496140515816469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732741839563664093677210979 1099112759345496140515816469)
            ·
              refine ⟨51520910594320131586678897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1099112759345496140515816469 51520910594320131586678897)
              ·
                refine ⟨38640682945740098690009173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51520910594320131586678897 38640682945740098690009173)
                ·
                  refine ⟨452820503270391781523545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38640682945740098690009173 452820503270391781523545)
                  ·
                    rfl

theorem cell23_7936783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 8].length) (baseStart_7936783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936783 prefixEnd_7936783 := by exact prefixLift 7936783
  have htrace : WordTrace (prefixWord ++ tailWord_7936783) baseStart_7936783 baseEnd_7936783 := by
    simpa [prefixWord, tailWord_7936783, baseEnd_7936783] using wordTrace_append hprefix tailTrace_7936783
  have hstable : (prefixWord ++ tailWord_7936783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936783).length < 2 ^ (prefixWord ++ tailWord_7936783).sum := by decide
  have hdescent : baseEnd_7936783 < baseStart_7936783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936800 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 8]
def baseStart_7936800 : Nat := 118140960795 + 7936800 * 2 ^ 59
def prefixEnd_7936800 : Nat := 4983230072969 + 3 ^ 40 * 7936800 * 2
def baseEnd_7936800 : Nat := 452821473178294718577703

theorem tailTrace_7936800 : CollatzResearch.WordTrace tailWord_7936800 prefixEnd_7936800 452821473178294718577703 := by
  unfold tailWord_7936800
  simp only [CollatzResearch.WordTrace]
  refine ⟨144739438823168286184219927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192985918430891048245626569 144739438823168286184219927)
  ·
    refine ⟨217109158234752429276329891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144739438823168286184219927 217109158234752429276329891)
    ·
      refine ⟨325663737352128643914494837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217109158234752429276329891 325663737352128643914494837)
      ·
        refine ⟨30530975376762060366983891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325663737352128643914494837 30530975376762060366983891)
        ·
          refine ⟨45796463065143090550475837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30530975376762060366983891 45796463065143090550475837)
          ·
            refine ⟨17173673649428658956428439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45796463065143090550475837 17173673649428658956428439)
            ·
              refine ⟨25760510474142988434642659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17173673649428658956428439 25760510474142988434642659)
              ·
                refine ⟨38640765711214482651963989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25760510474142988434642659 38640765711214482651963989)
                ·
                  refine ⟨452821473178294718577703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38640765711214482651963989 452821473178294718577703)
                  ·
                    rfl

theorem cell23_7936800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_7936800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936800 prefixEnd_7936800 := by exact prefixLift 7936800
  have htrace : WordTrace (prefixWord ++ tailWord_7936800) baseStart_7936800 baseEnd_7936800 := by
    simpa [prefixWord, tailWord_7936800, baseEnd_7936800] using wordTrace_append hprefix tailTrace_7936800
  have hstable : (prefixWord ++ tailWord_7936800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936800).length < 2 ^ (prefixWord ++ tailWord_7936800).sum := by decide
  have hdescent : baseEnd_7936800 < baseStart_7936800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936804 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_7936804 : Nat := 118140960795 + 7936804 * 2 ^ 59
def prefixEnd_7936804 : Nat := 4983230072969 + 3 ^ 40 * 7936804 * 2
def baseEnd_7936804 : Nat := 1358465104175756817183103

theorem tailTrace_7936804 : CollatzResearch.WordTrace tailWord_7936804 prefixEnd_7936804 1358465104175756817183103 := by
  unfold tailWord_7936804
  simp only [CollatzResearch.WordTrace]
  refine ⟨144739511769161040525792733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192986015692214720701056977 144739511769161040525792733)
  ·
    refine ⟨54277316913435390197172275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144739511769161040525792733 54277316913435390197172275)
    ·
      refine ⟨81415975370153085295758413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54277316913435390197172275 81415975370153085295758413)
      ·
        refine ⟨30530990763807406985909405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81415975370153085295758413 30530990763807406985909405)
        ·
          refine ⟨11449121536427777619716027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30530990763807406985909405 11449121536427777619716027)
          ·
            refine ⟨17173682304641666429574041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449121536427777619716027 17173682304641666429574041)
            ·
              refine ⟨12880261728481249822180531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17173682304641666429574041 12880261728481249822180531)
              ·
                refine ⟨19320392592721874733270797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12880261728481249822180531 19320392592721874733270797)
                ·
                  refine ⟨7245147222270703024976549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19320392592721874733270797 7245147222270703024976549)
                  ·
                    refine ⟨1358465104175756817183103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7245147222270703024976549 1358465104175756817183103)
                    ·
                      rfl

theorem cell23_7936804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_7936804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936804 prefixEnd_7936804 := by exact prefixLift 7936804
  have htrace : WordTrace (prefixWord ++ tailWord_7936804) baseStart_7936804 baseEnd_7936804 := by
    simpa [prefixWord, tailWord_7936804, baseEnd_7936804] using wordTrace_append hprefix tailTrace_7936804
  have hstable : (prefixWord ++ tailWord_7936804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936804).length < 2 ^ (prefixWord ++ tailWord_7936804).sum := by decide
  have hdescent : baseEnd_7936804 < baseStart_7936804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936817 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 6]
def baseStart_7936817 : Nat := 118140960795 + 7936817 * 2 ^ 59
def prefixEnd_7936817 : Nat := 4983230072969 + 3 ^ 40 * 7936817 * 2
def baseEnd_7936817 : Nat := 452822443086197655631861

theorem tailTrace_7936817 : CollatzResearch.WordTrace tailWord_7936817 prefixEnd_7936817 452822443086197655631861 := by
  unfold tailWord_7936817
  simp only [CollatzResearch.WordTrace]
  refine ⟨289479497687274984271808705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192986331791516656181205803 289479497687274984271808705)
  ·
    refine ⟨217109623265456238203856529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289479497687274984271808705 217109623265456238203856529)
    ·
      refine ⟨162832217449092178652892397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217109623265456238203856529 162832217449092178652892397)
      ·
        refine ⟨61062081543409566994834649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162832217449092178652892397 61062081543409566994834649)
        ·
          refine ⟨45796561157557175246125987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61062081543409566994834649 45796561157557175246125987)
          ·
            refine ⟨68694841736335762869188981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45796561157557175246125987 68694841736335762869188981)
            ·
              refine ⟨6440141412781477768986467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68694841736335762869188981 6440141412781477768986467)
              ·
                refine ⟨9660212119172216653479701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440141412781477768986467 9660212119172216653479701)
                ·
                  refine ⟨452822443086197655631861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9660212119172216653479701 452822443086197655631861)
                  ·
                    rfl

theorem cell23_7936817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 6].length) (baseStart_7936817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936817 prefixEnd_7936817 := by exact prefixLift 7936817
  have htrace : WordTrace (prefixWord ++ tailWord_7936817) baseStart_7936817 baseEnd_7936817 := by
    simpa [prefixWord, tailWord_7936817, baseEnd_7936817] using wordTrace_append hprefix tailTrace_7936817
  have hstable : (prefixWord ++ tailWord_7936817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936817).length < 2 ^ (prefixWord ++ tailWord_7936817).sum := by decide
  have hdescent : baseEnd_7936817 < baseStart_7936817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936880 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_7936880 : Nat := 118140960795 + 7936880 * 2 ^ 59
def prefixEnd_7936880 : Nat := 4983230072969 + 3 ^ 40 * 7936880 * 2
def baseEnd_7936880 : Nat := 4075434337057012154198959

theorem tailTrace_7936880 : CollatzResearch.WordTrace tailWord_7936880 prefixEnd_7936880 4075434337057012154198959 := by
  unfold tailWord_7936880
  simp only [CollatzResearch.WordTrace]
  refine ⟨144740897743023373015676047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192987863657364497354234729 144740897743023373015676047)
  ·
    refine ⟨217111346614535059523514071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144740897743023373015676047 217111346614535059523514071)
    ·
      refine ⟨325667019921802589285271107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217111346614535059523514071 325667019921802589285271107)
      ·
        refine ⟨488500529882703883927906661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325667019921802589285271107 488500529882703883927906661)
        ·
          refine ⟨91593849353006978236482499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488500529882703883927906661 91593849353006978236482499)
          ·
            refine ⟨137390774029510467354723749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91593849353006978236482499 137390774029510467354723749)
            ·
              refine ⟨25760770130533212629010703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137390774029510467354723749 25760770130533212629010703)
              ·
                refine ⟨38641155195799818943516055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25760770130533212629010703 38641155195799818943516055)
                ·
                  refine ⟨57961732793699728415274083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38641155195799818943516055 57961732793699728415274083)
                  ·
                    refine ⟨86942599190549592622911125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57961732793699728415274083 86942599190549592622911125)
                    ·
                      refine ⟨4075434337057012154198959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86942599190549592622911125 4075434337057012154198959)
                      ·
                        rfl

theorem cell23_7936880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_7936880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936880 prefixEnd_7936880 := by exact prefixLift 7936880
  have htrace : WordTrace (prefixWord ++ tailWord_7936880) baseStart_7936880 baseEnd_7936880 := by
    simpa [prefixWord, tailWord_7936880, baseEnd_7936880] using wordTrace_append hprefix tailTrace_7936880
  have hstable : (prefixWord ++ tailWord_7936880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936880).length < 2 ^ (prefixWord ++ tailWord_7936880).sum := by decide
  have hdescent : baseEnd_7936880 < baseStart_7936880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936904 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7936904 : Nat := 118140960795 + 7936904 * 2 ^ 59
def prefixEnd_7936904 : Nat := 4983230072969 + 3 ^ 40 * 7936904 * 2
def baseEnd_7936904 : Nat := 4075446660592720060298849

theorem tailTrace_7936904 : CollatzResearch.WordTrace tailWord_7936904 prefixEnd_7936904 4075446660592720060298849 := by
  unfold tailWord_7936904
  simp only [CollatzResearch.WordTrace]
  refine ⟨144741335418979899065112883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192988447225306532086817177 144741335418979899065112883)
  ·
    refine ⟨217112003128469848597669325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144741335418979899065112883 217112003128469848597669325)
    ·
      refine ⟨81417001173176193224125997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217112003128469848597669325 81417001173176193224125997)
      ·
        refine ⟨30531375439941072459047249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81417001173176193224125997 30531375439941072459047249)
        ·
          refine ⟨22898531579955804344285437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30531375439941072459047249 22898531579955804344285437)
          ·
            refine ⟨8586949342483426629107039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22898531579955804344285437 8586949342483426629107039)
            ·
              refine ⟨12880424013725139943660559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8586949342483426629107039 12880424013725139943660559)
              ·
                refine ⟨19320636020587709915490839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12880424013725139943660559 19320636020587709915490839)
                ·
                  refine ⟨28980954030881564873236259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19320636020587709915490839 28980954030881564873236259)
                  ·
                    refine ⟨43471431046322347309854389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28980954030881564873236259 43471431046322347309854389)
                    ·
                      refine ⟨4075446660592720060298849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43471431046322347309854389 4075446660592720060298849)
                      ·
                        rfl

theorem cell23_7936904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7936904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936904 prefixEnd_7936904 := by exact prefixLift 7936904
  have htrace : WordTrace (prefixWord ++ tailWord_7936904) baseStart_7936904 baseEnd_7936904 := by
    simpa [prefixWord, tailWord_7936904, baseEnd_7936904] using wordTrace_append hprefix tailTrace_7936904
  have hstable : (prefixWord ++ tailWord_7936904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936904).length < 2 ^ (prefixWord ++ tailWord_7936904).sum := by decide
  have hdescent : baseEnd_7936904 < baseStart_7936904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936924 : List Nat := [2, 2, 3, 3, 2, 2, 1, 8]
def baseStart_7936924 : Nat := 118140960795 + 7936924 * 2 ^ 59
def prefixEnd_7936924 : Nat := 4983230072969 + 3 ^ 40 * 7936924 * 2
def baseEnd_7936924 : Nat := 150942849266881851186991

theorem tailTrace_7936924 : CollatzResearch.WordTrace tailWord_7936924 prefixEnd_7936924 150942849266881851186991 := by
  unfold tailWord_7936924
  simp only [CollatzResearch.WordTrace]
  refine ⟨144741700148943670772976913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192988933531924894363969217 144741700148943670772976913)
  ·
    refine ⟨108556275111707753079732685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144741700148943670772976913 108556275111707753079732685)
    ·
      refine ⟨40708603166890407404899757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108556275111707753079732685 40708603166890407404899757)
      ·
        refine ⟨15265726187583902776837409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40708603166890407404899757 15265726187583902776837409)
        ·
          refine ⟨11449294640687927082628057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15265726187583902776837409 11449294640687927082628057)
          ·
            refine ⟨8586970980515945311971043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11449294640687927082628057 8586970980515945311971043)
            ·
              refine ⟨12880456470773917967956565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8586970980515945311971043 12880456470773917967956565)
              ·
                refine ⟨150942849266881851186991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12880456470773917967956565 150942849266881851186991)
                ·
                  rfl

theorem cell23_7936924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 8].length) (baseStart_7936924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936924 prefixEnd_7936924 := by exact prefixLift 7936924
  have htrace : WordTrace (prefixWord ++ tailWord_7936924) baseStart_7936924 baseEnd_7936924 := by
    simpa [prefixWord, tailWord_7936924, baseEnd_7936924] using wordTrace_append hprefix tailTrace_7936924
  have hstable : (prefixWord ++ tailWord_7936924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936924).length < 2 ^ (prefixWord ++ tailWord_7936924).sum := by decide
  have hdescent : baseEnd_7936924 < baseStart_7936924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936941 : List Nat := [1, 5, 2, 3, 1, 1, 3, 7]
def baseStart_7936941 : Nat := 118140960795 + 7936941 * 2 ^ 59
def prefixEnd_7936941 : Nat := 4983230072969 + 3 ^ 40 * 7936941 * 2
def baseEnd_7936941 : Nat := 150943172569516163538377

theorem tailTrace_7936941 : CollatzResearch.WordTrace tailWord_7936941 prefixEnd_7936941 150943172569516163538377 := by
  unfold tailWord_7936941
  simp only [CollatzResearch.WordTrace]
  refine ⟨289484020338825753449322677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192989346892550502299548451 289484020338825753449322677)
  ·
    refine ⟨27139126906764914385874001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289484020338825753449322677 27139126906764914385874001)
    ·
      refine ⟨20354345180073685789405501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27139126906764914385874001 20354345180073685789405501)
      ·
        refine ⟨7632879442527632171027063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20354345180073685789405501 7632879442527632171027063)
        ·
          refine ⟨11449319163791448256540595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632879442527632171027063 11449319163791448256540595)
          ·
            refine ⟨17173978745687172384810893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449319163791448256540595 17173978745687172384810893)
            ·
              refine ⟨6440242029632689644304085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17173978745687172384810893 6440242029632689644304085)
              ·
                refine ⟨150943172569516163538377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6440242029632689644304085 150943172569516163538377)
                ·
                  rfl

theorem cell23_7936941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 7].length) (baseStart_7936941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936941 prefixEnd_7936941 := by exact prefixLift 7936941
  have htrace : WordTrace (prefixWord ++ tailWord_7936941) baseStart_7936941 baseEnd_7936941 := by
    simpa [prefixWord, tailWord_7936941, baseEnd_7936941] using wordTrace_append hprefix tailTrace_7936941
  have hstable : (prefixWord ++ tailWord_7936941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936941).length < 2 ^ (prefixWord ++ tailWord_7936941).sum := by decide
  have hdescent : baseEnd_7936941 < baseStart_7936941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936968 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_7936968 : Nat := 118140960795 + 7936968 * 2 ^ 59
def prefixEnd_7936968 : Nat := 4983230072969 + 3 ^ 40 * 7936968 * 2
def baseEnd_7936968 : Nat := 4075479523354607809898555

theorem tailTrace_7936968 : CollatzResearch.WordTrace tailWord_7936968 prefixEnd_7936968 4075479523354607809898555 := by
  unfold tailWord_7936968
  simp only [CollatzResearch.WordTrace]
  refine ⟨144742502554863968530277779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192990003406485291373703705 144742502554863968530277779)
  ·
    refine ⟨217113753832295952795416669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144742502554863968530277779 217113753832295952795416669)
    ·
      refine ⟨81417657687110982298281251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217113753832295952795416669 81417657687110982298281251)
      ·
        refine ⟨122126486530666473447421877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81417657687110982298281251 122126486530666473447421877)
        ·
          refine ⟨11449358112249981885695801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122126486530666473447421877 11449358112249981885695801)
          ·
            refine ⟨8587018584187486414271851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11449358112249981885695801 8587018584187486414271851)
            ·
              refine ⟨12880527876281229621407777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587018584187486414271851 12880527876281229621407777)
              ·
                refine ⟨9660395907210922216055833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12880527876281229621407777 9660395907210922216055833)
                ·
                  refine ⟨7245296930408191662041875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9660395907210922216055833 7245296930408191662041875)
                  ·
                    refine ⟨10867945395612287493062813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7245296930408191662041875 10867945395612287493062813)
                    ·
                      refine ⟨4075479523354607809898555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10867945395612287493062813 4075479523354607809898555)
                      ·
                        rfl

theorem cell23_7936968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_7936968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936968 prefixEnd_7936968 := by exact prefixLift 7936968
  have htrace : WordTrace (prefixWord ++ tailWord_7936968) baseStart_7936968 baseEnd_7936968 := by
    simpa [prefixWord, tailWord_7936968, baseEnd_7936968] using wordTrace_append hprefix tailTrace_7936968
  have hstable : (prefixWord ++ tailWord_7936968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936968).length < 2 ^ (prefixWord ++ tailWord_7936968).sum := by decide
  have hdescent : baseEnd_7936968 < baseStart_7936968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937031 : List Nat := [1, 1, 4, 3, 1, 1, 5, 2, 5]
def baseStart_7937031 : Nat := 118140960795 + 7937031 * 2 ^ 59
def prefixEnd_7937031 : Nat := 4983230072969 + 3 ^ 40 * 7937031 * 2
def baseEnd_7937031 : Nat := 452834652515093451490085

theorem tailTrace_7937031 : CollatzResearch.WordTrace tailWord_7937031 prefixEnd_7937031 452834652515093451490085 := by
  unfold tailWord_7937031
  simp only [CollatzResearch.WordTrace]
  refine ⟨289487302908499698820098947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192991535272333132546732631 289487302908499698820098947)
  ·
    refine ⟨434230954362749548230148421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289487302908499698820098947 434230954362749548230148421)
    ·
      refine ⟨81418303943015540293152829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434230954362749548230148421 81418303943015540293152829)
      ·
        refine ⟨30531863978630827609932311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81418303943015540293152829 30531863978630827609932311)
        ·
          refine ⟨45797795967946241414898467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30531863978630827609932311 45797795967946241414898467)
          ·
            refine ⟨68696693951919362122347701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45797795967946241414898467 68696693951919362122347701)
            ·
              refine ⟨6440315057992440198970097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68696693951919362122347701 6440315057992440198970097)
              ·
                refine ⟨4830236293494330149227573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440315057992440198970097 4830236293494330149227573)
                ·
                  refine ⟨452834652515093451490085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4830236293494330149227573 452834652515093451490085)
                  ·
                    rfl

theorem cell23_7937031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 5].length) (baseStart_7937031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937031 prefixEnd_7937031 := by exact prefixLift 7937031
  have htrace : WordTrace (prefixWord ++ tailWord_7937031) baseStart_7937031 baseEnd_7937031 := by
    simpa [prefixWord, tailWord_7937031, baseEnd_7937031] using wordTrace_append hprefix tailTrace_7937031
  have hstable : (prefixWord ++ tailWord_7937031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937031).length < 2 ^ (prefixWord ++ tailWord_7937031).sum := by decide
  have hdescent : baseEnd_7937031 < baseStart_7937031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937077 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7937077 : Nat := 118140960795 + 7937077 * 2 ^ 59
def prefixEnd_7937077 : Nat := 4983230072969 + 3 ^ 40 * 7937077 * 2
def baseEnd_7937077 : Nat := 4075535492745947883435553

theorem tailTrace_7937077 : CollatzResearch.WordTrace tailWord_7937077 prefixEnd_7937077 4075535492745947883435553 := by
  unfold tailWord_7937077
  simp only [CollatzResearch.WordTrace]
  refine ⟨289488980666333048676273485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192992653777555365784182323 289488980666333048676273485)
  ·
    refine ⟨108558367749874893253602557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289488980666333048676273485 108558367749874893253602557)
    ·
      refine ⟨40709387906203084970100959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108558367749874893253602557 40709387906203084970100959)
      ·
        refine ⟨61064081859304627455151439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40709387906203084970100959 61064081859304627455151439)
        ·
          refine ⟨91596122788956941182727159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61064081859304627455151439 91596122788956941182727159)
          ·
            refine ⟨137394184183435411774090739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91596122788956941182727159 137394184183435411774090739)
            ·
              refine ⟨206091276275153117661136109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137394184183435411774090739 206091276275153117661136109)
              ·
                refine ⟨77284228603182419122926041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206091276275153117661136109 77284228603182419122926041)
                ·
                  refine ⟨57963171452386814342194531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77284228603182419122926041 57963171452386814342194531)
                  ·
                    refine ⟨86944757178580221513291797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57963171452386814342194531 86944757178580221513291797)
                    ·
                      refine ⟨4075535492745947883435553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86944757178580221513291797 4075535492745947883435553)
                      ·
                        rfl

theorem cell23_7937077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7937077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937077 prefixEnd_7937077 := by exact prefixLift 7937077
  have htrace : WordTrace (prefixWord ++ tailWord_7937077) baseStart_7937077 baseEnd_7937077 := by
    simpa [prefixWord, tailWord_7937077, baseEnd_7937077] using wordTrace_append hprefix tailTrace_7937077
  have hstable : (prefixWord ++ tailWord_7937077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937077).length < 2 ^ (prefixWord ++ tailWord_7937077).sum := by decide
  have hdescent : baseEnd_7937077 < baseStart_7937077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937091 : List Nat := [1, 1, 1, 3, 1, 2, 5, 4, 1, 4]
def baseStart_7937091 : Nat := 118140960795 + 7937091 * 2 ^ 59
def prefixEnd_7937091 : Nat := 4983230072969 + 3 ^ 40 * 7937091 * 2
def baseEnd_7937091 : Nat := 1358514227158370276220163

theorem tailTrace_7937091 : CollatzResearch.WordTrace tailWord_7937091 prefixEnd_7937091 1358514227158370276220163 := by
  unfold tailWord_7937091
  simp only [CollatzResearch.WordTrace]
  refine ⟨289489491288282329067283127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192992994192188219378188751 289489491288282329067283127)
  ·
    refine ⟨434234236932423493600924691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289489491288282329067283127 434234236932423493600924691)
    ·
      refine ⟨651351355398635240401387037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434234236932423493600924691 651351355398635240401387037)
      ·
        refine ⟨244256758274488215150520139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651351355398635240401387037 244256758274488215150520139)
        ·
          refine ⟨366385137411732322725780209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244256758274488215150520139 366385137411732322725780209)
          ·
            refine ⟨274788853058799242044335157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366385137411732322725780209 274788853058799242044335157)
            ·
              refine ⟨25761454974262428941656421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274788853058799242044335157 25761454974262428941656421)
              ·
                refine ⟨4830272807674205426560579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25761454974262428941656421 4830272807674205426560579)
                ·
                  refine ⟨7245409211511308139840869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830272807674205426560579 7245409211511308139840869)
                  ·
                    refine ⟨1358514227158370276220163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7245409211511308139840869 1358514227158370276220163)
                    ·
                      rfl

theorem cell23_7937091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 4].length) (baseStart_7937091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937091 prefixEnd_7937091 := by exact prefixLift 7937091
  have htrace : WordTrace (prefixWord ++ tailWord_7937091) baseStart_7937091 baseEnd_7937091 := by
    simpa [prefixWord, tailWord_7937091, baseEnd_7937091] using wordTrace_append hprefix tailTrace_7937091
  have hstable : (prefixWord ++ tailWord_7937091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937091).length < 2 ^ (prefixWord ++ tailWord_7937091).sum := by decide
  have hdescent : baseEnd_7937091 < baseStart_7937091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937147 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 3, 6]
def baseStart_7937147 : Nat := 118140960795 + 7937147 * 2 ^ 59
def prefixEnd_7937147 : Nat := 4983230072969 + 3 ^ 40 * 7937147 * 2
def baseEnd_7937147 : Nat := 1358523812130587536520077

theorem tailTrace_7937147 : CollatzResearch.WordTrace tailWord_7937147 prefixEnd_7937147 1358523812130587536520077 := by
  unfold tailWord_7937147
  simp only [CollatzResearch.WordTrace]
  refine ⟨289491533776079450631321695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192994355850719633754214463 289491533776079450631321695)
  ·
    refine ⟨434237300664119175946982543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289491533776079450631321695 434237300664119175946982543)
    ·
      refine ⟨651355950996178763920473815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434237300664119175946982543 651355950996178763920473815)
      ·
        refine ⟨977033926494268145880710723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651355950996178763920473815 977033926494268145880710723)
        ·
          refine ⟨1465550889741402218821066085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977033926494268145880710723 1465550889741402218821066085)
          ·
            refine ⟨274790791826512916028949891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1465550889741402218821066085 274790791826512916028949891)
            ·
              refine ⟨412186187739769374043424837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274790791826512916028949891 412186187739769374043424837)
              ·
                refine ⟨77284910201206757633142157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412186187739769374043424837 77284910201206757633142157)
                ·
                  refine ⟨28981841325452534112428309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77284910201206757633142157 28981841325452534112428309)
                  ·
                    refine ⟨1358523812130587536520077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28981841325452534112428309 1358523812130587536520077)
                    ·
                      rfl

theorem cell23_7937147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 6].length) (baseStart_7937147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937147 prefixEnd_7937147 := by exact prefixLift 7937147
  have htrace : WordTrace (prefixWord ++ tailWord_7937147) baseStart_7937147 baseEnd_7937147 := by
    simpa [prefixWord, tailWord_7937147, baseEnd_7937147] using wordTrace_append hprefix tailTrace_7937147
  have hstable : (prefixWord ++ tailWord_7937147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937147).length < 2 ^ (prefixWord ++ tailWord_7937147).sum := by decide
  have hdescent : baseEnd_7937147 < baseStart_7937147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937148 : List Nat := [2, 2, 2, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_7937148 : Nat := 118140960795 + 7937148 * 2 ^ 59
def prefixEnd_7937148 : Nat := 4983230072969 + 3 ^ 40 * 7937148 * 2
def baseEnd_7937148 : Nat := 4075571949872417105647727

theorem tailTrace_7937148 : CollatzResearch.WordTrace tailWord_7937148 prefixEnd_7937148 4075571949872417105647727 := by
  unfold tailWord_7937148
  simp only [CollatzResearch.WordTrace]
  refine ⟨144745785124537913901054049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192994380166050551868072065 144745785124537913901054049)
  ·
    refine ⟨108559338843403435425790537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144745785124537913901054049 108559338843403435425790537)
    ·
      refine ⟨81419504132552576569342903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108559338843403435425790537 81419504132552576569342903)
      ·
        refine ⟨122129256198828864854014355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81419504132552576569342903 122129256198828864854014355)
        ·
          refine ⟨183193884298243297281021533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122129256198828864854014355 183193884298243297281021533)
          ·
            refine ⟨68697706611841236480383075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183193884298243297281021533 68697706611841236480383075)
            ·
              refine ⟨103046559917761854720574613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68697706611841236480383075 103046559917761854720574613)
              ·
                refine ⟨4830307496145086940026935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103046559917761854720574613 4830307496145086940026935)
                ·
                  refine ⟨7245461244217630410040403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830307496145086940026935 7245461244217630410040403)
                  ·
                    refine ⟨10868191866326445615060605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7245461244217630410040403 10868191866326445615060605)
                    ·
                      refine ⟨4075571949872417105647727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10868191866326445615060605 4075571949872417105647727)
                      ·
                        rfl

theorem cell23_7937148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_7937148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937148 prefixEnd_7937148 := by exact prefixLift 7937148
  have htrace : WordTrace (prefixWord ++ tailWord_7937148) baseStart_7937148 baseEnd_7937148 := by
    simpa [prefixWord, tailWord_7937148, baseEnd_7937148] using wordTrace_append hprefix tailTrace_7937148
  have hstable : (prefixWord ++ tailWord_7937148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937148).length < 2 ^ (prefixWord ++ tailWord_7937148).sum := by decide
  have hdescent : baseEnd_7937148 < baseStart_7937148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937182 : List Nat := [4, 3, 1, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_7937182 : Nat := 118140960795 + 7937182 * 2 ^ 59
def prefixEnd_7937182 : Nat := 4983230072969 + 3 ^ 40 * 7937182 * 2
def baseEnd_7937182 : Nat := 4075589408214669972622571

theorem tailTrace_7937182 : CollatzResearch.WordTrace tailWord_7937182 prefixEnd_7937182 4075589408214669972622571 := by
  unfold tailWord_7937182
  simp only [CollatzResearch.WordTrace]
  refine ⟨36186601291369081451105725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192995206887301767739230533 36186601291369081451105725)
  ·
    refine ⟨13569975484263405544164647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36186601291369081451105725 13569975484263405544164647)
    ·
      refine ⟨20354963226395108316246971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569975484263405544164647 20354963226395108316246971)
      ·
        refine ⟨30532444839592662474370457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20354963226395108316246971 30532444839592662474370457)
        ·
          refine ⟨22899333629694496855777843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30532444839592662474370457 22899333629694496855777843)
          ·
            refine ⟨34349000444541745283666765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22899333629694496855777843 34349000444541745283666765)
            ·
              refine ⟨12880875166703154481375037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34349000444541745283666765 12880875166703154481375037)
              ·
                refine ⟨4830328187513682930515639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12880875166703154481375037 4830328187513682930515639)
                ·
                  refine ⟨7245492281270524395773459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830328187513682930515639 7245492281270524395773459)
                  ·
                    refine ⟨10868238421905786593660189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7245492281270524395773459 10868238421905786593660189)
                    ·
                      refine ⟨4075589408214669972622571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10868238421905786593660189 4075589408214669972622571)
                      ·
                        rfl

theorem cell23_7937182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_7937182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937182 prefixEnd_7937182 := by exact prefixLift 7937182
  have htrace : WordTrace (prefixWord ++ tailWord_7937182) baseStart_7937182 baseEnd_7937182 := by
    simpa [prefixWord, tailWord_7937182, baseEnd_7937182] using wordTrace_append hprefix tailTrace_7937182
  have hstable : (prefixWord ++ tailWord_7937182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937182).length < 2 ^ (prefixWord ++ tailWord_7937182).sum := by decide
  have hdescent : baseEnd_7937182 < baseStart_7937182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937184 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_7937184 : Nat := 118140960795 + 7937184 * 2 ^ 59
def prefixEnd_7937184 : Nat := 4983230072969 + 3 ^ 40 * 7937184 * 2
def baseEnd_7937184 : Nat := 4075590435175978964797561

theorem tailTrace_7937184 : CollatzResearch.WordTrace tailWord_7937184 prefixEnd_7937184 4075590435175978964797561 := by
  unfold tailWord_7937184
  simp only [CollatzResearch.WordTrace]
  refine ⟨144746441638472702975209303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192995255517963603966945737 144746441638472702975209303)
  ·
    refine ⟨217119662457709054462813955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144746441638472702975209303 217119662457709054462813955)
    ·
      refine ⟨325679493686563581694220933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217119662457709054462813955 325679493686563581694220933)
      ·
        refine ⟨61064905066230671567666425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325679493686563581694220933 61064905066230671567666425)
        ·
          refine ⟨45798678799673003675749819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61064905066230671567666425 45798678799673003675749819)
          ·
            refine ⟨68698018199509505513624729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45798678799673003675749819 68698018199509505513624729)
            ·
              refine ⟨51523513649632129135218547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68698018199509505513624729 51523513649632129135218547)
              ·
                refine ⟨77285270474448193702827821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51523513649632129135218547 77285270474448193702827821)
                ·
                  refine ⟨28981976427918072638560433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77285270474448193702827821 28981976427918072638560433)
                  ·
                    refine ⟨21736482320938554478920325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28981976427918072638560433 21736482320938554478920325)
                    ·
                      refine ⟨4075590435175978964797561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21736482320938554478920325 4075590435175978964797561)
                      ·
                        rfl

theorem cell23_7937184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_7937184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937184 prefixEnd_7937184 := by exact prefixLift 7937184
  have htrace : WordTrace (prefixWord ++ tailWord_7937184) baseStart_7937184 baseEnd_7937184 := by
    simpa [prefixWord, tailWord_7937184, baseEnd_7937184] using wordTrace_append hprefix tailTrace_7937184
  have hstable : (prefixWord ++ tailWord_7937184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937184).length < 2 ^ (prefixWord ++ tailWord_7937184).sum := by decide
  have hdescent : baseEnd_7937184 < baseStart_7937184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937191 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7937191 : Nat := 118140960795 + 7937191 * 2 ^ 59
def prefixEnd_7937191 : Nat := 4983230072969 + 3 ^ 40 * 7937191 * 2
def baseEnd_7937191 : Nat := 4075594029540560437410029

theorem tailTrace_7937191 : CollatzResearch.WordTrace tailWord_7937191 prefixEnd_7937191 4075594029540560437410029 := by
  unfold tailWord_7937191
  simp only [CollatzResearch.WordTrace]
  refine ⟨289493138587920046145923427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192995425725280030763948951 289493138587920046145923427)
  ·
    refine ⟨434239707881880069218885141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289493138587920046145923427 434239707881880069218885141)
    ·
      refine ⟨20354986306963128244635241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 434239707881880069218885141 20354986306963128244635241)
      ·
        refine ⟨15266239730222346183476431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20354986306963128244635241 15266239730222346183476431)
        ·
          refine ⟨22899359595333519275214647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15266239730222346183476431 22899359595333519275214647)
          ·
            refine ⟨34349039393000278912821971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22899359595333519275214647 34349039393000278912821971)
            ·
              refine ⟨51523559089500418369232957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34349039393000278912821971 51523559089500418369232957)
              ·
                refine ⟨19321334658562656888462359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51523559089500418369232957 19321334658562656888462359)
                ·
                  refine ⟨28982001987843985332693539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19321334658562656888462359 28982001987843985332693539)
                  ·
                    refine ⟨43473002981765977999040309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28982001987843985332693539 43473002981765977999040309)
                    ·
                      refine ⟨4075594029540560437410029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43473002981765977999040309 4075594029540560437410029)
                      ·
                        rfl

theorem cell23_7937191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7937191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937191 prefixEnd_7937191 := by exact prefixLift 7937191
  have htrace : WordTrace (prefixWord ++ tailWord_7937191) baseStart_7937191 baseEnd_7937191 := by
    simpa [prefixWord, tailWord_7937191, baseEnd_7937191] using wordTrace_append hprefix tailTrace_7937191
  have hstable : (prefixWord ++ tailWord_7937191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937191).length < 2 ^ (prefixWord ++ tailWord_7937191).sum := by decide
  have hdescent : baseEnd_7937191 < baseStart_7937191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937222 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7937222 : Nat := 118140960795 + 7937222 * 2 ^ 59
def prefixEnd_7937222 : Nat := 4983230072969 + 3 ^ 40 * 7937222 * 2
def baseEnd_7937222 : Nat := 4075609947440849816122387

theorem tailTrace_7937222 : CollatzResearch.WordTrace tailWord_7937222 prefixEnd_7937222 4075609947440849816122387 := by
  unfold tailWord_7937222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046695914087741826259435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192996179500538492293534613 9046695914087741826259435)
  ·
    refine ⟨13570043871131612739389153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9046695914087741826259435 13570043871131612739389153)
    ·
      refine ⟨10177532903348709554541865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13570043871131612739389153 10177532903348709554541865)
      ·
        refine ⟨7633149677511532165906399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10177532903348709554541865 7633149677511532165906399)
        ·
          refine ⟨11449724516267298248859599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7633149677511532165906399 11449724516267298248859599)
          ·
            refine ⟨17174586774400947373289399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449724516267298248859599 17174586774400947373289399)
            ·
              refine ⟨25761880161601421059934099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17174586774400947373289399 25761880161601421059934099)
              ·
                refine ⟨38642820242402131589901149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25761880161601421059934099 38642820242402131589901149)
                ·
                  refine ⟨14491057590900799346212931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38642820242402131589901149 14491057590900799346212931)
                  ·
                    refine ⟨21736586386351199019319397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14491057590900799346212931 21736586386351199019319397)
                    ·
                      refine ⟨4075609947440849816122387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21736586386351199019319397 4075609947440849816122387)
                      ·
                        rfl

theorem cell23_7937222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7937222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937222 prefixEnd_7937222 := by exact prefixLift 7937222
  have htrace : WordTrace (prefixWord ++ tailWord_7937222) baseStart_7937222 baseEnd_7937222 := by
    simpa [prefixWord, tailWord_7937222, baseEnd_7937222] using wordTrace_append hprefix tailTrace_7937222
  have hstable : (prefixWord ++ tailWord_7937222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937222).length < 2 ^ (prefixWord ++ tailWord_7937222).sum := by decide
  have hdescent : baseEnd_7937222 < baseStart_7937222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937261 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7937261 : Nat := 118140960795 + 7937261 * 2 ^ 59
def prefixEnd_7937261 : Nat := 4983230072969 + 3 ^ 40 * 7937261 * 2
def baseEnd_7937261 : Nat := 4075629973186375163534707

theorem tailTrace_7937261 : CollatzResearch.WordTrace tailWord_7937261 prefixEnd_7937261 4075629973186375163534707 := by
  unfold tailWord_7937261
  simp only [CollatzResearch.WordTrace]
  refine ⟨289495691697666448100971637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192997127798444298733981091 289495691697666448100971637)
  ·
    refine ⟨27140221096656229509466091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289495691697666448100971637 27140221096656229509466091)
    ·
      refine ⟨40710331644984344264199137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27140221096656229509466091 40710331644984344264199137)
      ·
        refine ⟨30532748733738258198149353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40710331644984344264199137 30532748733738258198149353)
        ·
          refine ⟨22899561550303693648612015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30532748733738258198149353 22899561550303693648612015)
          ·
            refine ⟨34349342325455540472918023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22899561550303693648612015 34349342325455540472918023)
            ·
              refine ⟨51524013488183310709377035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34349342325455540472918023 51524013488183310709377035)
              ·
                refine ⟨77286020232274966064065553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51524013488183310709377035 77286020232274966064065553)
                ·
                  refine ⟨57964515174206224548049165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77286020232274966064065553 57964515174206224548049165)
                  ·
                    refine ⟨21736693190327334205518437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57964515174206224548049165 21736693190327334205518437)
                    ·
                      refine ⟨4075629973186375163534707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21736693190327334205518437 4075629973186375163534707)
                      ·
                        rfl

theorem cell23_7937261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7937261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937261 prefixEnd_7937261 := by exact prefixLift 7937261
  have htrace : WordTrace (prefixWord ++ tailWord_7937261) baseStart_7937261 baseEnd_7937261 := by
    simpa [prefixWord, tailWord_7937261, baseEnd_7937261] using wordTrace_append hprefix tailTrace_7937261
  have hstable : (prefixWord ++ tailWord_7937261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937261).length < 2 ^ (prefixWord ++ tailWord_7937261).sum := by decide
  have hdescent : baseEnd_7937261 < baseStart_7937261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937321 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 6, 5, 2]
def baseStart_7937321 : Nat := 118140960795 + 7937321 * 2 ^ 59
def prefixEnd_7937321 : Nat := 4983230072969 + 3 ^ 40 * 7937321 * 2
def baseEnd_7937321 : Nat := 4075660782025644928784431

theorem tailTrace_7937321 : CollatzResearch.WordTrace tailWord_7937321 prefixEnd_7937321 4075660782025644928784431 := by
  unfold tailWord_7937321
  simp only [CollatzResearch.WordTrace]
  refine ⟨289497880077449078348155817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192998586718299385565437211 289497880077449078348155817)
  ·
    refine ⟨217123410058086808761116863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289497880077449078348155817 217123410058086808761116863)
    ·
      refine ⟨325685115087130213141675295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217123410058086808761116863 325685115087130213141675295)
      ·
        refine ⟨488527672630695319712512943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325685115087130213141675295 488527672630695319712512943)
        ·
          refine ⟨732791508946042979568769415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488527672630695319712512943 732791508946042979568769415)
          ·
            refine ⟨1099187263419064469353154123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732791508946042979568769415 1099187263419064469353154123)
            ·
              refine ⟨1648780895128596704029731185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099187263419064469353154123 1648780895128596704029731185)
              ·
                refine ⟨1236585671346447528022298389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648780895128596704029731185 1236585671346447528022298389)
                ·
                  refine ⟨57964953344364727876045237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1236585671346447528022298389 57964953344364727876045237)
                  ·
                    refine ⟨5434214376034193238379241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57964953344364727876045237 5434214376034193238379241)
                    ·
                      refine ⟨4075660782025644928784431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434214376034193238379241 4075660782025644928784431)
                      ·
                        rfl

theorem cell23_7937321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 5, 2].length) (baseStart_7937321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937321 prefixEnd_7937321 := by exact prefixLift 7937321
  have htrace : WordTrace (prefixWord ++ tailWord_7937321) baseStart_7937321 baseEnd_7937321 := by
    simpa [prefixWord, tailWord_7937321, baseEnd_7937321] using wordTrace_append hprefix tailTrace_7937321
  have hstable : (prefixWord ++ tailWord_7937321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937321).length < 2 ^ (prefixWord ++ tailWord_7937321).sum := by decide
  have hdescent : baseEnd_7937321 < baseStart_7937321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937324 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_7937324 : Nat := 118140960795 + 7937324 * 2 ^ 59
def prefixEnd_7937324 : Nat := 4983230072969 + 3 ^ 40 * 7937324 * 2
def baseEnd_7937324 : Nat := 4075662322467608417046917

theorem tailTrace_7937324 : CollatzResearch.WordTrace tailWord_7937324 prefixEnd_7937324 4075662322467608417046917 := by
  unfold tailWord_7937324
  simp only [CollatzResearch.WordTrace]
  refine ⟨144748994748219104930257513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192998659664292139907010017 144748994748219104930257513)
  ·
    refine ⟨108561746061164328697693135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144748994748219104930257513 108561746061164328697693135)
    ·
      refine ⟨162842619091746493046539703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108561746061164328697693135 162842619091746493046539703)
      ·
        refine ⟨244263928637619739569809555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162842619091746493046539703 244263928637619739569809555)
        ·
          refine ⟨366395892956429609354714333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244263928637619739569809555 366395892956429609354714333)
          ·
            refine ⟨137398459858661103508017875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366395892956429609354714333 137398459858661103508017875)
            ·
              refine ⟨206097689787991655262026813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137398459858661103508017875 206097689787991655262026813)
              ·
                refine ⟨77286633670496870723260055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206097689787991655262026813 77286633670496870723260055)
                ·
                  refine ⟨115929950505745306084890083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77286633670496870723260055 115929950505745306084890083)
                  ·
                    refine ⟨173894925758617959127335125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115929950505745306084890083 173894925758617959127335125)
                    ·
                      refine ⟨4075662322467608417046917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173894925758617959127335125 4075662322467608417046917)
                      ·
                        rfl

theorem cell23_7937324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_7937324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937324 prefixEnd_7937324 := by exact prefixLift 7937324
  have htrace : WordTrace (prefixWord ++ tailWord_7937324) baseStart_7937324 baseEnd_7937324 := by
    simpa [prefixWord, tailWord_7937324, baseEnd_7937324] using wordTrace_append hprefix tailTrace_7937324
  have hstable : (prefixWord ++ tailWord_7937324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937324).length < 2 ^ (prefixWord ++ tailWord_7937324).sum := by decide
  have hdescent : baseEnd_7937324 < baseStart_7937324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937344 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 2, 8]
def baseStart_7937344 : Nat := 118140960795 + 7937344 * 2 ^ 59
def prefixEnd_7937344 : Nat := 4983230072969 + 3 ^ 40 * 7937344 * 2
def baseEnd_7937344 : Nat := 1358557530693566112932275

theorem tailTrace_7937344 : CollatzResearch.WordTrace tailWord_7937344 prefixEnd_7937344 1358557530693566112932275 := by
  unfold tailWord_7937344
  simp only [CollatzResearch.WordTrace]
  refine ⟨144749359478182876638121543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192999145970910502184162057 144749359478182876638121543)
  ·
    refine ⟨217124039217274314957182315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144749359478182876638121543 217124039217274314957182315)
    ·
      refine ⟨325686058825911472435773473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217124039217274314957182315 325686058825911472435773473)
      ·
        refine ⟨244264544119433604326830105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325686058825911472435773473 244264544119433604326830105)
        ·
          refine ⟨183198408089575203245122579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244264544119433604326830105 183198408089575203245122579)
          ·
            refine ⟨274797612134362804867683869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183198408089575203245122579 274797612134362804867683869)
            ·
              refine ⟨103049104550386051825381451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274797612134362804867683869 103049104550386051825381451)
              ·
                refine ⟨154573656825579077738072177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103049104550386051825381451 154573656825579077738072177)
                ·
                  refine ⟨115930242619184308303554133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154573656825579077738072177 115930242619184308303554133)
                  ·
                    refine ⟨1358557530693566112932275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115930242619184308303554133 1358557530693566112932275)
                    ·
                      rfl

theorem cell23_7937344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_7937344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937344 prefixEnd_7937344 := by exact prefixLift 7937344
  have htrace : WordTrace (prefixWord ++ tailWord_7937344) baseStart_7937344 baseEnd_7937344 := by
    simpa [prefixWord, tailWord_7937344, baseEnd_7937344] using wordTrace_append hprefix tailTrace_7937344
  have hstable : (prefixWord ++ tailWord_7937344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937344).length < 2 ^ (prefixWord ++ tailWord_7937344).sum := by decide
  have hdescent : baseEnd_7937344 < baseStart_7937344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937348 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7937348 : Nat := 118140960795 + 7937348 * 2 ^ 59
def prefixEnd_7937348 : Nat := 4983230072969 + 3 ^ 40 * 7937348 * 2
def baseEnd_7937348 : Nat := 1358558215334438774382269

theorem tailTrace_7937348 : CollatzResearch.WordTrace tailWord_7937348 prefixEnd_7937348 1358558215334438774382269 := by
  unfold tailWord_7937348
  simp only [CollatzResearch.WordTrace]
  refine ⟨144749432424175630979694349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192999243232234174639592465 144749432424175630979694349)
  ·
    refine ⟨54281037159065861617385381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144749432424175630979694349 54281037159065861617385381)
    ·
      refine ⟨10177694467324849053259759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54281037159065861617385381 10177694467324849053259759)
      ·
        refine ⟨15266541700987273579889639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10177694467324849053259759 15266541700987273579889639)
        ·
          refine ⟨22899812551480910369834459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15266541700987273579889639 22899812551480910369834459)
          ·
            refine ⟨34349718827221365554751689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22899812551480910369834459 34349718827221365554751689)
            ·
              refine ⟨25762289120416024166063767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34349718827221365554751689 25762289120416024166063767)
              ·
                refine ⟨38643433680624036249095651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25762289120416024166063767 38643433680624036249095651)
                ·
                  refine ⟨57965150520936054373643477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38643433680624036249095651 57965150520936054373643477)
                  ·
                    refine ⟨1358558215334438774382269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57965150520936054373643477 1358558215334438774382269)
                    ·
                      rfl

theorem cell23_7937348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7937348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937348 prefixEnd_7937348 := by exact prefixLift 7937348
  have htrace : WordTrace (prefixWord ++ tailWord_7937348) baseStart_7937348 baseEnd_7937348 := by
    simpa [prefixWord, tailWord_7937348, baseEnd_7937348] using wordTrace_append hprefix tailTrace_7937348
  have hstable : (prefixWord ++ tailWord_7937348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937348).length < 2 ^ (prefixWord ++ tailWord_7937348).sum := by decide
  have hdescent : baseEnd_7937348 < baseStart_7937348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937351 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_7937351 : Nat := 118140960795 + 7937351 * 2 ^ 59
def prefixEnd_7937351 : Nat := 4983230072969 + 3 ^ 40 * 7937351 * 2
def baseEnd_7937351 : Nat := 4075676186445279811409293

theorem tailTrace_7937351 : CollatzResearch.WordTrace tailWord_7937351 prefixEnd_7937351 4075676186445279811409293 := by
  unfold tailWord_7937351
  simp only [CollatzResearch.WordTrace]
  refine ⟨289498974267340393471747907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192999316178226928981165271 289498974267340393471747907)
  ·
    refine ⟨434248461401010590207621861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289498974267340393471747907 434248461401010590207621861)
    ·
      refine ⟨81421586512689485663929099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434248461401010590207621861 81421586512689485663929099)
      ·
        refine ⟨122132379769034228495893649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81421586512689485663929099 122132379769034228495893649)
        ·
          refine ⟨91599284826775671371920237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122132379769034228495893649 91599284826775671371920237)
          ·
            refine ⟨34349731810040876764470089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91599284826775671371920237 34349731810040876764470089)
            ·
              refine ⟨25762298857530657573352567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34349731810040876764470089 25762298857530657573352567)
              ·
                refine ⟨38643448286295986360028851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25762298857530657573352567 38643448286295986360028851)
                ·
                  refine ⟨57965172429443979540043277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38643448286295986360028851 57965172429443979540043277)
                  ·
                    refine ⟨21736939661041492327516229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57965172429443979540043277 21736939661041492327516229)
                    ·
                      refine ⟨4075676186445279811409293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21736939661041492327516229 4075676186445279811409293)
                      ·
                        rfl

theorem cell23_7937351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_7937351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937351 prefixEnd_7937351 := by exact prefixLift 7937351
  have htrace : WordTrace (prefixWord ++ tailWord_7937351) baseStart_7937351 baseEnd_7937351 := by
    simpa [prefixWord, tailWord_7937351, baseEnd_7937351] using wordTrace_append hprefix tailTrace_7937351
  have hstable : (prefixWord ++ tailWord_7937351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937351).length < 2 ^ (prefixWord ++ tailWord_7937351).sum := by decide
  have hdescent : baseEnd_7937351 < baseStart_7937351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937391 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 6]
def baseStart_7937391 : Nat := 118140960795 + 7937391 * 2 ^ 59
def prefixEnd_7937391 : Nat := 4983230072969 + 3 ^ 40 * 7937391 * 2
def baseEnd_7937391 : Nat := 452855191741273294989901

theorem tailTrace_7937391 : CollatzResearch.WordTrace tailWord_7937391 prefixEnd_7937391 452855191741273294989901 := by
  unfold tailWord_7937391
  simp only [CollatzResearch.WordTrace]
  refine ⟨289500433187195480303204027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193000288791463653535469351 289500433187195480303204027)
  ·
    refine ⟨434250649780793220454806041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289500433187195480303204027 434250649780793220454806041)
    ·
      refine ⟨325687987335594915341104531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434250649780793220454806041 325687987335594915341104531)
      ·
        refine ⟨488531981003392373011656797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325687987335594915341104531 488531981003392373011656797)
        ·
          refine ⟨183199492876272139879371299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488531981003392373011656797 183199492876272139879371299)
          ·
            refine ⟨274799239314408209819056949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183199492876272139879371299 274799239314408209819056949)
            ·
              refine ⟨25762428685725769670536589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274799239314408209819056949 25762428685725769670536589)
              ·
                refine ⟨9660910757147163626451221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25762428685725769670536589 9660910757147163626451221)
                ·
                  refine ⟨452855191741273294989901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9660910757147163626451221 452855191741273294989901)
                  ·
                    rfl

theorem cell23_7937391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 6].length) (baseStart_7937391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937391 prefixEnd_7937391 := by exact prefixLift 7937391
  have htrace : WordTrace (prefixWord ++ tailWord_7937391) baseStart_7937391 baseEnd_7937391 := by
    simpa [prefixWord, tailWord_7937391, baseEnd_7937391] using wordTrace_append hprefix tailTrace_7937391
  have hstable : (prefixWord ++ tailWord_7937391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937391).length < 2 ^ (prefixWord ++ tailWord_7937391).sum := by decide
  have hdescent : baseEnd_7937391 < baseStart_7937391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937401 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 3]
def baseStart_7937401 : Nat := 118140960795 + 7937401 * 2 ^ 59
def prefixEnd_7937401 : Nat := 4983230072969 + 3 ^ 40 * 7937401 * 2
def baseEnd_7937401 : Nat := 4075701860478004615784063

theorem tailTrace_7937401 : CollatzResearch.WordTrace tailWord_7937401 prefixEnd_7937401 4075701860478004615784063 := by
  unfold tailWord_7937401
  simp only [CollatzResearch.WordTrace]
  refine ⟨289500797917159252011068057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193000531944772834674045371 289500797917159252011068057)
  ·
    refine ⟨217125598437869439008301043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289500797917159252011068057 217125598437869439008301043)
    ·
      refine ⟨325688397656804158512451565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217125598437869439008301043 325688397656804158512451565)
      ·
        refine ⟨122133149121301559442169337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325688397656804158512451565 122133149121301559442169337)
        ·
          refine ⟨91599861840976169581627003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122133149121301559442169337 91599861840976169581627003)
          ·
            refine ⟨137399792761464254372440505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91599861840976169581627003 137399792761464254372440505)
            ·
              refine ⟨103049844571098190779330379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137399792761464254372440505 103049844571098190779330379)
              ·
                refine ⟨154574766856647286168995569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103049844571098190779330379 154574766856647286168995569)
                ·
                  refine ⟨115931075142485464626746677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154574766856647286168995569 115931075142485464626746677)
                  ·
                    refine ⟨10868538294608012308757501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115931075142485464626746677 10868538294608012308757501)
                    ·
                      refine ⟨4075701860478004615784063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10868538294608012308757501 4075701860478004615784063)
                      ·
                        rfl

theorem cell23_7937401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_7937401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937401 prefixEnd_7937401 := by exact prefixLift 7937401
  have htrace : WordTrace (prefixWord ++ tailWord_7937401) baseStart_7937401 baseEnd_7937401 := by
    simpa [prefixWord, tailWord_7937401, baseEnd_7937401] using wordTrace_append hprefix tailTrace_7937401
  have hstable : (prefixWord ++ tailWord_7937401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937401).length < 2 ^ (prefixWord ++ tailWord_7937401).sum := by decide
  have hdescent : baseEnd_7937401 < baseStart_7937401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937458 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_7937458 : Nat := 118140960795 + 7937458 * 2 ^ 59
def prefixEnd_7937458 : Nat := 4983230072969 + 3 ^ 40 * 7937458 * 2
def baseEnd_7937458 : Nat := 4075731128875310892771301

theorem tailTrace_7937458 : CollatzResearch.WordTrace tailWord_7937458 prefixEnd_7937458 4075731128875310892771301 := by
  unfold tailWord_7937458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72375719219488187686473257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193001917918635167163928685 72375719219488187686473257)
  ·
    refine ⟨54281789414616140764854943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72375719219488187686473257 54281789414616140764854943)
    ·
      refine ⟨81422684121924211147282415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54281789414616140764854943 81422684121924211147282415)
      ·
        refine ⟨122134026182886316720923623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81422684121924211147282415 122134026182886316720923623)
        ·
          refine ⟨183201039274329475081385435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122134026182886316720923623 183201039274329475081385435)
          ·
            refine ⟨274801558911494212622078153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183201039274329475081385435 274801558911494212622078153)
            ·
              refine ⟨206101169183620659466558615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274801558911494212622078153 206101169183620659466558615)
              ·
                refine ⟨309151753775430989199837923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206101169183620659466558615 309151753775430989199837923)
                ·
                  refine ⟨463727630663146483799756885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309151753775430989199837923 463727630663146483799756885)
                  ·
                    refine ⟨5434308171833747857028401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 463727630663146483799756885 5434308171833747857028401)
                    ·
                      refine ⟨4075731128875310892771301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434308171833747857028401 4075731128875310892771301)
                      ·
                        rfl

theorem cell23_7937458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_7937458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937458 prefixEnd_7937458 := by exact prefixLift 7937458
  have htrace : WordTrace (prefixWord ++ tailWord_7937458) baseStart_7937458 baseEnd_7937458 := by
    simpa [prefixWord, tailWord_7937458, baseEnd_7937458] using wordTrace_append hprefix tailTrace_7937458
  have hstable : (prefixWord ++ tailWord_7937458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937458).length < 2 ^ (prefixWord ++ tailWord_7937458).sum := by decide
  have hdescent : baseEnd_7937458 < baseStart_7937458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937475 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 1, 1, 4]
def baseStart_7937475 : Nat := 118140960795 + 7937475 * 2 ^ 59
def prefixEnd_7937475 : Nat := 4983230072969 + 3 ^ 40 * 7937475 * 2
def baseEnd_7937475 : Nat := 4075739858046437326258723

theorem tailTrace_7937475 : CollatzResearch.WordTrace tailWord_7937475 prefixEnd_7937475 4075739858046437326258723 := by
  unfold tailWord_7937475
  simp only [CollatzResearch.WordTrace]
  refine ⟨289503496918891162649261879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193002331279260775099507919 289503496918891162649261879)
  ·
    refine ⟨434255245378336743973892819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289503496918891162649261879 434255245378336743973892819)
    ·
      refine ⟨651382868067505115960839229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434255245378336743973892819 651382868067505115960839229)
      ·
        refine ⟨244268575525314418485314711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651382868067505115960839229 244268575525314418485314711)
        ·
          refine ⟨366402863287971627727972067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244268575525314418485314711 366402863287971627727972067)
          ·
            refine ⟨549604294931957441591958101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366402863287971627727972067 549604294931957441591958101)
            ·
              refine ⟨6440675331233876268655759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 549604294931957441591958101 6440675331233876268655759)
              ·
                refine ⟨9661012996850814402983639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440675331233876268655759 9661012996850814402983639)
                ·
                  refine ⟨14491519495276221604475459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9661012996850814402983639 14491519495276221604475459)
                  ·
                    refine ⟨21737279242914332406713189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14491519495276221604475459 21737279242914332406713189)
                    ·
                      refine ⟨4075739858046437326258723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21737279242914332406713189 4075739858046437326258723)
                      ·
                        rfl

theorem cell23_7937475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_7937475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937475 prefixEnd_7937475 := by exact prefixLift 7937475
  have htrace : WordTrace (prefixWord ++ tailWord_7937475) baseStart_7937475 baseEnd_7937475 := by
    simpa [prefixWord, tailWord_7937475, baseEnd_7937475] using wordTrace_append hprefix tailTrace_7937475
  have hstable : (prefixWord ++ tailWord_7937475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937475).length < 2 ^ (prefixWord ++ tailWord_7937475).sum := by decide
  have hdescent : baseEnd_7937475 < baseStart_7937475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937505 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_7937505 : Nat := 118140960795 + 7937505 * 2 ^ 59
def prefixEnd_7937505 : Nat := 4983230072969 + 3 ^ 40 * 7937505 * 2
def baseEnd_7937505 : Nat := 4075755262466072208883585

theorem tailTrace_7937505 : CollatzResearch.WordTrace tailWord_7937505 prefixEnd_7937505 4075755262466072208883585 := by
  unfold tailWord_7937505
  simp only [CollatzResearch.WordTrace]
  refine ⟨289504591108782477772853969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193003060739188318515235979 289504591108782477772853969)
  ·
    refine ⟨217128443331586858329640477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289504591108782477772853969 217128443331586858329640477)
    ·
      refine ⟨81423166249345071873615179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217128443331586858329640477 81423166249345071873615179)
      ·
        refine ⟨122134749374017607810422769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81423166249345071873615179 122134749374017607810422769)
        ·
          refine ⟨91601062030513205857817077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122134749374017607810422769 91601062030513205857817077)
          ·
            refine ⟨8587599565360613049170351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91601062030513205857817077 8587599565360613049170351)
            ·
              refine ⟨12881399348040919573755527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587599565360613049170351 12881399348040919573755527)
              ·
                refine ⟨19322099022061379360633291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12881399348040919573755527 19322099022061379360633291)
                ·
                  refine ⟨28983148533092069040949937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19322099022061379360633291 28983148533092069040949937)
                  ·
                    refine ⟨21737361399819051780712453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28983148533092069040949937 21737361399819051780712453)
                    ·
                      refine ⟨4075755262466072208883585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21737361399819051780712453 4075755262466072208883585)
                      ·
                        rfl

theorem cell23_7937505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_7937505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937505 prefixEnd_7937505 := by exact prefixLift 7937505
  have htrace : WordTrace (prefixWord ++ tailWord_7937505) baseStart_7937505 baseEnd_7937505 := by
    simpa [prefixWord, tailWord_7937505, baseEnd_7937505] using wordTrace_append hprefix tailTrace_7937505
  have hstable : (prefixWord ++ tailWord_7937505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937505).length < 2 ^ (prefixWord ++ tailWord_7937505).sum := by decide
  have hdescent : baseEnd_7937505 < baseStart_7937505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937526 : List Nat := [5, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_7937526 : Nat := 118140960795 + 7937526 * 2 ^ 59
def prefixEnd_7937526 : Nat := 4983230072969 + 3 ^ 40 * 7937526 * 2
def baseEnd_7937526 : Nat := 4075766045559816626720989

theorem tailTrace_7937526 : CollatzResearch.WordTrace tailWord_7937526 prefixEnd_7937526 4075766045559816626720989 := by
  unfold tailWord_7937526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18094084815106649897460527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193003571361137598906245621 18094084815106649897460527)
  ·
    refine ⟨27141127222659974846190791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18094084815106649897460527 27141127222659974846190791)
    ·
      refine ⟨40711690833989962269286187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27141127222659974846190791 40711690833989962269286187)
      ·
        refine ⟨61067536250984943403929281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40711690833989962269286187 61067536250984943403929281)
        ·
          refine ⟨45800652188238707552946961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61067536250984943403929281 45800652188238707552946961)
          ·
            refine ⟨34350489141179030664710221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45800652188238707552946961 34350489141179030664710221)
            ·
              refine ⟨12881433427942136499266333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34350489141179030664710221 12881433427942136499266333)
              ·
                refine ⟨4830537535478301187224875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12881433427942136499266333 4830537535478301187224875)
                ·
                  refine ⟨7245806303217451780837313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830537535478301187224875 7245806303217451780837313)
                  ·
                    refine ⟨5434354727413088835627985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7245806303217451780837313 5434354727413088835627985)
                    ·
                      refine ⟨4075766045559816626720989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434354727413088835627985 4075766045559816626720989)
                      ·
                        rfl

theorem cell23_7937526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_7937526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937526 prefixEnd_7937526 := by exact prefixLift 7937526
  have htrace : WordTrace (prefixWord ++ tailWord_7937526) baseStart_7937526 baseEnd_7937526 := by
    simpa [prefixWord, tailWord_7937526, baseEnd_7937526] using wordTrace_append hprefix tailTrace_7937526
  have hstable : (prefixWord ++ tailWord_7937526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937526).length < 2 ^ (prefixWord ++ tailWord_7937526).sum := by decide
  have hdescent : baseEnd_7937526 < baseStart_7937526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937569 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_7937569 : Nat := 118140960795 + 7937569 * 2 ^ 59
def prefixEnd_7937569 : Nat := 4983230072969 + 3 ^ 40 * 7937569 * 2
def baseEnd_7937569 : Nat := 4075788125227959958483291

theorem tailTrace_7937569 : CollatzResearch.WordTrace tailWord_7937569 prefixEnd_7937569 4075788125227959958483291 := by
  unfold tailWord_7937569
  simp only [CollatzResearch.WordTrace]
  refine ⟨289506925380550616703183761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193004616920367077802122507 289506925380550616703183761)
  ·
    refine ⟨217130194035412962527387821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289506925380550616703183761 217130194035412962527387821)
    ·
      refine ⟨81423822763279860947770433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217130194035412962527387821 81423822763279860947770433)
      ·
        refine ⟨61067867072459895710827825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81423822763279860947770433 61067867072459895710827825)
        ·
          refine ⟨45800900304344921783120869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61067867072459895710827825 45800900304344921783120869)
          ·
            refine ⟨8587668807064672834335163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45800900304344921783120869 8587668807064672834335163)
            ·
              refine ⟨12881503210597009251502745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587668807064672834335163 12881503210597009251502745)
              ·
                refine ⟨9661127407947756938627059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12881503210597009251502745 9661127407947756938627059)
                ·
                  refine ⟨14491691111921635407940589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9661127407947756938627059 14491691111921635407940589)
                  ·
                    refine ⟨5434384166970613277977721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14491691111921635407940589 5434384166970613277977721)
                    ·
                      refine ⟨4075788125227959958483291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434384166970613277977721 4075788125227959958483291)
                      ·
                        rfl

theorem cell23_7937569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_7937569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937569 prefixEnd_7937569 := by exact prefixLift 7937569
  have htrace : WordTrace (prefixWord ++ tailWord_7937569) baseStart_7937569 baseEnd_7937569 := by
    simpa [prefixWord, tailWord_7937569, baseEnd_7937569] using wordTrace_append hprefix tailTrace_7937569
  have hstable : (prefixWord ++ tailWord_7937569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937569).length < 2 ^ (prefixWord ++ tailWord_7937569).sum := by decide
  have hdescent : baseEnd_7937569 < baseStart_7937569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937582 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_7937582 : Nat := 118140960795 + 7937582 * 2 ^ 59
def prefixEnd_7937582 : Nat := 4983230072969 + 3 ^ 40 * 7937582 * 2
def baseEnd_7937582 : Nat := 4075794800476468407620731

theorem tailTrace_7937582 : CollatzResearch.WordTrace tailWord_7937582 prefixEnd_7937582 4075794800476468407620731 := by
  unfold tailWord_7937582
  simp only [CollatzResearch.WordTrace]
  refine ⟨36188424941187939990425875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193004933019669013282271333 36188424941187939990425875)
  ·
    refine ⟨54282637411781909985638813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36188424941187939990425875 54282637411781909985638813)
    ·
      refine ⟨20355989029418216244614555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54282637411781909985638813 20355989029418216244614555)
      ·
        refine ⟨30533983544127324366921833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20355989029418216244614555 30533983544127324366921833)
        ·
          refine ⟨22900487658095493275191375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30533983544127324366921833 22900487658095493275191375)
          ·
            refine ⟨34350731487143239912787063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22900487658095493275191375 34350731487143239912787063)
            ·
              refine ⟨51526097230714859869180595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34350731487143239912787063 51526097230714859869180595)
              ·
                refine ⟨77289145846072289803770893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51526097230714859869180595 77289145846072289803770893)
                ·
                  refine ⟨28983429692277108676414085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77289145846072289803770893 28983429692277108676414085)
                  ·
                    refine ⟨5434393067301957876827641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28983429692277108676414085 5434393067301957876827641)
                    ·
                      refine ⟨4075794800476468407620731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434393067301957876827641 4075794800476468407620731)
                      ·
                        rfl

theorem cell23_7937582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_7937582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937582 prefixEnd_7937582 := by exact prefixLift 7937582
  have htrace : WordTrace (prefixWord ++ tailWord_7937582) baseStart_7937582 baseEnd_7937582 := by
    simpa [prefixWord, tailWord_7937582, baseEnd_7937582] using wordTrace_append hprefix tailTrace_7937582
  have hstable : (prefixWord ++ tailWord_7937582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937582).length < 2 ^ (prefixWord ++ tailWord_7937582).sum := by decide
  have hdescent : baseEnd_7937582 < baseStart_7937582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937599 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 2, 2, 2]
def baseStart_7937599 : Nat := 118140960795 + 7937599 * 2 ^ 59
def prefixEnd_7937599 : Nat := 4983230072969 + 3 ^ 40 * 7937599 * 2
def baseEnd_7937599 : Nat := 4075803529647594841108153

theorem tailTrace_7937599 : CollatzResearch.WordTrace tailWord_7937599 prefixEnd_7937599 4075803529647594841108153 := by
  unfold tailWord_7937599
  simp only [CollatzResearch.WordTrace]
  refine ⟨289508019570441931826775851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193005346380294621217850567 289508019570441931826775851)
  ·
    refine ⟨434262029355662897740163777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289508019570441931826775851 434262029355662897740163777)
    ·
      refine ⟨325696522016747173305122833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434262029355662897740163777 325696522016747173305122833)
      ·
        refine ⟨244272391512560379978842125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325696522016747173305122833 244272391512560379978842125)
        ·
          refine ⟨91602146817210142492065797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244272391512560379978842125 91602146817210142492065797)
          ·
            refine ⟨17175402528226901717262337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91602146817210142492065797 17175402528226901717262337)
            ·
              refine ⟨12881551896170176287946753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17175402528226901717262337 12881551896170176287946753)
              ·
                refine ⟨9661163922127632215960065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12881551896170176287946753 9661163922127632215960065)
                ·
                  refine ⟨7245872941595724161970049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9661163922127632215960065 7245872941595724161970049)
                  ·
                    refine ⟨5434404706196793121477537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7245872941595724161970049 5434404706196793121477537)
                    ·
                      refine ⟨4075803529647594841108153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434404706196793121477537 4075803529647594841108153)
                      ·
                        rfl

theorem cell23_7937599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_7937599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937599 prefixEnd_7937599 := by exact prefixLift 7937599
  have htrace : WordTrace (prefixWord ++ tailWord_7937599) baseStart_7937599 baseEnd_7937599 := by
    simpa [prefixWord, tailWord_7937599, baseEnd_7937599] using wordTrace_append hprefix tailTrace_7937599
  have hstable : (prefixWord ++ tailWord_7937599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937599).length < 2 ^ (prefixWord ++ tailWord_7937599).sum := by decide
  have hdescent : baseEnd_7937599 < baseStart_7937599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937605 : List Nat := [1, 3, 1, 1, 1, 4, 3, 4, 5]
def baseStart_7937605 : Nat := 118140960795 + 7937605 * 2 ^ 59
def prefixEnd_7937605 : Nat := 4983230072969 + 3 ^ 40 * 7937605 * 2
def baseEnd_7937605 : Nat := 452867401170169090848125

theorem tailTrace_7937605 : CollatzResearch.WordTrace tailWord_7937605 prefixEnd_7937605 452867401170169090848125 := by
  unfold tailWord_7937605
  simp only [CollatzResearch.WordTrace]
  refine ⟨289508238408420194851494269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193005492272280129900996179 289508238408420194851494269)
  ·
    refine ⟨108565589403157573069310351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289508238408420194851494269 108565589403157573069310351)
    ·
      refine ⟨162848384104736359603965527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108565589403157573069310351 162848384104736359603965527)
      ·
        refine ⟨244272576157104539405948291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162848384104736359603965527 244272576157104539405948291)
        ·
          refine ⟨366408864235656809108922437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244272576157104539405948291 366408864235656809108922437)
          ·
            refine ⟨68701662044185651707922957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366408864235656809108922437 68701662044185651707922957)
            ·
              refine ⟨25763123266569619390471109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68701662044185651707922957 25763123266569619390471109)
              ·
                refine ⟨4830585612481803635713333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25763123266569619390471109 4830585612481803635713333)
                ·
                  refine ⟨452867401170169090848125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4830585612481803635713333 452867401170169090848125)
                  ·
                    rfl

theorem cell23_7937605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_7937605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937605 prefixEnd_7937605 := by exact prefixLift 7937605
  have htrace : WordTrace (prefixWord ++ tailWord_7937605) baseStart_7937605 baseEnd_7937605 := by
    simpa [prefixWord, tailWord_7937605, baseEnd_7937605] using wordTrace_append hprefix tailTrace_7937605
  have hstable : (prefixWord ++ tailWord_7937605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937605).length < 2 ^ (prefixWord ++ tailWord_7937605).sum := by decide
  have hdescent : baseEnd_7937605 < baseStart_7937605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937635 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 2, 5]
def baseStart_7937635 : Nat := 118140960795 + 7937635 * 2 ^ 59
def prefixEnd_7937635 : Nat := 4983230072969 + 3 ^ 40 * 7937635 * 2
def baseEnd_7937635 : Nat := 1358607338317052233419329

theorem tailTrace_7937635 : CollatzResearch.WordTrace tailWord_7937635 prefixEnd_7937635 1358607338317052233419329 := by
  unfold tailWord_7937635
  simp only [CollatzResearch.WordTrace]
  refine ⟨289509332598311509975086359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193006221732207673316724239 289509332598311509975086359)
  ·
    refine ⟨434263998897467264962629539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289509332598311509975086359 434263998897467264962629539)
    ·
      refine ⟨651395998346200897443944309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434263998897467264962629539 651395998346200897443944309)
      ·
        refine ⟨61068374844956334135369779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 651395998346200897443944309 61068374844956334135369779)
        ·
          refine ⟨91602562267434501203054669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61068374844956334135369779 91602562267434501203054669)
          ·
            refine ⟨34350960850287937951145501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91602562267434501203054669 34350960850287937951145501)
            ·
              refine ⟨12881610318857976731679563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34350960850287937951145501 12881610318857976731679563)
              ·
                refine ⟨19322415478286965097519345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12881610318857976731679563 19322415478286965097519345)
                ·
                  refine ⟨14491811608715223823139509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19322415478286965097519345 14491811608715223823139509)
                  ·
                    refine ⟨1358607338317052233419329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14491811608715223823139509 1358607338317052233419329)
                    ·
                      rfl

theorem cell23_7937635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 5].length) (baseStart_7937635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937635 prefixEnd_7937635 := by exact prefixLift 7937635
  have htrace : WordTrace (prefixWord ++ tailWord_7937635) baseStart_7937635 baseEnd_7937635 := by
    simpa [prefixWord, tailWord_7937635, baseEnd_7937635] using wordTrace_append hprefix tailTrace_7937635
  have hstable : (prefixWord ++ tailWord_7937635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937635).length < 2 ^ (prefixWord ++ tailWord_7937635).sum := by decide
  have hdescent : baseEnd_7937635 < baseStart_7937635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937725 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_7937725 : Nat := 118140960795 + 7937725 * 2 ^ 59
def prefixEnd_7937725 : Nat := 4983230072969 + 3 ^ 40 * 7937725 * 2
def baseEnd_7937725 : Nat := 1358622742736687116044191

theorem tailTrace_7937725 : CollatzResearch.WordTrace tailWord_7937725 prefixEnd_7937725 1358622742736687116044191 := by
  unfold tailWord_7937725
  simp only [CollatzResearch.WordTrace]
  refine ⟨289512615167985455345862629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193008410111990303563908419 289512615167985455345862629)
  ·
    refine ⟨54283615343997272877349243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289512615167985455345862629 54283615343997272877349243)
    ·
      refine ⟨81425423015995909316023865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54283615343997272877349243 81425423015995909316023865)
      ·
        refine ⟨61069067261996931987017899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81425423015995909316023865 61069067261996931987017899)
        ·
          refine ⟨91603600892995397980526849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61069067261996931987017899 91603600892995397980526849)
          ·
            refine ⟨68702700669746548485395137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91603600892995397980526849 68702700669746548485395137)
            ·
              refine ⟨51527025502309911364046353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68702700669746548485395137 51527025502309911364046353)
              ·
                refine ⟨38645269126732433523034765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51527025502309911364046353 38645269126732433523034765)
                ·
                  refine ⟨14491975922524662571138037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38645269126732433523034765 14491975922524662571138037)
                  ·
                    refine ⟨1358622742736687116044191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14491975922524662571138037 1358622742736687116044191)
                    ·
                      rfl

theorem cell23_7937725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_7937725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937725 prefixEnd_7937725 := by exact prefixLift 7937725
  have htrace : WordTrace (prefixWord ++ tailWord_7937725) baseStart_7937725 baseEnd_7937725 := by
    simpa [prefixWord, tailWord_7937725, baseEnd_7937725] using wordTrace_append hprefix tailTrace_7937725
  have hstable : (prefixWord ++ tailWord_7937725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937725).length < 2 ^ (prefixWord ++ tailWord_7937725).sum := by decide
  have hdescent : baseEnd_7937725 < baseStart_7937725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937772 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_7937772 : Nat := 118140960795 + 7937772 * 2 ^ 59
def prefixEnd_7937772 : Nat := 4983230072969 + 3 ^ 40 * 7937772 * 2
def baseEnd_7937772 : Nat := 1358630787266940888081619

theorem tailTrace_7937772 : CollatzResearch.WordTrace tailWord_7937772 prefixEnd_7937772 1358630787266940888081619 := by
  unfold tailWord_7937772
  simp only [CollatzResearch.WordTrace]
  refine ⟨144757164699407591186411785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193009552932543454915215713 144757164699407591186411785)
  ·
    refine ⟨108567873524555693389808839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144757164699407591186411785 108567873524555693389808839)
    ·
      refine ⟨162851810286833540084713259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108567873524555693389808839 162851810286833540084713259)
      ·
        refine ⟨244277715430250310127069889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162851810286833540084713259 244277715430250310127069889)
        ·
          refine ⟨183208286572687732595302417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244277715430250310127069889 183208286572687732595302417)
          ·
            refine ⟨137406214929515799446476813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183208286572687732595302417 137406214929515799446476813)
            ·
              refine ⟨51527330598568424792428805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137406214929515799446476813 51527330598568424792428805)
              ·
                refine ⟨9661374487231579648580401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51527330598568424792428805 9661374487231579648580401)
                ·
                  refine ⟨7246030865423684736435301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9661374487231579648580401 7246030865423684736435301)
                  ·
                    refine ⟨1358630787266940888081619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7246030865423684736435301 1358630787266940888081619)
                    ·
                      rfl

theorem cell23_7937772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_7937772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937772 prefixEnd_7937772 := by exact prefixLift 7937772
  have htrace : WordTrace (prefixWord ++ tailWord_7937772) baseStart_7937772 baseEnd_7937772 := by
    simpa [prefixWord, tailWord_7937772, baseEnd_7937772] using wordTrace_append hprefix tailTrace_7937772
  have hstable : (prefixWord ++ tailWord_7937772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937772).length < 2 ^ (prefixWord ++ tailWord_7937772).sum := by decide
  have hdescent : baseEnd_7937772 < baseStart_7937772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937773 : List Nat := [1, 5, 1, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_7937773 : Nat := 118140960795 + 7937773 * 2 ^ 59
def prefixEnd_7937773 : Nat := 4983230072969 + 3 ^ 40 * 7937773 * 2
def baseEnd_7937773 : Nat := 4075892875281477160332353

theorem tailTrace_7937773 : CollatzResearch.WordTrace tailWord_7937773 prefixEnd_7937773 4075892875281477160332353 := by
  unfold tailWord_7937773
  simp only [CollatzResearch.WordTrace]
  refine ⟨289514365871811559543609973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193009577247874373029073315 289514365871811559543609973)
  ·
    refine ⟨27141971800482333707213435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289514365871811559543609973 27141971800482333707213435)
    ·
      refine ⟨40712957700723500560820153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27141971800482333707213435 40712957700723500560820153)
      ·
        refine ⟨30534718275542625420615115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40712957700723500560820153 30534718275542625420615115)
        ·
          refine ⟨45802077413313938130922673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30534718275542625420615115 45802077413313938130922673)
          ·
            refine ⟨34351558059985453598192005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45802077413313938130922673 34351558059985453598192005)
            ·
              refine ⟨6440917136247272549661001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34351558059985453598192005 6440917136247272549661001)
              ·
                refine ⟨4830687852185454412245751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440917136247272549661001 4830687852185454412245751)
                ·
                  refine ⟨7246031778278181618368627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830687852185454412245751 7246031778278181618368627)
                  ·
                    refine ⟨10869047667417272427552941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7246031778278181618368627 10869047667417272427552941)
                    ·
                      refine ⟨4075892875281477160332353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869047667417272427552941 4075892875281477160332353)
                      ·
                        rfl

theorem cell23_7937773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_7937773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937773 prefixEnd_7937773 := by exact prefixLift 7937773
  have htrace : WordTrace (prefixWord ++ tailWord_7937773) baseStart_7937773 baseEnd_7937773 := by
    simpa [prefixWord, tailWord_7937773, baseEnd_7937773] using wordTrace_append hprefix tailTrace_7937773
  have hstable : (prefixWord ++ tailWord_7937773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937773).length < 2 ^ (prefixWord ++ tailWord_7937773).sum := by decide
  have hdescent : baseEnd_7937773 < baseStart_7937773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937775 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_7937775 : Nat := 118140960795 + 7937775 * 2 ^ 59
def prefixEnd_7937775 : Nat := 4983230072969 + 3 ^ 40 * 7937775 * 2
def baseEnd_7937775 : Nat := 4075893902242786152507343

theorem tailTrace_7937775 : CollatzResearch.WordTrace tailWord_7937775 prefixEnd_7937775 4075893902242786152507343 := by
  unfold tailWord_7937775
  simp only [CollatzResearch.WordTrace]
  refine ⟨289514438817804313885182779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193009625878536209256788519 289514438817804313885182779)
  ·
    refine ⟨434271658226706470827774169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289514438817804313885182779 434271658226706470827774169)
    ·
      refine ⟨325703743670029853120830627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434271658226706470827774169 325703743670029853120830627)
      ·
        refine ⟨488555615505044779681245941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325703743670029853120830627 488555615505044779681245941)
        ·
          refine ⟨45802088953597948095116807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 488555615505044779681245941 45802088953597948095116807)
          ·
            refine ⟨68703133430396922142675211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45802088953597948095116807 68703133430396922142675211)
            ·
              refine ⟨103054700145595383214012817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68703133430396922142675211 103054700145595383214012817)
              ·
                refine ⟨77291025109196537410509613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103054700145595383214012817 77291025109196537410509613)
                ·
                  refine ⟨28984134415948701528941105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77291025109196537410509613 28984134415948701528941105)
                  ·
                    refine ⟨21738100811961526146705829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28984134415948701528941105 21738100811961526146705829)
                    ·
                      refine ⟨4075893902242786152507343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21738100811961526146705829 4075893902242786152507343)
                      ·
                        rfl

theorem cell23_7937775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_7937775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937775 prefixEnd_7937775 := by exact prefixLift 7937775
  have htrace : WordTrace (prefixWord ++ tailWord_7937775) baseStart_7937775 baseEnd_7937775 := by
    simpa [prefixWord, tailWord_7937775, baseEnd_7937775] using wordTrace_append hprefix tailTrace_7937775
  have hstable : (prefixWord ++ tailWord_7937775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937775).length < 2 ^ (prefixWord ++ tailWord_7937775).sum := by decide
  have hdescent : baseEnd_7937775 < baseStart_7937775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937796 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_7937796 : Nat := 118140960795 + 7937796 * 2 ^ 59
def prefixEnd_7937796 : Nat := 4983230072969 + 3 ^ 40 * 7937796 * 2
def baseEnd_7937796 : Nat := 4075904685336530570344747

theorem tailTrace_7937796 : CollatzResearch.WordTrace tailWord_7937796 prefixEnd_7937796 4075904685336530570344747 := by
  unfold tailWord_7937796
  simp only [CollatzResearch.WordTrace]
  refine ⟨144757602375364117235848621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193010136500485489647798161 144757602375364117235848621)
  ·
    refine ⟨54284100890761543963443233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144757602375364117235848621 54284100890761543963443233)
    ·
      refine ⟨40713075668071157972582425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54284100890761543963443233 40713075668071157972582425)
      ·
        refine ⟨30534806751053368479436819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40713075668071157972582425 30534806751053368479436819)
        ·
          refine ⟨45802210126580052719155229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30534806751053368479436819 45802210126580052719155229)
          ·
            refine ⟨17175828797467519769683211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45802210126580052719155229 17175828797467519769683211)
            ·
              refine ⟨25763743196201279654524817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17175828797467519769683211 25763743196201279654524817)
              ·
                refine ⟨19322807397150959740893613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25763743196201279654524817 19322807397150959740893613)
                ·
                  refine ⟨7246052773931609902835105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19322807397150959740893613 7246052773931609902835105)
                  ·
                    refine ⟨5434539580448707427126329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246052773931609902835105 5434539580448707427126329)
                    ·
                      refine ⟨4075904685336530570344747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434539580448707427126329 4075904685336530570344747)
                      ·
                        rfl

theorem cell23_7937796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_7937796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937796 prefixEnd_7937796 := by exact prefixLift 7937796
  have htrace : WordTrace (prefixWord ++ tailWord_7937796) baseStart_7937796 baseEnd_7937796 := by
    simpa [prefixWord, tailWord_7937796, baseEnd_7937796] using wordTrace_append hprefix tailTrace_7937796
  have hstable : (prefixWord ++ tailWord_7937796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937796).length < 2 ^ (prefixWord ++ tailWord_7937796).sum := by decide
  have hdescent : baseEnd_7937796 < baseStart_7937796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937802 : List Nat := [3, 1, 2, 2, 1, 4, 3, 7]
def baseStart_7937802 : Nat := 118140960795 + 7937802 * 2 ^ 59
def prefixEnd_7937802 : Nat := 4983230072969 + 3 ^ 40 * 7937802 * 2
def baseEnd_7937802 : Nat := 150959546897053983217397

theorem tailTrace_7937802 : CollatzResearch.WordTrace tailWord_7937802 prefixEnd_7937802 150959546897053983217397 := by
  unfold tailWord_7937802
  simp only [CollatzResearch.WordTrace]
  refine ⟨72378855897176624374103915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193010282392470998330943773 72378855897176624374103915)
  ·
    refine ⟨108568283845764936561155873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72378855897176624374103915 108568283845764936561155873)
    ·
      refine ⟨81426212884323702420866905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108568283845764936561155873 81426212884323702420866905)
      ·
        refine ⟨61069659663242776815650179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81426212884323702420866905 61069659663242776815650179)
        ·
          refine ⟨91604489494864165223475269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61069659663242776815650179 91604489494864165223475269)
          ·
            refine ⟨17175841780287030979401613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91604489494864165223475269 17175841780287030979401613)
            ·
              refine ⟨6440940667607636617275605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17175841780287030979401613 6440940667607636617275605)
              ·
                refine ⟨150959546897053983217397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6440940667607636617275605 150959546897053983217397)
                ·
                  rfl

theorem cell23_7937802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_7937802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937802 prefixEnd_7937802 := by exact prefixLift 7937802
  have htrace : WordTrace (prefixWord ++ tailWord_7937802) baseStart_7937802 baseEnd_7937802 := by
    simpa [prefixWord, tailWord_7937802, baseEnd_7937802] using wordTrace_append hprefix tailTrace_7937802
  have hstable : (prefixWord ++ tailWord_7937802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937802).length < 2 ^ (prefixWord ++ tailWord_7937802).sum := by decide
  have hdescent : baseEnd_7937802 < baseStart_7937802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937813 : List Nat := [1, 3, 2, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_7937813 : Nat := 118140960795 + 7937813 * 2 ^ 59
def prefixEnd_7937813 : Nat := 4983230072969 + 3 ^ 40 * 7937813 * 2
def baseEnd_7937813 : Nat := 4075913414507657003832169

theorem tailTrace_7937813 : CollatzResearch.WordTrace tailWord_7937813 prefixEnd_7937813 4075913414507657003832169 := by
  unfold tailWord_7937813
  simp only [CollatzResearch.WordTrace]
  refine ⟨289515824791666646375066093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193010549861111097583377395 289515824791666646375066093)
  ·
    refine ⟨108568434296874992390649785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289515824791666646375066093 108568434296874992390649785)
    ·
      refine ⟨81426325722656244292987339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108568434296874992390649785 81426325722656244292987339)
      ·
        refine ⟨122139488583984366439481009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81426325722656244292987339 122139488583984366439481009)
        ·
          refine ⟨91604616437988274829610757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122139488583984366439481009 91604616437988274829610757)
          ·
            refine ⟨17175865582122801530552017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91604616437988274829610757 17175865582122801530552017)
            ·
              refine ⟨12881899186592101147914013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17175865582122801530552017 12881899186592101147914013)
              ·
                refine ⟨4830712194972037930467755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12881899186592101147914013 4830712194972037930467755)
                ·
                  refine ⟨7246068292458056895701633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830712194972037930467755 7246068292458056895701633)
                  ·
                    refine ⟨5434551219343542671776225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246068292458056895701633 5434551219343542671776225)
                    ·
                      refine ⟨4075913414507657003832169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434551219343542671776225 4075913414507657003832169)
                      ·
                        rfl

theorem cell23_7937813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_7937813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937813 prefixEnd_7937813 := by exact prefixLift 7937813
  have htrace : WordTrace (prefixWord ++ tailWord_7937813) baseStart_7937813 baseEnd_7937813 := by
    simpa [prefixWord, tailWord_7937813, baseEnd_7937813] using wordTrace_append hprefix tailTrace_7937813
  have hstable : (prefixWord ++ tailWord_7937813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937813).length < 2 ^ (prefixWord ++ tailWord_7937813).sum := by decide
  have hdescent : baseEnd_7937813 < baseStart_7937813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937829 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_7937829 : Nat := 118140960795 + 7937829 * 2 ^ 59
def prefixEnd_7937829 : Nat := 4983230072969 + 3 ^ 40 * 7937829 * 2
def baseEnd_7937829 : Nat := 4075921630198128941232095

theorem tailTrace_7937829 : CollatzResearch.WordTrace tailWord_7937829 prefixEnd_7937829 4075921630198128941232095 := by
  unfold tailWord_7937829
  simp only [CollatzResearch.WordTrace]
  refine ⟨289516408359608681107648541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193010938906405787405099027 289516408359608681107648541)
  ·
    refine ⟨108568653134853255415368203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289516408359608681107648541 108568653134853255415368203)
    ·
      refine ⟨162852979702279883123052305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108568653134853255415368203 162852979702279883123052305)
      ·
        refine ⟨122139734776709912342289229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162852979702279883123052305 122139734776709912342289229)
        ·
          refine ⟨45802400541266217128358461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122139734776709912342289229 45802400541266217128358461)
          ·
            refine ⟨17175900202974831423134423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45802400541266217128358461 17175900202974831423134423)
            ·
              refine ⟨25763850304462247134701635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17175900202974831423134423 25763850304462247134701635)
              ·
                refine ⟨38645775456693370702052453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25763850304462247134701635 38645775456693370702052453)
                ·
                  refine ⟨7246082898130007006634835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38645775456693370702052453 7246082898130007006634835)
                  ·
                    refine ⟨10869124347195010509952253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7246082898130007006634835 10869124347195010509952253)
                    ·
                      refine ⟨4075921630198128941232095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869124347195010509952253 4075921630198128941232095)
                      ·
                        rfl

theorem cell23_7937829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_7937829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937829 prefixEnd_7937829 := by exact prefixLift 7937829
  have htrace : WordTrace (prefixWord ++ tailWord_7937829) baseStart_7937829 baseEnd_7937829 := by
    simpa [prefixWord, tailWord_7937829, baseEnd_7937829] using wordTrace_append hprefix tailTrace_7937829
  have hstable : (prefixWord ++ tailWord_7937829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937829).length < 2 ^ (prefixWord ++ tailWord_7937829).sum := by decide
  have hdescent : baseEnd_7937829 < baseStart_7937829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937846 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7937846 : Nat := 118140960795 + 7937846 * 2 ^ 59
def prefixEnd_7937846 : Nat := 4983230072969 + 3 ^ 40 * 7937846 * 2
def baseEnd_7937846 : Nat := 4075930359369255374719517

theorem tailTrace_7937846 : CollatzResearch.WordTrace tailWord_7937846 prefixEnd_7937846 4075930359369255374719517 := by
  unfold tailWord_7937846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18094814275034193313188587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193011352267031395340678261 18094814275034193313188587)
  ·
    refine ⟨27142221412551289969782881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18094814275034193313188587 27142221412551289969782881)
    ·
      refine ⟨20356666059413467477337161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27142221412551289969782881 20356666059413467477337161)
      ·
        refine ⟨15267499544560100608002871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20356666059413467477337161 15267499544560100608002871)
        ·
          refine ⟨22901249316840150912004307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15267499544560100608002871 22901249316840150912004307)
          ·
            refine ⟨34351873975260226368006461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22901249316840150912004307 34351873975260226368006461)
            ·
              refine ⟨12881952740722584888002423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34351873975260226368006461 12881952740722584888002423)
              ·
                refine ⟨19322929111083877332003635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12881952740722584888002423 19322929111083877332003635)
                ·
                  refine ⟨28984393666625815998005453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19322929111083877332003635 28984393666625815998005453)
                  ·
                    refine ⟨10869147624984680999252045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28984393666625815998005453 10869147624984680999252045)
                    ·
                      refine ⟨4075930359369255374719517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869147624984680999252045 4075930359369255374719517)
                      ·
                        rfl

theorem cell23_7937846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7937846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937846 prefixEnd_7937846 := by exact prefixLift 7937846
  have htrace : WordTrace (prefixWord ++ tailWord_7937846) baseStart_7937846 baseEnd_7937846 := by
    simpa [prefixWord, tailWord_7937846, baseEnd_7937846] using wordTrace_append hprefix tailTrace_7937846
  have hstable : (prefixWord ++ tailWord_7937846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937846).length < 2 ^ (prefixWord ++ tailWord_7937846).sum := by decide
  have hdescent : baseEnd_7937846 < baseStart_7937846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937915 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7]
def baseStart_7937915 : Nat := 118140960795 + 7937915 * 2 ^ 59
def prefixEnd_7937915 : Nat := 4983230072969 + 3 ^ 40 * 7937915 * 2
def baseEnd_7937915 : Nat := 4075965789534415604756699

theorem tailTrace_7937915 : CollatzResearch.WordTrace tailWord_7937915 prefixEnd_7937915 4075965789534415604756699 := by
  unfold tailWord_7937915
  simp only [CollatzResearch.WordTrace]
  refine ⟨289519545037297117795279199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193013030024864745196852799 289519545037297117795279199)
  ·
    refine ⟨434279317555945676692918799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289519545037297117795279199 434279317555945676692918799)
    ·
      refine ⟨651418976333918515039378199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434279317555945676692918799 651418976333918515039378199)
      ·
        refine ⟨977128464500877772559067299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651418976333918515039378199 977128464500877772559067299)
        ·
          refine ⟨1465692696751316658838600949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977128464500877772559067299 1465692696751316658838600949)
          ·
            refine ⟨137408690320435936766118839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1465692696751316658838600949 137408690320435936766118839)
            ·
              refine ⟨206113035480653905149178259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137408690320435936766118839 206113035480653905149178259)
              ·
                refine ⟨309169553220980857723767389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206113035480653905149178259 309169553220980857723767389)
                ·
                  refine ⟨115938582457867821646412771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309169553220980857723767389 115938582457867821646412771)
                  ·
                    refine ⟨173907873686801732469619157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115938582457867821646412771 173907873686801732469619157)
                    ·
                      refine ⟨4075965789534415604756699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173907873686801732469619157 4075965789534415604756699)
                      ·
                        rfl

theorem cell23_7937915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_7937915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937915 prefixEnd_7937915 := by exact prefixLift 7937915
  have htrace : WordTrace (prefixWord ++ tailWord_7937915) baseStart_7937915 baseEnd_7937915 := by
    simpa [prefixWord, tailWord_7937915, baseEnd_7937915] using wordTrace_append hprefix tailTrace_7937915
  have hstable : (prefixWord ++ tailWord_7937915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937915).length < 2 ^ (prefixWord ++ tailWord_7937915).sum := by decide
  have hdescent : baseEnd_7937915 < baseStart_7937915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937935 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 6, 8]
def baseStart_7937935 : Nat := 118140960795 + 7937935 * 2 ^ 59
def prefixEnd_7937935 : Nat := 4983230072969 + 3 ^ 40 * 7937935 * 2
def baseEnd_7937935 : Nat := 1358658686382501842168869

theorem tailTrace_7937935 : CollatzResearch.WordTrace tailWord_7937935 prefixEnd_7937935 1358658686382501842168869 := by
  unfold tailWord_7937935
  simp only [CollatzResearch.WordTrace]
  refine ⟨289520274497224661211007259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193013516331483107474004839 289520274497224661211007259)
  ·
    refine ⟨434280411745836991816510889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289520274497224661211007259 434280411745836991816510889)
    ·
      refine ⟨325710308809377743862383167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434280411745836991816510889 325710308809377743862383167)
      ·
        refine ⟨488565463214066615793574751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325710308809377743862383167 488565463214066615793574751)
        ·
          refine ⟨732848194821099923690362127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488565463214066615793574751 732848194821099923690362127)
          ·
            refine ⟨1099272292231649885535543191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732848194821099923690362127 1099272292231649885535543191)
            ·
              refine ⟨1648908438347474828303314787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099272292231649885535543191 1648908438347474828303314787)
              ·
                refine ⟨2473362657521212242454972181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648908438347474828303314787 2473362657521212242454972181)
                ·
                  refine ⟨115938874571306823865076821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2473362657521212242454972181 115938874571306823865076821)
                  ·
                    refine ⟨1358658686382501842168869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115938874571306823865076821 1358658686382501842168869)
                    ·
                      rfl

theorem cell23_7937935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_7937935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937935 prefixEnd_7937935 := by exact prefixLift 7937935
  have htrace : WordTrace (prefixWord ++ tailWord_7937935) baseStart_7937935 baseEnd_7937935 := by
    simpa [prefixWord, tailWord_7937935, baseEnd_7937935] using wordTrace_append hprefix tailTrace_7937935
  have hstable : (prefixWord ++ tailWord_7937935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937935).length < 2 ^ (prefixWord ++ tailWord_7937935).sum := by decide
  have hdescent : baseEnd_7937935 < baseStart_7937935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7937969 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 5, 4]
def baseStart_7937969 : Nat := 118140960795 + 7937969 * 2 ^ 59
def prefixEnd_7937969 : Nat := 4983230072969 + 3 ^ 40 * 7937969 * 2
def baseEnd_7937969 : Nat := 1358664505829919464493817

theorem tailTrace_7937969 : CollatzResearch.WordTrace tailWord_7937969 prefixEnd_7937969 1358664505829919464493817 := by
  unfold tailWord_7937969
  simp only [CollatzResearch.WordTrace]
  refine ⟨289521514579101485017744961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193014343052734323345163307 289521514579101485017744961)
  ·
    refine ⟨217141135934326113763308721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289521514579101485017744961 217141135934326113763308721)
    ·
      refine ⟨162855851950744585322481541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217141135934326113763308721 162855851950744585322481541)
      ·
        refine ⟨30535472240764609747965289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162855851950744585322481541 30535472240764609747965289)
        ·
          refine ⟨22901604180573457310973967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30535472240764609747965289 22901604180573457310973967)
          ·
            refine ⟨34352406270860185966460951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22901604180573457310973967 34352406270860185966460951)
            ·
              refine ⟨51528609406290278949691427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34352406270860185966460951 51528609406290278949691427)
              ·
                refine ⟨77292914109435418424537141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51528609406290278949691427 77292914109435418424537141)
                ·
                  refine ⟨7246210697759570477300357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77292914109435418424537141 7246210697759570477300357)
                  ·
                    refine ⟨1358664505829919464493817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7246210697759570477300357 1358664505829919464493817)
                    ·
                      rfl

theorem cell23_7937969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_7937969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7937969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7937969 prefixEnd_7937969 := by exact prefixLift 7937969
  have htrace : WordTrace (prefixWord ++ tailWord_7937969) baseStart_7937969 baseEnd_7937969 := by
    simpa [prefixWord, tailWord_7937969, baseEnd_7937969] using wordTrace_append hprefix tailTrace_7937969
  have hstable : (prefixWord ++ tailWord_7937969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7937969).length < 2 ^ (prefixWord ++ tailWord_7937969).sum := by decide
  have hdescent : baseEnd_7937969 < baseStart_7937969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7937969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938026 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_7938026 : Nat := 118140960795 + 7938026 * 2 ^ 59
def prefixEnd_7938026 : Nat := 4983230072969 + 3 ^ 40 * 7938026 * 2
def baseEnd_7938026 : Nat := 4076022785887064670468689

theorem tailTrace_7938026 : CollatzResearch.WordTrace tailWord_7938026 prefixEnd_7938026 4076022785887064670468689 := by
  unfold tailWord_7938026
  simp only [CollatzResearch.WordTrace]
  refine ⟨72380898384973745938142483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193015729026596655835046621 72380898384973745938142483)
  ·
    refine ⟨108571347577460618907213725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72380898384973745938142483 108571347577460618907213725)
    ·
      refine ⟨40714255341547732090205147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108571347577460618907213725 40714255341547732090205147)
      ·
        refine ⟨61071383012321598135307721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40714255341547732090205147 61071383012321598135307721)
        ·
          refine ⟨45803537259241198601480791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61071383012321598135307721 45803537259241198601480791)
          ·
            refine ⟨68705305888861797902221187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45803537259241198601480791 68705305888861797902221187)
            ·
              refine ⟨103057958833292696853331781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68705305888861797902221187 103057958833292696853331781)
              ·
                refine ⟨19323367281242380659999709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103057958833292696853331781 19323367281242380659999709)
                ·
                  refine ⟨7246262730465892747499891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19323367281242380659999709 7246262730465892747499891)
                  ·
                    refine ⟨10869394095698839121249837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7246262730465892747499891 10869394095698839121249837)
                    ·
                      refine ⟨4076022785887064670468689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869394095698839121249837 4076022785887064670468689)
                      ·
                        rfl

theorem cell23_7938026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_7938026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938026 prefixEnd_7938026 := by exact prefixLift 7938026
  have htrace : WordTrace (prefixWord ++ tailWord_7938026) baseStart_7938026 baseEnd_7938026 := by
    simpa [prefixWord, tailWord_7938026, baseEnd_7938026] using wordTrace_append hprefix tailTrace_7938026
  have hstable : (prefixWord ++ tailWord_7938026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938026).length < 2 ^ (prefixWord ++ tailWord_7938026).sum := by decide
  have hdescent : baseEnd_7938026 < baseStart_7938026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938043 : List Nat := [1, 1, 1, 1, 1, 3, 7, 3, 1, 1, 3]
def baseStart_7938043 : Nat := 118140960795 + 7938043 * 2 ^ 59
def prefixEnd_7938043 : Nat := 4983230072969 + 3 ^ 40 * 7938043 * 2
def baseEnd_7938043 : Nat := 4076031515058191103956111

theorem tailTrace_7938043 : CollatzResearch.WordTrace tailWord_7938043 prefixEnd_7938043 4076031515058191103956111 := by
  unfold tailWord_7938043
  simp only [CollatzResearch.WordTrace]
  refine ⟨289524213580833395655938783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193016142387222263770625855 289524213580833395655938783)
  ·
    refine ⟨434286320371250093483908175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289524213580833395655938783 434286320371250093483908175)
    ·
      refine ⟨651429480556875140225862263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434286320371250093483908175 651429480556875140225862263)
      ·
        refine ⟨977144220835312710338793395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651429480556875140225862263 977144220835312710338793395)
        ·
          refine ⟨1465716331252969065508190093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977144220835312710338793395 1465716331252969065508190093)
          ·
            refine ⟨549643624219863399565571285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1465716331252969065508190093 549643624219863399565571285)
            ·
              refine ⟨12882272442653048427318077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 549643624219863399565571285 12882272442653048427318077)
              ·
                refine ⟨4830852165994893160244279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12882272442653048427318077 4830852165994893160244279)
                ·
                  refine ⟨7246278248992339740366419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830852165994893160244279 7246278248992339740366419)
                  ·
                    refine ⟨10869417373488509610549629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7246278248992339740366419 10869417373488509610549629)
                    ·
                      refine ⟨4076031515058191103956111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869417373488509610549629 4076031515058191103956111)
                      ·
                        rfl

theorem cell23_7938043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 1, 3].length) (baseStart_7938043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938043 prefixEnd_7938043 := by exact prefixLift 7938043
  have htrace : WordTrace (prefixWord ++ tailWord_7938043) baseStart_7938043 baseEnd_7938043 := by
    simpa [prefixWord, tailWord_7938043, baseEnd_7938043] using wordTrace_append hprefix tailTrace_7938043
  have hstable : (prefixWord ++ tailWord_7938043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938043).length < 2 ^ (prefixWord ++ tailWord_7938043).sum := by decide
  have hdescent : baseEnd_7938043 < baseStart_7938043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938054 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7938054 : Nat := 118140960795 + 7938054 * 2 ^ 59
def prefixEnd_7938054 : Nat := 4983230072969 + 3 ^ 40 * 7938054 * 2
def baseEnd_7938054 : Nat := 1358679054448463520306187

theorem tailTrace_7938054 : CollatzResearch.WordTrace tailWord_7938054 prefixEnd_7938054 1358679054448463520306187 := by
  unfold tailWord_7938054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9047644211993548266705913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193016409855862363023059477 9047644211993548266705913)
  ·
    refine ⟨6785733158995161200029435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9047644211993548266705913 6785733158995161200029435)
    ·
      refine ⟨10178599738492741800044153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6785733158995161200029435 10178599738492741800044153)
      ·
        refine ⟨7633949803869556350033115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10178599738492741800044153 7633949803869556350033115)
        ·
          refine ⟨11450924705804334525049673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7633949803869556350033115 11450924705804334525049673)
          ·
            refine ⟨8588193529353250893787255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11450924705804334525049673 8588193529353250893787255)
            ·
              refine ⟨12882290294029876340680883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588193529353250893787255 12882290294029876340680883)
              ·
                refine ⟨19323435441044814511021325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12882290294029876340680883 19323435441044814511021325)
                ·
                  refine ⟨7246288290391805441632997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19323435441044814511021325 7246288290391805441632997)
                  ·
                    refine ⟨1358679054448463520306187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7246288290391805441632997 1358679054448463520306187)
                    ·
                      rfl

theorem cell23_7938054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7938054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938054 prefixEnd_7938054 := by exact prefixLift 7938054
  have htrace : WordTrace (prefixWord ++ tailWord_7938054) baseStart_7938054 baseEnd_7938054 := by
    simpa [prefixWord, tailWord_7938054, baseEnd_7938054] using wordTrace_append hprefix tailTrace_7938054
  have hstable : (prefixWord ++ tailWord_7938054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938054).length < 2 ^ (prefixWord ++ tailWord_7938054).sum := by decide
  have hdescent : baseEnd_7938054 < baseStart_7938054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938059 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 4, 4]
def baseStart_7938059 : Nat := 118140960795 + 7938059 * 2 ^ 59
def prefixEnd_7938059 : Nat := 4983230072969 + 3 ^ 40 * 7938059 * 2
def baseEnd_7938059 : Nat := 1358679910249554347118679

theorem tailTrace_7938059 : CollatzResearch.WordTrace tailWord_7938059 prefixEnd_7938059 1358679910249554347118679 := by
  unfold tailWord_7938059
  simp only [CollatzResearch.WordTrace]
  refine ⟨289524797148775430388521231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193016531432516953592347487 289524797148775430388521231)
  ·
    refine ⟨434287195723163145582781847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289524797148775430388521231 434287195723163145582781847)
    ·
      refine ⟨651430793584744718374172771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434287195723163145582781847 651430793584744718374172771)
      ·
        refine ⟨977146190377117077561259157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651430793584744718374172771 977146190377117077561259157)
        ·
          refine ⟨45803727673927363010684023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 977146190377117077561259157 45803727673927363010684023)
          ·
            refine ⟨68705591510891044516026035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45803727673927363010684023 68705591510891044516026035)
            ·
              refine ⟨103058387266336566774039053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68705591510891044516026035 103058387266336566774039053)
              ·
                refine ⟨38646895224876212540264645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103058387266336566774039053 38646895224876212540264645)
                ·
                  refine ⟨7246292854664289851299621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38646895224876212540264645 7246292854664289851299621)
                  ·
                    refine ⟨1358679910249554347118679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7246292854664289851299621 1358679910249554347118679)
                    ·
                      rfl

theorem cell23_7938059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 4].length) (baseStart_7938059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938059 prefixEnd_7938059 := by exact prefixLift 7938059
  have htrace : WordTrace (prefixWord ++ tailWord_7938059) baseStart_7938059 baseEnd_7938059 := by
    simpa [prefixWord, tailWord_7938059, baseEnd_7938059] using wordTrace_append hprefix tailTrace_7938059
  have hstable : (prefixWord ++ tailWord_7938059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938059).length < 2 ^ (prefixWord ++ tailWord_7938059).sum := by decide
  have hdescent : baseEnd_7938059 < baseStart_7938059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938060 : List Nat := [2, 2, 1, 2, 3, 1, 5, 2, 1, 1, 3]
def baseStart_7938060 : Nat := 118140960795 + 7938060 * 2 ^ 59
def prefixEnd_7938060 : Nat := 4983230072969 + 3 ^ 40 * 7938060 * 2
def baseEnd_7938060 : Nat := 4076040244229317537443533

theorem tailTrace_7938060 : CollatzResearch.WordTrace tailWord_7938060 prefixEnd_7938060 4076040244229317537443533 := by
  unfold tailWord_7938060
  simp only [CollatzResearch.WordTrace]
  refine ⟨144762416810885903779653817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193016555747847871706205089 144762416810885903779653817)
  ·
    refine ⟨108571812608164427834740363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144762416810885903779653817 108571812608164427834740363)
    ·
      refine ⟨162857718912246641752110545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108571812608164427834740363 162857718912246641752110545)
      ·
        refine ⟨122143289184184981314082909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162857718912246641752110545 122143289184184981314082909)
        ·
          refine ⟨45803733444069367992781091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122143289184184981314082909 45803733444069367992781091)
          ·
            refine ⟨68705600166104051989171637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45803733444069367992781091 68705600166104051989171637)
            ·
              refine ⟨6441150015572254873984841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68705600166104051989171637 6441150015572254873984841)
              ·
                refine ⟨4830862511679191155488631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6441150015572254873984841 4830862511679191155488631)
                ·
                  refine ⟨7246293767518786733232947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830862511679191155488631 7246293767518786733232947)
                  ·
                    refine ⟨10869440651278180099849421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7246293767518786733232947 10869440651278180099849421)
                    ·
                      refine ⟨4076040244229317537443533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869440651278180099849421 4076040244229317537443533)
                      ·
                        rfl

theorem cell23_7938060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_7938060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938060 prefixEnd_7938060 := by exact prefixLift 7938060
  have htrace : WordTrace (prefixWord ++ tailWord_7938060) baseStart_7938060 baseEnd_7938060 := by
    simpa [prefixWord, tailWord_7938060, baseEnd_7938060] using wordTrace_append hprefix tailTrace_7938060
  have hstable : (prefixWord ++ tailWord_7938060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938060).length < 2 ^ (prefixWord ++ tailWord_7938060).sum := by decide
  have hdescent : baseEnd_7938060 < baseStart_7938060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938079 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_7938079 : Nat := 118140960795 + 7938079 * 2 ^ 59
def prefixEnd_7938079 : Nat := 4983230072969 + 3 ^ 40 * 7938079 * 2
def baseEnd_7938079 : Nat := 4076050000361752963105945

theorem tailTrace_7938079 : CollatzResearch.WordTrace tailWord_7938079 prefixEnd_7938079 4076050000361752963105945 := by
  unfold tailWord_7938079
  simp only [CollatzResearch.WordTrace]
  refine ⟨289525526608702973804249291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193017017739135315869499527 289525526608702973804249291)
  ·
    refine ⟨434288289913054460706373937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289525526608702973804249291 434288289913054460706373937)
    ·
      refine ⟨325716217434790845529780453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434288289913054460706373937 325716217434790845529780453)
      ·
        refine ⟨61071790769023283536833835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325716217434790845529780453 61071790769023283536833835)
        ·
          refine ⟨91607686153534925305250753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61071790769023283536833835 91607686153534925305250753)
          ·
            refine ⟨68705764615151193978938065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91607686153534925305250753 68705764615151193978938065)
            ·
              refine ⟨51529323461363395484203549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68705764615151193978938065 51529323461363395484203549)
              ·
                refine ⟨19323496298011273306576331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51529323461363395484203549 19323496298011273306576331)
                ·
                  refine ⟨28985244447016909959864497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19323496298011273306576331 28985244447016909959864497)
                  ·
                    refine ⟨21738933335262682469898373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28985244447016909959864497 21738933335262682469898373)
                    ·
                      refine ⟨4076050000361752963105945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21738933335262682469898373 4076050000361752963105945)
                      ·
                        rfl

theorem cell23_7938079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_7938079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938079 prefixEnd_7938079 := by exact prefixLift 7938079
  have htrace : WordTrace (prefixWord ++ tailWord_7938079) baseStart_7938079 baseEnd_7938079 := by
    simpa [prefixWord, tailWord_7938079, baseEnd_7938079] using wordTrace_append hprefix tailTrace_7938079
  have hstable : (prefixWord ++ tailWord_7938079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938079).length < 2 ^ (prefixWord ++ tailWord_7938079).sum := by decide
  have hdescent : baseEnd_7938079 < baseStart_7938079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938099 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 3]
def baseStart_7938099 : Nat := 118140960795 + 7938099 * 2 ^ 59
def prefixEnd_7938099 : Nat := 4983230072969 + 3 ^ 40 * 7938099 * 2
def baseEnd_7938099 : Nat := 4076060269974842884855853

theorem tailTrace_7938099 : CollatzResearch.WordTrace tailWord_7938099 prefixEnd_7938099 4076060269974842884855853 := by
  unfold tailWord_7938099
  simp only [CollatzResearch.WordTrace]
  refine ⟨289526256068630517219977351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193017504045753678146651567 289526256068630517219977351)
  ·
    refine ⟨434289384102945775829966027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289526256068630517219977351 434289384102945775829966027)
    ·
      refine ⟨651434076154418663744949041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434289384102945775829966027 651434076154418663744949041)
      ·
        refine ⟨488575557115813997808711781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651434076154418663744949041 488575557115813997808711781)
        ·
          refine ⟨91607916959215124589133459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488575557115813997808711781 91607916959215124589133459)
          ·
            refine ⟨137411875438822686883700189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91607916959215124589133459 137411875438822686883700189)
            ·
              refine ⟨51529453289558507581387571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137411875438822686883700189 51529453289558507581387571)
              ·
                refine ⟨77294179934337761372081357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51529453289558507581387571 77294179934337761372081357)
                ·
                  refine ⟨28985317475376660514530509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77294179934337761372081357 28985317475376660514530509)
                  ·
                    refine ⟨10869494053266247692948941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28985317475376660514530509 10869494053266247692948941)
                    ·
                      refine ⟨4076060269974842884855853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869494053266247692948941 4076060269974842884855853)
                      ·
                        rfl

theorem cell23_7938099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_7938099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938099 prefixEnd_7938099 := by exact prefixLift 7938099
  have htrace : WordTrace (prefixWord ++ tailWord_7938099) baseStart_7938099 baseEnd_7938099 := by
    simpa [prefixWord, tailWord_7938099, baseEnd_7938099] using wordTrace_append hprefix tailTrace_7938099
  have hstable : (prefixWord ++ tailWord_7938099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938099).length < 2 ^ (prefixWord ++ tailWord_7938099).sum := by decide
  have hdescent : baseEnd_7938099 < baseStart_7938099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938110 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7938110 : Nat := 118140960795 + 7938110 * 2 ^ 59
def prefixEnd_7938110 : Nat := 4983230072969 + 3 ^ 40 * 7938110 * 2
def baseEnd_7938110 : Nat := 1358688639420680780606101

theorem tailTrace_7938110 : CollatzResearch.WordTrace tailWord_7938110 prefixEnd_7938110 1358688639420680780606101 := by
  unfold tailWord_7938110
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190832158948833262328473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193017771514393777399085189 36190832158948833262328473)
  ·
    refine ⟨27143124119211624946746355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36190832158948833262328473 27143124119211624946746355)
    ·
      refine ⟨40714686178817437420119533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27143124119211624946746355 40714686178817437420119533)
      ·
        refine ⟨15268007317056539032544825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40714686178817437420119533 15268007317056539032544825)
        ·
          refine ⟨11451005487792404274408619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15268007317056539032544825 11451005487792404274408619)
          ·
            refine ⟨17176508231688606411612929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11451005487792404274408619 17176508231688606411612929)
            ·
              refine ⟨12882381173766454808709697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17176508231688606411612929 12882381173766454808709697)
              ·
                refine ⟨9661785880324841106532273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12882381173766454808709697 9661785880324841106532273)
                ·
                  refine ⟨7246339410243630829899205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9661785880324841106532273 7246339410243630829899205)
                  ·
                    refine ⟨1358688639420680780606101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7246339410243630829899205 1358688639420680780606101)
                    ·
                      rfl

theorem cell23_7938110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7938110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938110 prefixEnd_7938110 := by exact prefixLift 7938110
  have htrace : WordTrace (prefixWord ++ tailWord_7938110) baseStart_7938110 baseEnd_7938110 := by
    simpa [prefixWord, tailWord_7938110, baseEnd_7938110] using wordTrace_append hprefix tailTrace_7938110
  have hstable : (prefixWord ++ tailWord_7938110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938110).length < 2 ^ (prefixWord ++ tailWord_7938110).sum := by decide
  have hdescent : baseEnd_7938110 < baseStart_7938110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938133 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7938133 : Nat := 118140960795 + 7938133 * 2 ^ 59
def prefixEnd_7938133 : Nat := 4983230072969 + 3 ^ 40 * 7938133 * 2
def baseEnd_7938133 : Nat := 4076077728317095751830697

theorem tailTrace_7938133 : CollatzResearch.WordTrace tailWord_7938133 prefixEnd_7938133 4076077728317095751830697 := by
  unfold tailWord_7938133
  simp only [CollatzResearch.WordTrace]
  refine ⟨289527496150507341026715053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193018330767004894017810035 289527496150507341026715053)
  ·
    refine ⟨108572811056440252885018145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289527496150507341026715053 108572811056440252885018145)
    ·
      refine ⟨81429608292330189663763609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108572811056440252885018145 81429608292330189663763609)
      ·
        refine ⟨61072206219247642247822707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81429608292330189663763609 61072206219247642247822707)
        ·
          refine ⟨91608309328871463371734061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61072206219247642247822707 91608309328871463371734061)
          ·
            refine ⟨34353115998326798764400273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91608309328871463371734061 34353115998326798764400273)
            ·
              refine ⟨25764836998745099073300205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34353115998326798764400273 25764836998745099073300205)
              ·
                refine ⟨9661813874529412152487577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25764836998745099073300205 9661813874529412152487577)
                ·
                  refine ⟨7246360405897059114365683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9661813874529412152487577 7246360405897059114365683)
                  ·
                    refine ⟨10869540608845588671548525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7246360405897059114365683 10869540608845588671548525)
                    ·
                      refine ⟨4076077728317095751830697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869540608845588671548525 4076077728317095751830697)
                      ·
                        rfl

theorem cell23_7938133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7938133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938133 prefixEnd_7938133 := by exact prefixLift 7938133
  have htrace : WordTrace (prefixWord ++ tailWord_7938133) baseStart_7938133 baseEnd_7938133 := by
    simpa [prefixWord, tailWord_7938133, baseEnd_7938133] using wordTrace_append hprefix tailTrace_7938133
  have hstable : (prefixWord ++ tailWord_7938133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938133).length < 2 ^ (prefixWord ++ tailWord_7938133).sum := by decide
  have hdescent : baseEnd_7938133 < baseStart_7938133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938160 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 1, 3, 2]
def baseStart_7938160 : Nat := 118140960795 + 7938160 * 2 ^ 59
def prefixEnd_7938160 : Nat := 4983230072969 + 3 ^ 40 * 7938160 * 2
def baseEnd_7938160 : Nat := 4076091592294767146193073

theorem tailTrace_7938160 : CollatzResearch.WordTrace tailWord_7938160 prefixEnd_7938160 4076091592294767146193073 := by
  unfold tailWord_7938160
  simp only [CollatzResearch.WordTrace]
  refine ⟨144764240460704762318973967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193018987280939683091965289 144764240460704762318973967)
  ·
    refine ⟨217146360691057143478460951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144764240460704762318973967 217146360691057143478460951)
    ·
      refine ⟨325719541036585715217691427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217146360691057143478460951 325719541036585715217691427)
      ·
        refine ⟨488579311554878572826537141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325719541036585715217691427 488579311554878572826537141)
        ·
          refine ⟨45804310458269866202487857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 488579311554878572826537141 45804310458269866202487857)
          ·
            refine ⟨34353232843702399651865893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45804310458269866202487857 34353232843702399651865893)
            ·
              refine ⟨6441231158194199934724855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34353232843702399651865893 6441231158194199934724855)
              ·
                refine ⟨9661846737291299902087283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441231158194199934724855 9661846737291299902087283)
                ·
                  refine ⟨14492770105936949853130925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9661846737291299902087283 14492770105936949853130925)
                  ·
                    refine ⟨5434788789726356194924097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14492770105936949853130925 5434788789726356194924097)
                    ·
                      refine ⟨4076091592294767146193073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434788789726356194924097 4076091592294767146193073)
                      ·
                        rfl

theorem cell23_7938160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 3, 2].length) (baseStart_7938160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938160 prefixEnd_7938160 := by exact prefixLift 7938160
  have htrace : WordTrace (prefixWord ++ tailWord_7938160) baseStart_7938160 baseEnd_7938160 := by
    simpa [prefixWord, tailWord_7938160, baseEnd_7938160] using wordTrace_append hprefix tailTrace_7938160
  have hstable : (prefixWord ++ tailWord_7938160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938160).length < 2 ^ (prefixWord ++ tailWord_7938160).sum := by decide
  have hdescent : baseEnd_7938160 < baseStart_7938160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938166 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_7938166 : Nat := 118140960795 + 7938166 * 2 ^ 59
def prefixEnd_7938166 : Nat := 4983230072969 + 3 ^ 40 * 7938166 * 2
def baseEnd_7938166 : Nat := 1358698224392898040906015

theorem tailTrace_7938166 : CollatzResearch.WordTrace tailWord_7938166 prefixEnd_7938166 1358698224392898040906015 := by
  unfold tailWord_7938166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18095543734961736728916647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193019133172925191775110901 18095543734961736728916647)
  ·
    refine ⟨27143315602442605093374971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18095543734961736728916647 27143315602442605093374971)
    ·
      refine ⟨40714973403663907640062457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27143315602442605093374971 40714973403663907640062457)
      ·
        refine ⟨30536230052747930730046843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40714973403663907640062457 30536230052747930730046843)
        ·
          refine ⟨45804345079121896095070265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30536230052747930730046843 45804345079121896095070265)
          ·
            refine ⟨34353258809341422071302699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45804345079121896095070265 34353258809341422071302699)
            ·
              refine ⟨51529888214012133106954049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34353258809341422071302699 51529888214012133106954049)
              ·
                refine ⟨38647416160509099830215537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51529888214012133106954049 38647416160509099830215537)
                ·
                  refine ⟨28985562120381824872661653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38647416160509099830215537 28985562120381824872661653)
                  ·
                    refine ⟨1358698224392898040906015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28985562120381824872661653 1358698224392898040906015)
                    ·
                      rfl

theorem cell23_7938166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_7938166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938166 prefixEnd_7938166 := by exact prefixLift 7938166
  have htrace : WordTrace (prefixWord ++ tailWord_7938166) baseStart_7938166 baseEnd_7938166 := by
    simpa [prefixWord, tailWord_7938166, baseEnd_7938166] using wordTrace_append hprefix tailTrace_7938166
  have hstable : (prefixWord ++ tailWord_7938166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938166).length < 2 ^ (prefixWord ++ tailWord_7938166).sum := by decide
  have hdescent : baseEnd_7938166 < baseStart_7938166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938179 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 7]
def baseStart_7938179 : Nat := 118140960795 + 7938179 * 2 ^ 59
def prefixEnd_7938179 : Nat := 4983230072969 + 3 ^ 40 * 7938179 * 2
def baseEnd_7938179 : Nat := 452900149825244730206165

theorem tailTrace_7938179 : CollatzResearch.WordTrace tailWord_7938179 prefixEnd_7938179 452900149825244730206165 := by
  unfold tailWord_7938179
  simp only [CollatzResearch.WordTrace]
  refine ⟨289529173908340690882889591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193019449272227127255259727 289529173908340690882889591)
  ·
    refine ⟨434293760862511036324334387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289529173908340690882889591 434293760862511036324334387)
    ·
      refine ⟨651440641293766554486501581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434293760862511036324334387 651440641293766554486501581)
      ·
        refine ⟨244290240485162457932438093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651440641293766554486501581 244290240485162457932438093)
        ·
          refine ⟨91608840181935921724664285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244290240485162457932438093 91608840181935921724664285)
          ·
            refine ⟨34353315068225970646749107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91608840181935921724664285 34353315068225970646749107)
            ·
              refine ⟨51529972602338955970123661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34353315068225970646749107 51529972602338955970123661)
              ·
                refine ⟨19323739725877108488796373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51529972602338955970123661 19323739725877108488796373)
                ·
                  refine ⟨452900149825244730206165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19323739725877108488796373 452900149825244730206165)
                  ·
                    rfl

theorem cell23_7938179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 7].length) (baseStart_7938179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938179 prefixEnd_7938179 := by exact prefixLift 7938179
  have htrace : WordTrace (prefixWord ++ tailWord_7938179) baseStart_7938179 baseEnd_7938179 := by
    simpa [prefixWord, tailWord_7938179, baseEnd_7938179] using wordTrace_append hprefix tailTrace_7938179
  have hstable : (prefixWord ++ tailWord_7938179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938179).length < 2 ^ (prefixWord ++ tailWord_7938179).sum := by decide
  have hdescent : baseEnd_7938179 < baseStart_7938179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938186 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7938186 : Nat := 118140960795 + 7938186 * 2 ^ 59
def prefixEnd_7938186 : Nat := 4983230072969 + 3 ^ 40 * 7938186 * 2
def baseEnd_7938186 : Nat := 4076104942791784044467953

theorem tailTrace_7938186 : CollatzResearch.WordTrace tailWord_7938186 prefixEnd_7938186 4076104942791784044467953 := by
  unfold tailWord_7938186
  simp only [CollatzResearch.WordTrace]
  refine ⟨72382357304828832769598603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193019619479543554052262941 72382357304828832769598603)
  ·
    refine ⟨108573535957243249154397905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72382357304828832769598603 108573535957243249154397905)
    ·
      refine ⟨81430151967932436865798429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108573535957243249154397905 81430151967932436865798429)
      ·
        refine ⟨30536306987974663824674411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81430151967932436865798429 30536306987974663824674411)
        ·
          refine ⟨45804460481961995737011617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30536306987974663824674411 45804460481961995737011617)
          ·
            refine ⟨34353345361471496802758713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45804460481961995737011617 34353345361471496802758713)
            ·
              refine ⟨25765009021103622602069035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34353345361471496802758713 25765009021103622602069035)
              ·
                refine ⟨38647513531655433903103553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25765009021103622602069035 38647513531655433903103553)
                ·
                  refine ⟨28985635148741575427327665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38647513531655433903103553 28985635148741575427327665)
                  ·
                    refine ⟨21739226361556181570495749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28985635148741575427327665 21739226361556181570495749)
                    ·
                      refine ⟨4076104942791784044467953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21739226361556181570495749 4076104942791784044467953)
                      ·
                        rfl

theorem cell23_7938186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7938186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938186 prefixEnd_7938186 := by exact prefixLift 7938186
  have htrace : WordTrace (prefixWord ++ tailWord_7938186) baseStart_7938186 baseEnd_7938186 := by
    simpa [prefixWord, tailWord_7938186, baseEnd_7938186] using wordTrace_append hprefix tailTrace_7938186
  have hstable : (prefixWord ++ tailWord_7938186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938186).length < 2 ^ (prefixWord ++ tailWord_7938186).sum := by decide
  have hdescent : baseEnd_7938186 < baseStart_7938186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938226 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_7938226 : Nat := 118140960795 + 7938226 * 2 ^ 59
def prefixEnd_7938226 : Nat := 4983230072969 + 3 ^ 40 * 7938226 * 2
def baseEnd_7938226 : Nat := 1358708494005987962655923

theorem tailTrace_7938226 : CollatzResearch.WordTrace tailWord_7938226 prefixEnd_7938226 1358708494005987962655923 := by
  unfold tailWord_7938226
  simp only [CollatzResearch.WordTrace]
  refine ⟨72382722034792604477462633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193020592092780278606567021 72382722034792604477462633)
  ·
    refine ⟨54287041526094453358096975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72382722034792604477462633 54287041526094453358096975)
    ·
      refine ⟨81430562289141680037145463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54287041526094453358096975 81430562289141680037145463)
      ·
        refine ⟨122145843433712520055718195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81430562289141680037145463 122145843433712520055718195)
        ·
          refine ⟨183218765150568780083577293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122145843433712520055718195 183218765150568780083577293)
          ·
            refine ⟨68707036931463292531341485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183218765150568780083577293 68707036931463292531341485)
            ·
              refine ⟨25765138849298734699253057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68707036931463292531341485 25765138849298734699253057)
              ·
                refine ⟨19323854136974051024439793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25765138849298734699253057 19323854136974051024439793)
                ·
                  refine ⟨14492890602730538268329845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19323854136974051024439793 14492890602730538268329845)
                  ·
                    refine ⟨1358708494005987962655923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14492890602730538268329845 1358708494005987962655923)
                    ·
                      rfl

theorem cell23_7938226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_7938226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938226 prefixEnd_7938226 := by exact prefixLift 7938226
  have htrace : WordTrace (prefixWord ++ tailWord_7938226) baseStart_7938226 baseEnd_7938226 := by
    simpa [prefixWord, tailWord_7938226, baseEnd_7938226] using wordTrace_append hprefix tailTrace_7938226
  have hstable : (prefixWord ++ tailWord_7938226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938226).length < 2 ^ (prefixWord ++ tailWord_7938226).sum := by decide
  have hdescent : baseEnd_7938226 < baseStart_7938226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938241 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7938241 : Nat := 118140960795 + 7938241 * 2 ^ 59
def prefixEnd_7938241 : Nat := 4983230072969 + 3 ^ 40 * 7938241 * 2
def baseEnd_7938241 : Nat := 4076133184227781329280201

theorem tailTrace_7938241 : CollatzResearch.WordTrace tailWord_7938241 prefixEnd_7938241 4076133184227781329280201 := by
  unfold tailWord_7938241
  simp only [CollatzResearch.WordTrace]
  refine ⟨289531435234116075471646577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193020956822744050314431051 289531435234116075471646577)
  ·
    refine ⟨217148576425587056603734933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289531435234116075471646577 217148576425587056603734933)
    ·
      refine ⟨10178839519949393278300075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217148576425587056603734933 10178839519949393278300075)
      ·
        refine ⟨15268259279924089917450113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10178839519949393278300075 15268259279924089917450113)
        ·
          refine ⟨11451194459943067438087585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15268259279924089917450113 11451194459943067438087585)
          ·
            refine ⟨8588395844957300578565689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11451194459943067438087585 8588395844957300578565689)
            ·
              refine ⟨6441296883717975433924267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8588395844957300578565689 6441296883717975433924267)
              ·
                refine ⟨9661945325576963150886401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441296883717975433924267 9661945325576963150886401)
                ·
                  refine ⟨7246458994182722363164801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9661945325576963150886401 7246458994182722363164801)
                  ·
                    refine ⟨5434844245637041772373601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246458994182722363164801 5434844245637041772373601)
                    ·
                      refine ⟨4076133184227781329280201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434844245637041772373601 4076133184227781329280201)
                      ·
                        rfl

theorem cell23_7938241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7938241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938241 prefixEnd_7938241 := by exact prefixLift 7938241
  have htrace : WordTrace (prefixWord ++ tailWord_7938241) baseStart_7938241 baseEnd_7938241 := by
    simpa [prefixWord, tailWord_7938241, baseEnd_7938241] using wordTrace_append hprefix tailTrace_7938241
  have hstable : (prefixWord ++ tailWord_7938241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938241).length < 2 ^ (prefixWord ++ tailWord_7938241).sum := by decide
  have hdescent : baseEnd_7938241 < baseStart_7938241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938266 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_7938266 : Nat := 118140960795 + 7938266 * 2 ^ 59
def prefixEnd_7938266 : Nat := 4983230072969 + 3 ^ 40 * 7938266 * 2
def baseEnd_7938266 : Nat := 4076146021244143731467585

theorem tailTrace_7938266 : CollatzResearch.WordTrace tailWord_7938266 prefixEnd_7938266 4076146021244143731467585 := by
  unfold tailWord_7938266
  simp only [CollatzResearch.WordTrace]
  refine ⟨72383086764756376185326663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193021564706017003160871101 72383086764756376185326663)
  ·
    refine ⟨108574630147134564277989995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72383086764756376185326663 108574630147134564277989995)
    ·
      refine ⟨162861945220701846416984993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108574630147134564277989995 162861945220701846416984993)
      ·
        refine ⟨122146458915526384812738745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162861945220701846416984993 122146458915526384812738745)
        ·
          refine ⟨91609844186644788609554059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122146458915526384812738745 91609844186644788609554059)
          ·
            refine ⟨137414766279967182914331089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91609844186644788609554059 137414766279967182914331089)
            ·
              refine ⟨103061074709975387185748317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137414766279967182914331089 103061074709975387185748317)
              ·
                refine ⟨38647903016240770194655619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103061074709975387185748317 38647903016240770194655619)
                ·
                  refine ⟨57971854524361155291983429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38647903016240770194655619 57971854524361155291983429)
                  ·
                    refine ⟨10869722723317716617246893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57971854524361155291983429 10869722723317716617246893)
                    ·
                      refine ⟨4076146021244143731467585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869722723317716617246893 4076146021244143731467585)
                      ·
                        rfl

theorem cell23_7938266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_7938266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938266 prefixEnd_7938266 := by exact prefixLift 7938266
  have htrace : WordTrace (prefixWord ++ tailWord_7938266) baseStart_7938266 baseEnd_7938266 := by
    simpa [prefixWord, tailWord_7938266, baseEnd_7938266] using wordTrace_append hprefix tailTrace_7938266
  have hstable : (prefixWord ++ tailWord_7938266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938266).length < 2 ^ (prefixWord ++ tailWord_7938266).sum := by decide
  have hdescent : baseEnd_7938266 < baseStart_7938266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938313 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 3]
def baseStart_7938313 : Nat := 118140960795 + 7938313 * 2 ^ 59
def prefixEnd_7938313 : Nat := 4983230072969 + 3 ^ 40 * 7938313 * 2
def baseEnd_7938313 : Nat := 4076170154834905047579869

theorem tailTrace_7938313 : CollatzResearch.WordTrace tailWord_7938313 prefixEnd_7938313 4076170154834905047579869 := by
  unfold tailWord_7938313
  simp only [CollatzResearch.WordTrace]
  refine ⟨289534061289855231768267593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193022707526570154512178395 289534061289855231768267593)
  ·
    refine ⟨217150545967391423826200695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289534061289855231768267593 217150545967391423826200695)
    ·
      refine ⟨325725818951087135739301043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217150545967391423826200695 325725818951087135739301043)
      ·
        refine ⟨488588728426630703608951565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325725818951087135739301043 488588728426630703608951565)
        ·
          refine ⟨183220773159986513853356837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488588728426630703608951565 183220773159986513853356837)
          ·
            refine ⟨34353894967497471347504407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183220773159986513853356837 34353894967497471347504407)
            ·
              refine ⟨51530842451246207021256611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34353894967497471347504407 51530842451246207021256611)
              ·
                refine ⟨77296263676869310531884917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51530842451246207021256611 77296263676869310531884917)
                ·
                  refine ⟨7246524719706497862364211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77296263676869310531884917 7246524719706497862364211)
                  ·
                    refine ⟨10869787079559746793546317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7246524719706497862364211 10869787079559746793546317)
                    ·
                      refine ⟨4076170154834905047579869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869787079559746793546317 4076170154834905047579869)
                      ·
                        rfl

theorem cell23_7938313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 3].length) (baseStart_7938313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938313 prefixEnd_7938313 := by exact prefixLift 7938313
  have htrace : WordTrace (prefixWord ++ tailWord_7938313) baseStart_7938313 baseEnd_7938313 := by
    simpa [prefixWord, tailWord_7938313, baseEnd_7938313] using wordTrace_append hprefix tailTrace_7938313
  have hstable : (prefixWord ++ tailWord_7938313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938313).length < 2 ^ (prefixWord ++ tailWord_7938313).sum := by decide
  have hdescent : baseEnd_7938313 < baseStart_7938313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938316 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_7938316 : Nat := 118140960795 + 7938316 * 2 ^ 59
def prefixEnd_7938316 : Nat := 4983230072969 + 3 ^ 40 * 7938316 * 2
def baseEnd_7938316 : Nat := 1358723898425622845280785

theorem tailTrace_7938316 : CollatzResearch.WordTrace tailWord_7938316 prefixEnd_7938316 1358723898425622845280785 := by
  unfold tailWord_7938316
  simp only [CollatzResearch.WordTrace]
  refine ⟨144767085354422181640313401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193022780472562908853751201 144767085354422181640313401)
  ·
    refine ⟨108575314015816636230235051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144767085354422181640313401 108575314015816636230235051)
    ·
      refine ⟨162862971023724954345352577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108575314015816636230235051 162862971023724954345352577)
      ·
        refine ⟨122147228267793715759014433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162862971023724954345352577 122147228267793715759014433)
        ·
          refine ⟨91610421200845286819260825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122147228267793715759014433 91610421200845286819260825)
          ·
            refine ⟨68707815900633965114445619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91610421200845286819260825 68707815900633965114445619)
            ·
              refine ⟨103061723850950947671668429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68707815900633965114445619 103061723850950947671668429)
              ·
                refine ⟨38648146444106605376875661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103061723850950947671668429 38648146444106605376875661)
                ·
                  refine ⟨14493054916539977016328373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38648146444106605376875661 14493054916539977016328373)
                  ·
                    refine ⟨1358723898425622845280785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14493054916539977016328373 1358723898425622845280785)
                    ·
                      rfl

theorem cell23_7938316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_7938316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938316 prefixEnd_7938316 := by exact prefixLift 7938316
  have htrace : WordTrace (prefixWord ++ tailWord_7938316) baseStart_7938316 baseEnd_7938316 := by
    simpa [prefixWord, tailWord_7938316, baseEnd_7938316] using wordTrace_append hprefix tailTrace_7938316
  have hstable : (prefixWord ++ tailWord_7938316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938316).length < 2 ^ (prefixWord ++ tailWord_7938316).sum := by decide
  have hdescent : baseEnd_7938316 < baseStart_7938316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938387 : List Nat := [1, 1, 1, 2, 1, 1, 4, 7, 1, 2, 2]
def baseStart_7938387 : Nat := 118140960795 + 7938387 * 2 ^ 59
def prefixEnd_7938387 : Nat := 4983230072969 + 3 ^ 40 * 7938387 * 2
def baseEnd_7938387 : Nat := 4076208152403337758054529

theorem tailTrace_7938387 : CollatzResearch.WordTrace tailWord_7938387 prefixEnd_7938387 4076208152403337758054529 := by
  unfold tailWord_7938387
  simp only [CollatzResearch.WordTrace]
  refine ⟨289536760291587142406461415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193024506861058094937640943 289536760291587142406461415)
  ·
    refine ⟨434305140437380713609692123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289536760291587142406461415 434305140437380713609692123)
    ·
      refine ⟨651457710656071070414538185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434305140437380713609692123 651457710656071070414538185)
      ·
        refine ⟨488593282992053302810903639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651457710656071070414538185 488593282992053302810903639)
        ·
          refine ⟨732889924488079954216355459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488593282992053302810903639 732889924488079954216355459)
          ·
            refine ⟨1099334886732119931324533189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732889924488079954216355459 1099334886732119931324533189)
            ·
              refine ⟨206125291262272487123349973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1099334886732119931324533189 206125291262272487123349973)
              ·
                refine ⟨4831061513959511416953515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206125291262272487123349973 4831061513959511416953515)
                ·
                  refine ⟨7246592270939267125430273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831061513959511416953515 7246592270939267125430273)
                  ·
                    refine ⟨5434944203204450344072705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246592270939267125430273 5434944203204450344072705)
                    ·
                      refine ⟨4076208152403337758054529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5434944203204450344072705 4076208152403337758054529)
                      ·
                        rfl

theorem cell23_7938387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 2, 2].length) (baseStart_7938387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938387 prefixEnd_7938387 := by exact prefixLift 7938387
  have htrace : WordTrace (prefixWord ++ tailWord_7938387) baseStart_7938387 baseEnd_7938387 := by
    simpa [prefixWord, tailWord_7938387, baseEnd_7938387] using wordTrace_append hprefix tailTrace_7938387
  have hstable : (prefixWord ++ tailWord_7938387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938387).length < 2 ^ (prefixWord ++ tailWord_7938387).sum := by decide
  have hdescent : baseEnd_7938387 < baseStart_7938387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938463 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 3]
def baseStart_7938463 : Nat := 118140960795 + 7938463 * 2 ^ 59
def prefixEnd_7938463 : Nat := 4983230072969 + 3 ^ 40 * 7938463 * 2
def baseEnd_7938463 : Nat := 4076247176933079460704179

theorem tailTrace_7938463 : CollatzResearch.WordTrace tailWord_7938463 prefixEnd_7938463 4076247176933079460704179 := by
  unfold tailWord_7938463
  simp only [CollatzResearch.WordTrace]
  refine ⟨289539532239311807386228043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193026354826207871590818695 289539532239311807386228043)
  ·
    refine ⟨434309298358967711079342065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289539532239311807386228043 434309298358967711079342065)
    ·
      refine ⟨325731973769225783309506549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434309298358967711079342065 325731973769225783309506549)
      ·
        refine ⟨30537372540864917185266239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325731973769225783309506549 30537372540864917185266239)
        ·
          refine ⟨45806058811297375777899359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30537372540864917185266239 45806058811297375777899359)
          ·
            refine ⟨68709088216946063666849039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45806058811297375777899359 68709088216946063666849039)
            ·
              refine ⟨103063632325419095500273559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68709088216946063666849039 103063632325419095500273559)
              ·
                refine ⟨154595448488128643250410339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103063632325419095500273559 154595448488128643250410339)
                ·
                  refine ⟨231893172732192964875615509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154595448488128643250410339 231893172732192964875615509)
                  ·
                    refine ⟨10869992471821545228544477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231893172732192964875615509 10869992471821545228544477)
                    ·
                      refine ⟨4076247176933079460704179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10869992471821545228544477 4076247176933079460704179)
                      ·
                        rfl

theorem cell23_7938463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_7938463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938463 prefixEnd_7938463 := by exact prefixLift 7938463
  have htrace : WordTrace (prefixWord ++ tailWord_7938463) baseStart_7938463 baseEnd_7938463 := by
    simpa [prefixWord, tailWord_7938463, baseEnd_7938463] using wordTrace_append hprefix tailTrace_7938463
  have hstable : (prefixWord ++ tailWord_7938463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938463).length < 2 ^ (prefixWord ++ tailWord_7938463).sum := by decide
  have hdescent : baseEnd_7938463 < baseStart_7938463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938513 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 2, 5]
def baseStart_7938513 : Nat := 118140960795 + 7938513 * 2 ^ 59
def prefixEnd_7938513 : Nat := 4983230072969 + 3 ^ 40 * 7938513 * 2
def baseEnd_7938513 : Nat := 1358757616988601421692983

theorem tailTrace_7938513 : CollatzResearch.WordTrace tailWord_7938513 prefixEnd_7938513 1358757616988601421692983 := by
  unfold tailWord_7938513
  simp only [CollatzResearch.WordTrace]
  refine ⟨289541355889130665925548193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193027570592753777283698795 289541355889130665925548193)
  ·
    refine ⟨217156016916847999444161145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289541355889130665925548193 217156016916847999444161145)
    ·
      refine ⟨162867012687635999583120859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217156016916847999444161145 162867012687635999583120859)
      ·
        refine ⟨244300519031453999374681289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162867012687635999583120859 244300519031453999374681289)
        ·
          refine ⟨183225389273590499531010967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244300519031453999374681289 183225389273590499531010967)
          ·
            refine ⟨274838083910385749296516451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183225389273590499531010967 274838083910385749296516451)
            ·
              refine ⟨412257125865578623944774677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274838083910385749296516451 412257125865578623944774677)
              ·
                refine ⟨19324552774948997997411313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 412257125865578623944774677 19324552774948997997411313)
                ·
                  refine ⟨14493414581211748498058485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19324552774948997997411313 14493414581211748498058485)
                  ·
                    refine ⟨1358757616988601421692983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14493414581211748498058485 1358757616988601421692983)
                    ·
                      rfl

theorem cell23_7938513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_7938513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938513 prefixEnd_7938513 := by exact prefixLift 7938513
  have htrace : WordTrace (prefixWord ++ tailWord_7938513) baseStart_7938513 baseEnd_7938513 := by
    simpa [prefixWord, tailWord_7938513, baseEnd_7938513] using wordTrace_append hprefix tailTrace_7938513
  have hstable : (prefixWord ++ tailWord_7938513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938513).length < 2 ^ (prefixWord ++ tailWord_7938513).sum := by decide
  have hdescent : baseEnd_7938513 < baseStart_7938513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938550 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_7938550 : Nat := 118140960795 + 7938550 * 2 ^ 59
def prefixEnd_7938550 : Nat := 4983230072969 + 3 ^ 40 * 7938550 * 2
def baseEnd_7938550 : Nat := 4076291849750020620316279

theorem tailTrace_7938550 : CollatzResearch.WordTrace tailWord_7938550 prefixEnd_7938550 4076291849750020620316279 := by
  unfold tailWord_7938550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096419086874788827790319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193028470259997747496430069 18096419086874788827790319)
  ·
    refine ⟨27144628630312183241685479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18096419086874788827790319 27144628630312183241685479)
    ·
      refine ⟨40716942945468274862528219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27144628630312183241685479 40716942945468274862528219)
      ·
        refine ⟨61075414418202412293792329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40716942945468274862528219 61075414418202412293792329)
        ·
          refine ⟨45806560813651809220344247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61075414418202412293792329 45806560813651809220344247)
          ·
            refine ⟨68709841220477713830516371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45806560813651809220344247 68709841220477713830516371)
            ·
              refine ⟨103064761830716570745774557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68709841220477713830516371 103064761830716570745774557)
              ·
                refine ⟨38649285686518714029665459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103064761830716570745774557 38649285686518714029665459)
                ·
                  refine ⟨57973928529778071044498189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38649285686518714029665459 57973928529778071044498189)
                  ·
                    refine ⟨21740223198666776641686821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57973928529778071044498189 21740223198666776641686821)
                    ·
                      refine ⟨4076291849750020620316279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21740223198666776641686821 4076291849750020620316279)
                      ·
                        rfl

theorem cell23_7938550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_7938550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938550 prefixEnd_7938550 := by exact prefixLift 7938550
  have htrace : WordTrace (prefixWord ++ tailWord_7938550) baseStart_7938550 baseEnd_7938550 := by
    simpa [prefixWord, tailWord_7938550, baseEnd_7938550] using wordTrace_append hprefix tailTrace_7938550
  have hstable : (prefixWord ++ tailWord_7938550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938550).length < 2 ^ (prefixWord ++ tailWord_7938550).sum := by decide
  have hdescent : baseEnd_7938550 < baseStart_7938550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938567 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_7938567 : Nat := 118140960795 + 7938567 * 2 ^ 59
def prefixEnd_7938567 : Nat := 4983230072969 + 3 ^ 40 * 7938567 * 2
def baseEnd_7938567 : Nat := 4076300578921147053803701

theorem tailTrace_7938567 : CollatzResearch.WordTrace tailWord_7938567 prefixEnd_7938567 4076300578921147053803701 := by
  unfold tailWord_7938567
  simp only [CollatzResearch.WordTrace]
  refine ⟨289543325430935033148013955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193028883620623355432009303 289543325430935033148013955)
  ·
    refine ⟨434314988146402549722020933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289543325430935033148013955 434314988146402549722020933)
    ·
      refine ⟨81434060277450478072878925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434314988146402549722020933 81434060277450478072878925)
      ·
        refine ⟨30537772604043929277329597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81434060277450478072878925 30537772604043929277329597)
        ·
          refine ⟨11451664726516473478998599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30537772604043929277329597 11451664726516473478998599)
          ·
            refine ⟨17177497089774710218497899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11451664726516473478998599 17177497089774710218497899)
            ·
              refine ⟨25766245634662065327746849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17177497089774710218497899 25766245634662065327746849)
              ·
                refine ⟨19324684225996548995810137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25766245634662065327746849 19324684225996548995810137)
                ·
                  refine ⟨14493513169497411746857603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19324684225996548995810137 14493513169497411746857603)
                  ·
                    refine ⟨21740269754246117620286405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14493513169497411746857603 21740269754246117620286405)
                    ·
                      refine ⟨4076300578921147053803701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21740269754246117620286405 4076300578921147053803701)
                      ·
                        rfl

theorem cell23_7938567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_7938567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938567 prefixEnd_7938567 := by exact prefixLift 7938567
  have htrace : WordTrace (prefixWord ++ tailWord_7938567) baseStart_7938567 baseEnd_7938567 := by
    simpa [prefixWord, tailWord_7938567, baseEnd_7938567] using wordTrace_append hprefix tailTrace_7938567
  have hstable : (prefixWord ++ tailWord_7938567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938567).length < 2 ^ (prefixWord ++ tailWord_7938567).sum := by decide
  have hdescent : baseEnd_7938567 < baseStart_7938567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938637 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7938637 : Nat := 118140960795 + 7938637 * 2 ^ 59
def prefixEnd_7938637 : Nat := 4983230072969 + 3 ^ 40 * 7938637 * 2
def baseEnd_7938637 : Nat := 1358778840855653926642793

theorem tailTrace_7938637 : CollatzResearch.WordTrace tailWord_7938637 prefixEnd_7938637 1358778840855653926642793 := by
  unfold tailWord_7938637
  simp only [CollatzResearch.WordTrace]
  refine ⟨289545878540681435103062165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193030585693787623402041443 289545878540681435103062165)
  ·
    refine ⟨13572463056594442270456039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289545878540681435103062165 13572463056594442270456039)
    ·
      refine ⟨20358694584891663405684059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13572463056594442270456039 20358694584891663405684059)
      ·
        refine ⟨30538041877337495108526089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20358694584891663405684059 30538041877337495108526089)
        ·
          refine ⟨22903531408003121331394567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30538041877337495108526089 22903531408003121331394567)
          ·
            refine ⟨34355297112004681997091851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22903531408003121331394567 34355297112004681997091851)
            ·
              refine ⟨51532945668007022995637777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34355297112004681997091851 51532945668007022995637777)
              ·
                refine ⟨38649709251005267246728333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51532945668007022995637777 38649709251005267246728333)
                ·
                  refine ⟨14493640969126975217523125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38649709251005267246728333 14493640969126975217523125)
                  ·
                    refine ⟨1358778840855653926642793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14493640969126975217523125 1358778840855653926642793)
                    ·
                      rfl

theorem cell23_7938637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7938637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938637 prefixEnd_7938637 := by exact prefixLift 7938637
  have htrace : WordTrace (prefixWord ++ tailWord_7938637) baseStart_7938637 baseEnd_7938637 := by
    simpa [prefixWord, tailWord_7938637, baseEnd_7938637] using wordTrace_append hprefix tailTrace_7938637
  have hstable : (prefixWord ++ tailWord_7938637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938637).length < 2 ^ (prefixWord ++ tailWord_7938637).sum := by decide
  have hdescent : baseEnd_7938637 < baseStart_7938637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938650 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_7938650 : Nat := 118140960795 + 7938650 * 2 ^ 59
def prefixEnd_7938650 : Nat := 4983230072969 + 3 ^ 40 * 7938650 * 2
def baseEnd_7938650 : Nat := 1358781065938490076355273

theorem tailTrace_7938650 : CollatzResearch.WordTrace tailWord_7938650 prefixEnd_7938650 1358781065938490076355273 := by
  unfold tailWord_7938650
  simp only [CollatzResearch.WordTrace]
  refine ⟨72386588172408584580821351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193030901793089558882190269 72386588172408584580821351)
  ·
    refine ⟨108579882258612876871232027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72386588172408584580821351 108579882258612876871232027)
    ·
      refine ⟨162869823387919315306848041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108579882258612876871232027 162869823387919315306848041)
      ·
        refine ⟨122152367540939486480136031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162869823387919315306848041 122152367540939486480136031)
        ·
          refine ⟨183228551311409229720204047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122152367540939486480136031 183228551311409229720204047)
          ·
            refine ⟨274842826967113844580306071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183228551311409229720204047 274842826967113844580306071)
            ·
              refine ⟨412264240450670766870459107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274842826967113844580306071 412264240450670766870459107)
              ·
                refine ⟨618396360676006150305688661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412264240450670766870459107 618396360676006150305688661)
                ·
                  refine ⟨7246832351671947073894789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 618396360676006150305688661 7246832351671947073894789)
                  ·
                    refine ⟨1358781065938490076355273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7246832351671947073894789 1358781065938490076355273)
                    ·
                      rfl

theorem cell23_7938650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_7938650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938650 prefixEnd_7938650 := by exact prefixLift 7938650
  have htrace : WordTrace (prefixWord ++ tailWord_7938650) baseStart_7938650 baseEnd_7938650 := by
    simpa [prefixWord, tailWord_7938650, baseEnd_7938650] using wordTrace_append hprefix tailTrace_7938650
  have hstable : (prefixWord ++ tailWord_7938650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938650).length < 2 ^ (prefixWord ++ tailWord_7938650).sum := by decide
  have hdescent : baseEnd_7938650 < baseStart_7938650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938661 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 2, 3, 2]
def baseStart_7938661 : Nat := 118140960795 + 7938661 * 2 ^ 59
def prefixEnd_7938661 : Nat := 4983230072969 + 3 ^ 40 * 7938661 * 2
def baseEnd_7938661 : Nat := 4076348846102669686028269

theorem tailTrace_7938661 : CollatzResearch.WordTrace tailWord_7938661 prefixEnd_7938661 4076348846102669686028269 := by
  unfold tailWord_7938661
  simp only [CollatzResearch.WordTrace]
  refine ⟨289546753892594487201935837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193031169261729658134623891 289546753892594487201935837)
  ·
    refine ⟨108580032709722932700725939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289546753892594487201935837 108580032709722932700725939)
    ·
      refine ⟨162870049064584399051088909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108580032709722932700725939 162870049064584399051088909)
      ·
        refine ⟨61076268399219149644158341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162870049064584399051088909 61076268399219149644158341)
        ·
          refine ⟨11451800324853590558279689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61076268399219149644158341 11451800324853590558279689)
          ·
            refine ⟨8588850243640192918709767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11451800324853590558279689 8588850243640192918709767)
            ·
              refine ⟨12883275365460289378064651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588850243640192918709767 12883275365460289378064651)
              ·
                refine ⟨19324913048190434067096977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12883275365460289378064651 19324913048190434067096977)
                ·
                  refine ⟨14493684786142825550322733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19324913048190434067096977 14493684786142825550322733)
                  ·
                    refine ⟨5435131794803559581371025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14493684786142825550322733 5435131794803559581371025)
                    ·
                      refine ⟨4076348846102669686028269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435131794803559581371025 4076348846102669686028269)
                      ·
                        rfl

theorem cell23_7938661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_7938661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938661 prefixEnd_7938661 := by exact prefixLift 7938661
  have htrace : WordTrace (prefixWord ++ tailWord_7938661) baseStart_7938661 baseEnd_7938661 := by
    simpa [prefixWord, tailWord_7938661, baseEnd_7938661] using wordTrace_append hprefix tailTrace_7938661
  have hstable : (prefixWord ++ tailWord_7938661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938661).length < 2 ^ (prefixWord ++ tailWord_7938661).sum := by decide
  have hdescent : baseEnd_7938661 < baseStart_7938661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938674 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_7938674 : Nat := 118140960795 + 7938674 * 2 ^ 59
def prefixEnd_7938674 : Nat := 4983230072969 + 3 ^ 40 * 7938674 * 2
def baseEnd_7938674 : Nat := 4076355521351178135165709

theorem tailTrace_7938674 : CollatzResearch.WordTrace tailWord_7938674 prefixEnd_7938674 4076355521351178135165709 := by
  unfold tailWord_7938674
  simp only [CollatzResearch.WordTrace]
  refine ⟨72386807010386847605539769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193031485361031593614772717 72386807010386847605539769)
  ·
    refine ⟨54290105257790135704154827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72386807010386847605539769 54290105257790135704154827)
    ·
      refine ⟨81435157886685203556232241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54290105257790135704154827 81435157886685203556232241)
      ·
        refine ⟨61076368415013902667174181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81435157886685203556232241 61076368415013902667174181)
        ·
          refine ⟨11451819077815106750095159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61076368415013902667174181 11451819077815106750095159)
          ·
            refine ⟨17177728616722660125142739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11451819077815106750095159 17177728616722660125142739)
            ·
              refine ⟨25766592925083990187714109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17177728616722660125142739 25766592925083990187714109)
              ·
                refine ⟨9662472346906496320392791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25766592925083990187714109 9662472346906496320392791)
                ·
                  refine ⟨14493708520359744480589187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9662472346906496320392791 14493708520359744480589187)
                  ·
                    refine ⟨21740562780539616720883781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14493708520359744480589187 21740562780539616720883781)
                    ·
                      refine ⟨4076355521351178135165709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21740562780539616720883781 4076355521351178135165709)
                      ·
                        rfl

theorem cell23_7938674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_7938674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938674 prefixEnd_7938674 := by exact prefixLift 7938674
  have htrace : WordTrace (prefixWord ++ tailWord_7938674) baseStart_7938674 baseEnd_7938674 := by
    simpa [prefixWord, tailWord_7938674, baseEnd_7938674] using wordTrace_append hprefix tailTrace_7938674
  have hstable : (prefixWord ++ tailWord_7938674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938674).length < 2 ^ (prefixWord ++ tailWord_7938674).sum := by decide
  have hdescent : baseEnd_7938674 < baseStart_7938674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938691 : List Nat := [1, 1, 1, 3, 3, 1, 4, 4, 1, 2, 2]
def baseStart_7938691 : Nat := 118140960795 + 7938691 * 2 ^ 59
def prefixEnd_7938691 : Nat := 4983230072969 + 3 ^ 40 * 7938691 * 2
def baseEnd_7938691 : Nat := 4076364250522304568653131

theorem tailTrace_7938691 : CollatzResearch.WordTrace tailWord_7938691 prefixEnd_7938691 4076364250522304568653131 := by
  unfold tailWord_7938691
  simp only [CollatzResearch.WordTrace]
  refine ⟨289547848082485802325527927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193031898721657201550351951 289547848082485802325527927)
  ·
    refine ⟨434321772123728703488291891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289547848082485802325527927 434321772123728703488291891)
    ·
      refine ⟨651482658185593055232437837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434321772123728703488291891 651482658185593055232437837)
      ·
        refine ⟨244305996819597395712164189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651482658185593055232437837 244305996819597395712164189)
        ·
          refine ⟨91614748807349023392061571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244305996819597395712164189 91614748807349023392061571)
          ·
            refine ⟨137422123211023535088092357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91614748807349023392061571 137422123211023535088092357)
            ·
              refine ⟨25766648102066912829017317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137422123211023535088092357 25766648102066912829017317)
              ·
                refine ⟨4831246519137546155440747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25766648102066912829017317 4831246519137546155440747)
                ·
                  refine ⟨7246869778706319233161121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831246519137546155440747 7246869778706319233161121)
                  ·
                    refine ⟨5435152334029739424870841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246869778706319233161121 5435152334029739424870841)
                    ·
                      refine ⟨4076364250522304568653131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435152334029739424870841 4076364250522304568653131)
                      ·
                        rfl

theorem cell23_7938691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_7938691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938691 prefixEnd_7938691 := by exact prefixLift 7938691
  have htrace : WordTrace (prefixWord ++ tailWord_7938691) baseStart_7938691 baseEnd_7938691 := by
    simpa [prefixWord, tailWord_7938691, baseEnd_7938691] using wordTrace_append hprefix tailTrace_7938691
  have hstable : (prefixWord ++ tailWord_7938691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938691).length < 2 ^ (prefixWord ++ tailWord_7938691).sum := by decide
  have hdescent : baseEnd_7938691 < baseStart_7938691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938742 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7938742 : Nat := 118140960795 + 7938742 * 2 ^ 59
def prefixEnd_7938742 : Nat := 4983230072969 + 3 ^ 40 * 7938742 * 2
def baseEnd_7938742 : Nat := 4076390438035683869115397

theorem tailTrace_7938742 : CollatzResearch.WordTrace tailWord_7938742 prefixEnd_7938742 4076390438035683869115397 := by
  unfold tailWord_7938742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096856762831314877227155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193033138803534025357089653 18096856762831314877227155)
  ·
    refine ⟨27145285144246972315840733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18096856762831314877227155 27145285144246972315840733)
    ·
      refine ⟨10179481929092614618440275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27145285144246972315840733 10179481929092614618440275)
      ·
        refine ⟨15269222893638921927660413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179481929092614618440275 15269222893638921927660413)
        ·
          refine ⟨5725958585114595722872655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15269222893638921927660413 5725958585114595722872655)
          ·
            refine ⟨8588937877671893584308983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5725958585114595722872655 8588937877671893584308983)
            ·
              refine ⟨12883406816507840376463475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588937877671893584308983 12883406816507840376463475)
              ·
                refine ⟨19325110224761760564695213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12883406816507840376463475 19325110224761760564695213)
                ·
                  refine ⟨7246916334285660211760705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19325110224761760564695213 7246916334285660211760705)
                  ·
                    refine ⟨5435187250714245158820529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246916334285660211760705 5435187250714245158820529)
                    ·
                      refine ⟨4076390438035683869115397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435187250714245158820529 4076390438035683869115397)
                      ·
                        rfl

theorem cell23_7938742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7938742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938742 prefixEnd_7938742 := by exact prefixLift 7938742
  have htrace : WordTrace (prefixWord ++ tailWord_7938742) baseStart_7938742 baseEnd_7938742 := by
    simpa [prefixWord, tailWord_7938742, baseEnd_7938742] using wordTrace_append hprefix tailTrace_7938742
  have hstable : (prefixWord ++ tailWord_7938742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938742).length < 2 ^ (prefixWord ++ tailWord_7938742).sum := by decide
  have hdescent : baseEnd_7938742 < baseStart_7938742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938798 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_7938798 : Nat := 118140960795 + 7938798 * 2 ^ 59
def prefixEnd_7938798 : Nat := 4983230072969 + 3 ^ 40 * 7938798 * 2
def baseEnd_7938798 : Nat := 4076419192952335650015139

theorem tailTrace_7938798 : CollatzResearch.WordTrace tailWord_7938798 prefixEnd_7938798 4076419192952335650015139 := by
  unfold tailWord_7938798
  simp only [CollatzResearch.WordTrace]
  refine ⟨36193968836637269949959131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193034500462065439733115365 36193968836637269949959131)
  ·
    refine ⟨54290953254955904924938697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36193968836637269949959131 54290953254955904924938697)
    ·
      refine ⟨40718214941216928693704023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54290953254955904924938697 40718214941216928693704023)
      ·
        refine ⟨61077322411825393040556035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40718214941216928693704023 61077322411825393040556035)
        ·
          refine ⟨91615983617738089560834053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61077322411825393040556035 91615983617738089560834053)
          ·
            refine ⟨17177996928325891792656385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91615983617738089560834053 17177996928325891792656385)
            ·
              refine ⟨12883497696244418844492289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17177996928325891792656385 12883497696244418844492289)
              ·
                refine ⟨9662623272183314133369217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12883497696244418844492289 9662623272183314133369217)
                ·
                  refine ⟨7246967454137485600026913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9662623272183314133369217 7246967454137485600026913)
                  ·
                    refine ⟨5435225590603114200020185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246967454137485600026913 5435225590603114200020185)
                    ·
                      refine ⟨4076419192952335650015139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435225590603114200020185 4076419192952335650015139)
                      ·
                        rfl

theorem cell23_7938798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_7938798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938798 prefixEnd_7938798 := by exact prefixLift 7938798
  have htrace : WordTrace (prefixWord ++ tailWord_7938798) baseStart_7938798 baseEnd_7938798 := by
    simpa [prefixWord, tailWord_7938798, baseEnd_7938798] using wordTrace_append hprefix tailTrace_7938798
  have hstable : (prefixWord ++ tailWord_7938798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938798).length < 2 ^ (prefixWord ++ tailWord_7938798).sum := by decide
  have hdescent : baseEnd_7938798 < baseStart_7938798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938814 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7938814 : Nat := 118140960795 + 7938814 * 2 ^ 59
def prefixEnd_7938814 : Nat := 4983230072969 + 3 ^ 40 * 7938814 * 2
def baseEnd_7938814 : Nat := 4076427408642807587415065

theorem tailTrace_7938814 : CollatzResearch.WordTrace tailWord_7938814 prefixEnd_7938814 4076427408642807587415065 := by
  unfold tailWord_7938814
  simp only [CollatzResearch.WordTrace]
  refine ⟨36194041782630024291531937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193034889507360129554836997 36194041782630024291531937)
  ·
    refine ⟨27145531336972518218648953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36194041782630024291531937 27145531336972518218648953)
    ·
      refine ⟨20359148502729388663986715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27145531336972518218648953 20359148502729388663986715)
      ·
        refine ⟨30538722754094082995980073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20359148502729388663986715 30538722754094082995980073)
        ·
          refine ⟨22904042065570562246985055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30538722754094082995980073 22904042065570562246985055)
          ·
            refine ⟨34356063098355843370477583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22904042065570562246985055 34356063098355843370477583)
            ·
              refine ⟨51534094647533765055716375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34356063098355843370477583 51534094647533765055716375)
              ·
                refine ⟨77301141971300647583574563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51534094647533765055716375 77301141971300647583574563)
                ·
                  refine ⟨115951712956950971375361845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77301141971300647583574563 115951712956950971375361845)
                  ·
                    refine ⟨10870473089714153566440173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115951712956950971375361845 10870473089714153566440173)
                    ·
                      refine ⟨4076427408642807587415065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10870473089714153566440173 4076427408642807587415065)
                      ·
                        rfl

theorem cell23_7938814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7938814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938814 prefixEnd_7938814 := by exact prefixLift 7938814
  have htrace : WordTrace (prefixWord ++ tailWord_7938814) baseStart_7938814 baseEnd_7938814 := by
    simpa [prefixWord, tailWord_7938814, baseEnd_7938814] using wordTrace_append hprefix tailTrace_7938814
  have hstable : (prefixWord ++ tailWord_7938814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938814).length < 2 ^ (prefixWord ++ tailWord_7938814).sum := by decide
  have hdescent : baseEnd_7938814 < baseStart_7938814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938837 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7938837 : Nat := 118140960795 + 7938837 * 2 ^ 59
def prefixEnd_7938837 : Nat := 4983230072969 + 3 ^ 40 * 7938837 * 2
def baseEnd_7938837 : Nat := 4076439218697860997427459

theorem tailTrace_7938837 : CollatzResearch.WordTrace tailWord_7938837 prefixEnd_7938837 4076439218697860997427459 := by
  unfold tailWord_7938837
  simp only [CollatzResearch.WordTrace]
  refine ⟨289553173139956869260342765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193035448759971246173561843 289553173139956869260342765)
  ·
    refine ⟨108582439927483825972628537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289553173139956869260342765 108582439927483825972628537)
    ·
      refine ⟨81436829945612869479471403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108582439927483825972628537 81436829945612869479471403)
      ·
        refine ⟨122155244918419304219207105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81436829945612869479471403 122155244918419304219207105)
        ·
          refine ⟨91616433688814478164405329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122155244918419304219207105 91616433688814478164405329)
          ·
            refine ⟨68712325266610858623303997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91616433688814478164405329 68712325266610858623303997)
            ·
              refine ⟨25767121974979071983738999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68712325266610858623303997 25767121974979071983738999)
              ·
                refine ⟨38650682962468607975608499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25767121974979071983738999 38650682962468607975608499)
                ·
                  refine ⟨57976024443702911963412749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38650682962468607975608499 57976024443702911963412749)
                  ·
                    refine ⟨21741009166388591986279781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57976024443702911963412749 21741009166388591986279781)
                    ·
                      refine ⟨4076439218697860997427459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21741009166388591986279781 4076439218697860997427459)
                      ·
                        rfl

theorem cell23_7938837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7938837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938837 prefixEnd_7938837 := by exact prefixLift 7938837
  have htrace : WordTrace (prefixWord ++ tailWord_7938837) baseStart_7938837 baseEnd_7938837 := by
    simpa [prefixWord, tailWord_7938837, baseEnd_7938837] using wordTrace_append hprefix tailTrace_7938837
  have hstable : (prefixWord ++ tailWord_7938837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938837).length < 2 ^ (prefixWord ++ tailWord_7938837).sum := by decide
  have hdescent : baseEnd_7938837 < baseStart_7938837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938887 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_7938887 : Nat := 118140960795 + 7938887 * 2 ^ 59
def prefixEnd_7938887 : Nat := 4983230072969 + 3 ^ 40 * 7938887 * 2
def baseEnd_7938887 : Nat := 4076464892730585801802229

theorem tailTrace_7938887 : CollatzResearch.WordTrace tailWord_7938887 prefixEnd_7938887 4076464892730585801802229 := by
  unfold tailWord_7938887
  simp only [CollatzResearch.WordTrace]
  refine ⟨289554996789775727799662915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193036664526517151866441943 289554996789775727799662915)
  ·
    refine ⟨434332495184663591699494373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289554996789775727799662915 434332495184663591699494373)
    ·
      refine ⟨81437342847124423443655195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434332495184663591699494373 81437342847124423443655195)
      ·
        refine ⟨122156014270686635165482793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81437342847124423443655195 122156014270686635165482793)
        ·
          refine ⟨91617010703014976374112095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122156014270686635165482793 91617010703014976374112095)
          ·
            refine ⟨137425516054522464561168143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91617010703014976374112095 137425516054522464561168143)
            ·
              refine ⟨206138274081783696841752215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137425516054522464561168143 206138274081783696841752215)
              ·
                refine ⟨309207411122675545262628323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206138274081783696841752215 309207411122675545262628323)
                ·
                  refine ⟨463811116684013317893942485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309207411122675545262628323 463811116684013317893942485)
                  ·
                    refine ⟨10870573047281562138139277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 463811116684013317893942485 10870573047281562138139277)
                    ·
                      refine ⟨4076464892730585801802229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10870573047281562138139277 4076464892730585801802229)
                      ·
                        rfl

theorem cell23_7938887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_7938887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938887 prefixEnd_7938887 := by exact prefixLift 7938887
  have htrace : WordTrace (prefixWord ++ tailWord_7938887) baseStart_7938887 baseEnd_7938887 := by
    simpa [prefixWord, tailWord_7938887, baseEnd_7938887] using wordTrace_append hprefix tailTrace_7938887
  have hstable : (prefixWord ++ tailWord_7938887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938887).length < 2 ^ (prefixWord ++ tailWord_7938887).sum := by decide
  have hdescent : baseEnd_7938887 < baseStart_7938887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938904 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_7938904 : Nat := 118140960795 + 7938904 * 2 ^ 59
def prefixEnd_7938904 : Nat := 4983230072969 + 3 ^ 40 * 7938904 * 2
def baseEnd_7938904 : Nat := 4076473621901712235289651

theorem tailTrace_7938904 : CollatzResearch.WordTrace tailWord_7938904 prefixEnd_7938904 4076473621901712235289651 := by
  unfold tailWord_7938904
  simp only [CollatzResearch.WordTrace]
  refine ⟨144777808415357069851515883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193037077887142759802021177 144777808415357069851515883)
  ·
    refine ⟨217166712623035604777273825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144777808415357069851515883 217166712623035604777273825)
    ·
      refine ⟨162875034467276703582955369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217166712623035604777273825 162875034467276703582955369)
      ·
        refine ⟨122156275850457527687216527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162875034467276703582955369 122156275850457527687216527)
        ·
          refine ⟨183234413775686291530824791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122156275850457527687216527 183234413775686291530824791)
          ·
            refine ⟨274851620663529437296237187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183234413775686291530824791 274851620663529437296237187)
            ·
              refine ⟨412277430995294155944355781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274851620663529437296237187 412277430995294155944355781)
              ·
                refine ⟨77302018311617654239566709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412277430995294155944355781 77302018311617654239566709)
                ·
                  refine ⟨7247064216714155084959379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77302018311617654239566709 7247064216714155084959379)
                  ·
                    refine ⟨10870596325071232627439069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7247064216714155084959379 10870596325071232627439069)
                    ·
                      refine ⟨4076473621901712235289651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10870596325071232627439069 4076473621901712235289651)
                      ·
                        rfl

theorem cell23_7938904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_7938904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938904 prefixEnd_7938904 := by exact prefixLift 7938904
  have htrace : WordTrace (prefixWord ++ tailWord_7938904) baseStart_7938904 baseEnd_7938904 := by
    simpa [prefixWord, tailWord_7938904, baseEnd_7938904] using wordTrace_append hprefix tailTrace_7938904
  have hstable : (prefixWord ++ tailWord_7938904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938904).length < 2 ^ (prefixWord ++ tailWord_7938904).sum := by decide
  have hdescent : baseEnd_7938904 < baseStart_7938904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938944 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4]
def baseStart_7938944 : Nat := 118140960795 + 7938944 * 2 ^ 59
def prefixEnd_7938944 : Nat := 4983230072969 + 3 ^ 40 * 7938944 * 2
def baseEnd_7938944 : Nat := 4076494161127892078789467

theorem tailTrace_7938944 : CollatzResearch.WordTrace tailWord_7938944 prefixEnd_7938944 4076494161127892078789467 := by
  unfold tailWord_7938944
  simp only [CollatzResearch.WordTrace]
  refine ⟨144778537875284613267243943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193038050500379484356325257 144778537875284613267243943)
  ·
    refine ⟨217167806812926919900865915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144778537875284613267243943 217167806812926919900865915)
    ·
      refine ⟨325751710219390379851298873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217167806812926919900865915 325751710219390379851298873)
      ·
        refine ⟨244313782664542784888474155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325751710219390379851298873 244313782664542784888474155)
        ·
          refine ⟨366470673996814177332711233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244313782664542784888474155 366470673996814177332711233)
          ·
            refine ⟨274853005497610632999533425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366470673996814177332711233 274853005497610632999533425)
            ·
              refine ⟨206139754123207974749650069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274853005497610632999533425 206139754123207974749650069)
              ·
                refine ⟨9662800974525373816389847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206139754123207974749650069 9662800974525373816389847)
                ·
                  refine ⟨14494201461788060724584771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9662800974525373816389847 14494201461788060724584771)
                  ·
                    refine ⟨21741302192682091086877157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14494201461788060724584771 21741302192682091086877157)
                    ·
                      refine ⟨4076494161127892078789467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21741302192682091086877157 4076494161127892078789467)
                      ·
                        rfl

theorem cell23_7938944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_7938944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938944 prefixEnd_7938944 := by exact prefixLift 7938944
  have htrace : WordTrace (prefixWord ++ tailWord_7938944) baseStart_7938944 baseEnd_7938944 := by
    simpa [prefixWord, tailWord_7938944, baseEnd_7938944] using wordTrace_append hprefix tailTrace_7938944
  have hstable : (prefixWord ++ tailWord_7938944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938944).length < 2 ^ (prefixWord ++ tailWord_7938944).sum := by decide
  have hdescent : baseEnd_7938944 < baseStart_7938944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7938954 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_7938954 : Nat := 118140960795 + 7938954 * 2 ^ 59
def prefixEnd_7938954 : Nat := 4983230072969 + 3 ^ 40 * 7938954 * 2
def baseEnd_7938954 : Nat := 1358833098644812346554807

theorem tailTrace_7938954 : CollatzResearch.WordTrace tailWord_7938954 prefixEnd_7938954 1358833098644812346554807 := by
  unfold tailWord_7938954
  simp only [CollatzResearch.WordTrace]
  refine ⟨72389360120133249560587979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193038293653688665494901277 72389360120133249560587979)
  ·
    refine ⟨108584040180199874340881969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72389360120133249560587979 108584040180199874340881969)
    ·
      refine ⟨81438030135149905755661477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108584040180199874340881969 81438030135149905755661477)
      ·
        refine ⟨15269630650340607329186527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81438030135149905755661477 15269630650340607329186527)
        ·
          refine ⟨22904445975510910993779791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15269630650340607329186527 22904445975510910993779791)
          ·
            refine ⟨34356668963266366490669687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22904445975510910993779791 34356668963266366490669687)
            ·
              refine ⟨51535003444899549736004531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34356668963266366490669687 51535003444899549736004531)
              ·
                refine ⟨77302505167349324604006797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51535003444899549736004531 77302505167349324604006797)
                ·
                  refine ⟨28988439437755996726502549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77302505167349324604006797 28988439437755996726502549)
                  ·
                    refine ⟨1358833098644812346554807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28988439437755996726502549 1358833098644812346554807)
                    ·
                      rfl

theorem cell23_7938954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_7938954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7938954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7938954 prefixEnd_7938954 := by exact prefixLift 7938954
  have htrace : WordTrace (prefixWord ++ tailWord_7938954) baseStart_7938954 baseEnd_7938954 := by
    simpa [prefixWord, tailWord_7938954, baseEnd_7938954] using wordTrace_append hprefix tailTrace_7938954
  have hstable : (prefixWord ++ tailWord_7938954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7938954).length < 2 ^ (prefixWord ++ tailWord_7938954).sum := by decide
  have hdescent : baseEnd_7938954 < baseStart_7938954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7938954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939012 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7939012 : Nat := 118140960795 + 7939012 * 2 ^ 59
def prefixEnd_7939012 : Nat := 4983230072969 + 3 ^ 40 * 7939012 * 2
def baseEnd_7939012 : Nat := 4076529077812397812739155

theorem tailTrace_7939012 : CollatzResearch.WordTrace tailWord_7939012 prefixEnd_7939012 4076529077812397812739155 := by
  unfold tailWord_7939012
  simp only [CollatzResearch.WordTrace]
  refine ⟨144779777957161437073981645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193039703942881916098642193 144779777957161437073981645)
  ·
    refine ⟨54292416733935538902743117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144779777957161437073981645 54292416733935538902743117)
    ·
      refine ⟨20359656275225827088528669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54292416733935538902743117 20359656275225827088528669)
      ·
        refine ⟨7634871103209685158198251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20359656275225827088528669 7634871103209685158198251)
        ·
          refine ⟨11452306654814527737297377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634871103209685158198251 11452306654814527737297377)
          ·
            refine ⟨8589229991110895802973033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11452306654814527737297377 8589229991110895802973033)
            ·
              refine ⟨6441922493333171852229775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8589229991110895802973033 6441922493333171852229775)
              ·
                refine ⟨9662883739999757778344663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441922493333171852229775 9662883739999757778344663)
                ·
                  refine ⟨14494325609999636667516995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9662883739999757778344663 14494325609999636667516995)
                  ·
                    refine ⟨21741488414999455001275493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14494325609999636667516995 21741488414999455001275493)
                    ·
                      refine ⟨4076529077812397812739155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21741488414999455001275493 4076529077812397812739155)
                      ·
                        rfl

theorem cell23_7939012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7939012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939012 prefixEnd_7939012 := by exact prefixLift 7939012
  have htrace : WordTrace (prefixWord ++ tailWord_7939012) baseStart_7939012 baseEnd_7939012 := by
    simpa [prefixWord, tailWord_7939012, baseEnd_7939012] using wordTrace_append hprefix tailTrace_7939012
  have hstable : (prefixWord ++ tailWord_7939012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939012).length < 2 ^ (prefixWord ++ tailWord_7939012).sum := by decide
  have hdescent : baseEnd_7939012 < baseStart_7939012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939028 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_7939028 : Nat := 118140960795 + 7939028 * 2 ^ 59
def prefixEnd_7939028 : Nat := 4983230072969 + 3 ^ 40 * 7939028 * 2
def baseEnd_7939028 : Nat := 4076537293502869750139081

theorem tailTrace_7939028 : CollatzResearch.WordTrace tailWord_7939028 prefixEnd_7939028 4076537293502869750139081 := by
  unfold tailWord_7939028
  simp only [CollatzResearch.WordTrace]
  refine ⟨144780069741132454440272869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193040092988176605920363825 144780069741132454440272869)
  ·
    refine ⟨27146263076462335207551163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144780069741132454440272869 27146263076462335207551163)
    ·
      refine ⟨40719394614693502811326745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27146263076462335207551163 40719394614693502811326745)
      ·
        refine ⟨30539545961020127108495059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40719394614693502811326745 30539545961020127108495059)
        ·
          refine ⟨45809318941530190662742589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30539545961020127108495059 45809318941530190662742589)
          ·
            refine ⟨17178494603073821498528471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45809318941530190662742589 17178494603073821498528471)
            ·
              refine ⟨25767741904610732247792707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17178494603073821498528471 25767741904610732247792707)
              ·
                refine ⟨38651612856916098371689061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25767741904610732247792707 38651612856916098371689061)
                ·
                  refine ⟨7247177410671768444691699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38651612856916098371689061 7247177410671768444691699)
                  ·
                    refine ⟨10870766116007652667037549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7247177410671768444691699 10870766116007652667037549)
                    ·
                      refine ⟨4076537293502869750139081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10870766116007652667037549 4076537293502869750139081)
                      ·
                        rfl

theorem cell23_7939028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_7939028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939028 prefixEnd_7939028 := by exact prefixLift 7939028
  have htrace : WordTrace (prefixWord ++ tailWord_7939028) baseStart_7939028 baseEnd_7939028 := by
    simpa [prefixWord, tailWord_7939028, baseEnd_7939028] using wordTrace_append hprefix tailTrace_7939028
  have hstable : (prefixWord ++ tailWord_7939028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939028).length < 2 ^ (prefixWord ++ tailWord_7939028).sum := by decide
  have hdescent : baseEnd_7939028 < baseStart_7939028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939045 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7939045 : Nat := 118140960795 + 7939045 * 2 ^ 59
def prefixEnd_7939045 : Nat := 4983230072969 + 3 ^ 40 * 7939045 * 2
def baseEnd_7939045 : Nat := 4076546022673996183626503

theorem tailTrace_7939045 : CollatzResearch.WordTrace tailWord_7939045 prefixEnd_7939045 4076546022673996183626503 := by
  unfold tailWord_7939045
  simp only [CollatzResearch.WordTrace]
  refine ⟨289560759523203320783914589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193040506348802213855943059 289560759523203320783914589)
  ·
    refine ⟨108585284821201245293967971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289560759523203320783914589 108585284821201245293967971)
    ·
      refine ⟨162877927231801867940951957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108585284821201245293967971 162877927231801867940951957)
      ·
        refine ⟨7634902838990712559732123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162877927231801867940951957 7634902838990712559732123)
        ·
          refine ⟨11452354258486068839598185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634902838990712559732123 11452354258486068839598185)
          ·
            refine ⟨8589265693864551629698639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11452354258486068839598185 8589265693864551629698639)
            ·
              refine ⟨12883898540796827444547959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8589265693864551629698639 12883898540796827444547959)
              ·
                refine ⟨19325847811195241166821939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12883898540796827444547959 19325847811195241166821939)
                ·
                  refine ⟨28988771716792861750232909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19325847811195241166821939 28988771716792861750232909)
                  ·
                    refine ⟨10870789393797323156337341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28988771716792861750232909 10870789393797323156337341)
                    ·
                      refine ⟨4076546022673996183626503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10870789393797323156337341 4076546022673996183626503)
                      ·
                        rfl

theorem cell23_7939045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7939045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939045 prefixEnd_7939045 := by exact prefixLift 7939045
  have htrace : WordTrace (prefixWord ++ tailWord_7939045) baseStart_7939045 baseEnd_7939045 := by
    simpa [prefixWord, tailWord_7939045, baseEnd_7939045] using wordTrace_append hprefix tailTrace_7939045
  have hstable : (prefixWord ++ tailWord_7939045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939045).length < 2 ^ (prefixWord ++ tailWord_7939045).sum := by decide
  have hdescent : baseEnd_7939045 < baseStart_7939045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939068 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_7939068 : Nat := 118140960795 + 7939068 * 2 ^ 59
def prefixEnd_7939068 : Nat := 4983230072969 + 3 ^ 40 * 7939068 * 2
def baseEnd_7939068 : Nat := 4076557832729049593638897

theorem tailTrace_7939068 : CollatzResearch.WordTrace tailWord_7939068 prefixEnd_7939068 4076557832729049593638897 := by
  unfold tailWord_7939068
  simp only [CollatzResearch.WordTrace]
  refine ⟨144780799201059997856000929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193041065601413330474667905 144780799201059997856000929)
  ·
    refine ⟨108585599400794998392000697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144780799201059997856000929 108585599400794998392000697)
    ·
      refine ⟨81439199550596248794000523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108585599400794998392000697 81439199550596248794000523)
      ·
        refine ⟨122158799325894373191000785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81439199550596248794000523 122158799325894373191000785)
        ·
          refine ⟨91619099494420779893250589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122158799325894373191000785 91619099494420779893250589)
          ·
            refine ⟨34357162310407792459968971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91619099494420779893250589 34357162310407792459968971)
            ·
              refine ⟨51535743465611688689953457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34357162310407792459968971 51535743465611688689953457)
              ·
                refine ⟨38651807599208766517465093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51535743465611688689953457 38651807599208766517465093)
                ·
                  refine ⟨7247213924851643722024705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38651807599208766517465093 7247213924851643722024705)
                  ·
                    refine ⟨5435410443638732791518529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247213924851643722024705 5435410443638732791518529)
                    ·
                      refine ⟨4076557832729049593638897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435410443638732791518529 4076557832729049593638897)
                      ·
                        rfl

theorem cell23_7939068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_7939068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939068 prefixEnd_7939068 := by exact prefixLift 7939068
  have htrace : WordTrace (prefixWord ++ tailWord_7939068) baseStart_7939068 baseEnd_7939068 := by
    simpa [prefixWord, tailWord_7939068, baseEnd_7939068] using wordTrace_append hprefix tailTrace_7939068
  have hstable : (prefixWord ++ tailWord_7939068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939068).length < 2 ^ (prefixWord ++ tailWord_7939068).sum := by decide
  have hdescent : baseEnd_7939068 < baseStart_7939068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939121 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 2, 5]
def baseStart_7939121 : Nat := 118140960795 + 7939121 * 2 ^ 59
def prefixEnd_7939121 : Nat := 4983230072969 + 3 ^ 40 * 7939121 * 2
def baseEnd_7939121 : Nat := 1358861682401245962092051

theorem tailTrace_7939121 : CollatzResearch.WordTrace tailWord_7939121 prefixEnd_7939121 1358861682401245962092051 := by
  unfold tailWord_7939121
  simp only [CollatzResearch.WordTrace]
  refine ⟨289563531470927985763681217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193042354313951990509120811 289563531470927985763681217)
  ·
    refine ⟨217172648603195989322760913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289563531470927985763681217 217172648603195989322760913)
    ·
      refine ⟨162879486452396991992070685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217172648603195989322760913 162879486452396991992070685)
      ·
        refine ⟨61079807419648871997026507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162879486452396991992070685 61079807419648871997026507)
        ·
          refine ⟨91619711129473307995539761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61079807419648871997026507 91619711129473307995539761)
          ·
            refine ⟨68714783347104980996654821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91619711129473307995539761 68714783347104980996654821)
            ·
              refine ⟨12884021877582183936872779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68714783347104980996654821 12884021877582183936872779)
              ·
                refine ⟨19326032816373275905309169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12884021877582183936872779 19326032816373275905309169)
                ·
                  refine ⟨14494524612279956928981877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19326032816373275905309169 14494524612279956928981877)
                  ·
                    refine ⟨1358861682401245962092051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14494524612279956928981877 1358861682401245962092051)
                    ·
                      rfl

theorem cell23_7939121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_7939121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939121 prefixEnd_7939121 := by exact prefixLift 7939121
  have htrace : WordTrace (prefixWord ++ tailWord_7939121) baseStart_7939121 baseEnd_7939121 := by
    simpa [prefixWord, tailWord_7939121, baseEnd_7939121] using wordTrace_append hprefix tailTrace_7939121
  have hstable : (prefixWord ++ tailWord_7939121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939121).length < 2 ^ (prefixWord ++ tailWord_7939121).sum := by decide
  have hdescent : baseEnd_7939121 < baseStart_7939121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939141 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_7939141 : Nat := 118140960795 + 7939141 * 2 ^ 59
def prefixEnd_7939141 : Nat := 4983230072969 + 3 ^ 40 * 7939141 * 2
def baseEnd_7939141 : Nat := 4076595316816827808026061

theorem tailTrace_7939141 : CollatzResearch.WordTrace tailWord_7939141 prefixEnd_7939141 4076595316816827808026061 := by
  unfold tailWord_7939141
  simp only [CollatzResearch.WordTrace]
  refine ⟨289564260930855529179409277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193042840620570352786272851 289564260930855529179409277)
  ·
    refine ⟨108586597849070823442278479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289564260930855529179409277 108586597849070823442278479)
    ·
      refine ⟨162879896773606235163417719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108586597849070823442278479 162879896773606235163417719)
      ·
        refine ⟨244319845160409352745126579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162879896773606235163417719 244319845160409352745126579)
        ·
          refine ⟨366479767740614029117689869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244319845160409352745126579 366479767740614029117689869)
          ·
            refine ⟨137429912902730260919133701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366479767740614029117689869 137429912902730260919133701)
            ·
              refine ⟨25768108669261923922337569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137429912902730260919133701 25768108669261923922337569)
              ·
                refine ⟨19326081501946442941753177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25768108669261923922337569 19326081501946442941753177)
                ·
                  refine ⟨14494561126459832206314883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19326081501946442941753177 14494561126459832206314883)
                  ·
                    refine ⟨21741841689689748309472325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14494561126459832206314883 21741841689689748309472325)
                    ·
                      refine ⟨4076595316816827808026061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21741841689689748309472325 4076595316816827808026061)
                      ·
                        rfl

theorem cell23_7939141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_7939141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939141 prefixEnd_7939141 := by exact prefixLift 7939141
  have htrace : WordTrace (prefixWord ++ tailWord_7939141) baseStart_7939141 baseEnd_7939141 := by
    simpa [prefixWord, tailWord_7939141, baseEnd_7939141] using wordTrace_append hprefix tailTrace_7939141
  have hstable : (prefixWord ++ tailWord_7939141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939141).length < 2 ^ (prefixWord ++ tailWord_7939141).sum := by decide
  have hdescent : baseEnd_7939141 < baseStart_7939141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939142 : List Nat := [6, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_7939142 : Nat := 118140960795 + 7939142 * 2 ^ 59
def prefixEnd_7939142 : Nat := 4983230072969 + 3 ^ 40 * 7939142 * 2
def baseEnd_7939142 : Nat := 452955092255275811568173

theorem tailTrace_7939142 : CollatzResearch.WordTrace tailWord_7939142 prefixEnd_7939142 452955092255275811568173 := by
  unfold tailWord_7939142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048884293870372073443615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193042864935901270900130453 9048884293870372073443615)
  ·
    refine ⟨13573326440805558110165423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9048884293870372073443615 13573326440805558110165423)
    ·
      refine ⟨20359989661208337165248135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13573326440805558110165423 20359989661208337165248135)
      ·
        refine ⟨30539984491812505747872203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20359989661208337165248135 30539984491812505747872203)
        ·
          refine ⟨45809976737718758621808305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30539984491812505747872203 45809976737718758621808305)
          ·
            refine ⟨34357482553289068966356229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45809976737718758621808305 34357482553289068966356229)
            ·
              refine ⟨6442027978741700431191793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34357482553289068966356229 6442027978741700431191793)
              ·
                refine ⟨4831520984056275323393845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442027978741700431191793 4831520984056275323393845)
                ·
                  refine ⟨452955092255275811568173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4831520984056275323393845 452955092255275811568173)
                  ·
                    rfl

theorem cell23_7939142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_7939142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939142 prefixEnd_7939142 := by exact prefixLift 7939142
  have htrace : WordTrace (prefixWord ++ tailWord_7939142) baseStart_7939142 baseEnd_7939142 := by
    simpa [prefixWord, tailWord_7939142, baseEnd_7939142] using wordTrace_append hprefix tailTrace_7939142
  have hstable : (prefixWord ++ tailWord_7939142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939142).length < 2 ^ (prefixWord ++ tailWord_7939142).sum := by decide
  have hdescent : baseEnd_7939142 < baseStart_7939142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939144 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_7939144 : Nat := 118140960795 + 7939144 * 2 ^ 59
def prefixEnd_7939144 : Nat := 4983230072969 + 3 ^ 40 * 7939144 * 2
def baseEnd_7939144 : Nat := 4076596857258791296288547

theorem tailTrace_7939144 : CollatzResearch.WordTrace tailWord_7939144 prefixEnd_7939144 4076596857258791296288547 := by
  unfold tailWord_7939144
  simp only [CollatzResearch.WordTrace]
  refine ⟨144782185174922330345884243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193042913566563107127845657 144782185174922330345884243)
  ·
    refine ⟨217173277762383495518826365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144782185174922330345884243 217173277762383495518826365)
    ·
      refine ⟨81439979160893810819559887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217173277762383495518826365 81439979160893810819559887)
      ·
        refine ⟨122159968741340716229339831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81439979160893810819559887 122159968741340716229339831)
        ·
          refine ⟨183239953112011074344009747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122159968741340716229339831 183239953112011074344009747)
          ·
            refine ⟨274859929668016611516014621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183239953112011074344009747 274859929668016611516014621)
            ·
              refine ⟨103072473625506229318505483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274859929668016611516014621 103072473625506229318505483)
              ·
                refine ⟨154608710438259343977758225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103072473625506229318505483 154608710438259343977758225)
                ·
                  refine ⟨115956532828694507983318669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154608710438259343977758225 115956532828694507983318669)
                  ·
                    refine ⟨43483699810760440493744501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115956532828694507983318669 43483699810760440493744501)
                    ·
                      refine ⟨4076596857258791296288547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43483699810760440493744501 4076596857258791296288547)
                      ·
                        rfl

theorem cell23_7939144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_7939144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939144 prefixEnd_7939144 := by exact prefixLift 7939144
  have htrace : WordTrace (prefixWord ++ tailWord_7939144) baseStart_7939144 baseEnd_7939144 := by
    simpa [prefixWord, tailWord_7939144, baseEnd_7939144] using wordTrace_append hprefix tailTrace_7939144
  have hstable : (prefixWord ++ tailWord_7939144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939144).length < 2 ^ (prefixWord ++ tailWord_7939144).sum := by decide
  have hdescent : baseEnd_7939144 < baseStart_7939144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939178 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_7939178 : Nat := 118140960795 + 7939178 * 2 ^ 59
def prefixEnd_7939178 : Nat := 4983230072969 + 3 ^ 40 * 7939178 * 2
def baseEnd_7939178 : Nat := 4076614315601044163263391

theorem tailTrace_7939178 : CollatzResearch.WordTrace tailWord_7939178 prefixEnd_7939178 4076614315601044163263391 := by
  unfold tailWord_7939178
  simp only [CollatzResearch.WordTrace]
  refine ⟨72391402607930371124626547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193043740287814322999004125 72391402607930371124626547)
  ·
    refine ⟨108587103911895556686939821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72391402607930371124626547 108587103911895556686939821)
    ·
      refine ⟨40720163966960833757602433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108587103911895556686939821 40720163966960833757602433)
      ·
        refine ⟨30540122975220625318201825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40720163966960833757602433 30540122975220625318201825)
        ·
          refine ⟨22905092231415468988651369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30540122975220625318201825 22905092231415468988651369)
          ·
            refine ⟨17178819173561601741488527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22905092231415468988651369 17178819173561601741488527)
            ·
              refine ⟨25768228760342402612232791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17178819173561601741488527 25768228760342402612232791)
              ·
                refine ⟨38652343140513603918349187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25768228760342402612232791 38652343140513603918349187)
                ·
                  refine ⟨57978514710770405877523781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38652343140513603918349187 57978514710770405877523781)
                  ·
                    refine ⟨10870971508269451102035709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57978514710770405877523781 10870971508269451102035709)
                    ·
                      refine ⟨4076614315601044163263391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10870971508269451102035709 4076614315601044163263391)
                      ·
                        rfl

theorem cell23_7939178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_7939178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939178 prefixEnd_7939178 := by exact prefixLift 7939178
  have htrace : WordTrace (prefixWord ++ tailWord_7939178) baseStart_7939178 baseEnd_7939178 := by
    simpa [prefixWord, tailWord_7939178, baseEnd_7939178] using wordTrace_append hprefix tailTrace_7939178
  have hstable : (prefixWord ++ tailWord_7939178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939178).length < 2 ^ (prefixWord ++ tailWord_7939178).sum := by decide
  have hdescent : baseEnd_7939178 < baseStart_7939178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939201 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7939201 : Nat := 118140960795 + 7939201 * 2 ^ 59
def prefixEnd_7939201 : Nat := 4983230072969 + 3 ^ 40 * 7939201 * 2
def baseEnd_7939201 : Nat := 4076626125656097573275785

theorem tailTrace_7939201 : CollatzResearch.WordTrace tailWord_7939201 prefixEnd_7939201 4076626125656097573275785 := by
  unfold tailWord_7939201
  simp only [CollatzResearch.WordTrace]
  refine ⟨289566449310638159426593457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193044299540425439617728971 289566449310638159426593457)
  ·
    refine ⟨217174836982978619569945093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289566449310638159426593457 217174836982978619569945093)
    ·
      refine ⟨40720281934308491169364705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217174836982978619569945093 40720281934308491169364705)
      ·
        refine ⟨30540211450731368377023529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40720281934308491169364705 30540211450731368377023529)
        ·
          refine ⟨22905158588048526282767647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30540211450731368377023529 22905158588048526282767647)
          ·
            refine ⟨34357737882072789424151471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905158588048526282767647 34357737882072789424151471)
            ·
              refine ⟨51536606823109184136227207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34357737882072789424151471 51536606823109184136227207)
              ·
                refine ⟨77304910234663776204340811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51536606823109184136227207 77304910234663776204340811)
                ·
                  refine ⟨115957365351995664306511217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77304910234663776204340811 115957365351995664306511217)
                  ·
                    refine ⟨86968024013996748229883413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115957365351995664306511217 86968024013996748229883413)
                    ·
                      refine ⟨4076626125656097573275785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86968024013996748229883413 4076626125656097573275785)
                      ·
                        rfl

theorem cell23_7939201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7939201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939201 prefixEnd_7939201 := by exact prefixLift 7939201
  have htrace : WordTrace (prefixWord ++ tailWord_7939201) baseStart_7939201 baseEnd_7939201 := by
    simpa [prefixWord, tailWord_7939201, baseEnd_7939201] using wordTrace_append hprefix tailTrace_7939201
  have hstable : (prefixWord ++ tailWord_7939201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939201).length < 2 ^ (prefixWord ++ tailWord_7939201).sum := by decide
  have hdescent : baseEnd_7939201 < baseStart_7939201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939228 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_7939228 : Nat := 118140960795 + 7939228 * 2 ^ 59
def prefixEnd_7939228 : Nat := 4983230072969 + 3 ^ 40 * 7939228 * 2
def baseEnd_7939228 : Nat := 1358879996544589655879387

theorem tailTrace_7939228 : CollatzResearch.WordTrace tailWord_7939228 prefixEnd_7939228 1358879996544589655879387 := by
  unfold tailWord_7939228
  simp only [CollatzResearch.WordTrace]
  refine ⟨144783717040770171518913169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193044956054360228691884225 144783717040770171518913169)
  ·
    refine ⟨108587787780577628639184877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144783717040770171518913169 108587787780577628639184877)
    ·
      refine ⟨40720420417716610739694329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108587787780577628639184877 40720420417716610739694329)
      ·
        refine ⟨30540315313287458054770747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40720420417716610739694329 30540315313287458054770747)
        ·
          refine ⟨45810472969931187082156121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30540315313287458054770747 45810472969931187082156121)
          ·
            refine ⟨34357854727448390311617091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45810472969931187082156121 34357854727448390311617091)
            ·
              refine ⟨51536782091172585467425637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34357854727448390311617091 51536782091172585467425637)
              ·
                refine ⟨9663146642094859775142307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51536782091172585467425637 9663146642094859775142307)
                ·
                  refine ⟨14494719963142289662713461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9663146642094859775142307 14494719963142289662713461)
                  ·
                    refine ⟨1358879996544589655879387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14494719963142289662713461 1358879996544589655879387)
                    ·
                      rfl

theorem cell23_7939228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_7939228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939228 prefixEnd_7939228 := by exact prefixLift 7939228
  have htrace : WordTrace (prefixWord ++ tailWord_7939228) baseStart_7939228 baseEnd_7939228 := by
    simpa [prefixWord, tailWord_7939228, baseEnd_7939228] using wordTrace_append hprefix tailTrace_7939228
  have hstable : (prefixWord ++ tailWord_7939228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939228).length < 2 ^ (prefixWord ++ tailWord_7939228).sum := by decide
  have hdescent : baseEnd_7939228 < baseStart_7939228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939251 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5]
def baseStart_7939251 : Nat := 118140960795 + 7939251 * 2 ^ 59
def prefixEnd_7939251 : Nat := 4983230072969 + 3 ^ 40 * 7939251 * 2
def baseEnd_7939251 : Nat := 4076651799688822377650555

theorem tailTrace_7939251 : CollatzResearch.WordTrace tailWord_7939251 prefixEnd_7939251 4076651799688822377650555 := by
  unfold tailWord_7939251
  simp only [CollatzResearch.WordTrace]
  refine ⟨289568272960457017965913607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193045515306971345310609071 289568272960457017965913607)
  ·
    refine ⟨434352409440685526948870411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289568272960457017965913607 434352409440685526948870411)
    ·
      refine ⟨651528614161028290423305617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434352409440685526948870411 651528614161028290423305617)
      ·
        refine ⟨488646460620771217817479213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651528614161028290423305617 488646460620771217817479213)
        ·
          refine ⟨183242422732789206681554705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488646460620771217817479213 183242422732789206681554705)
          ·
            refine ⟨137431817049591905011166029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183242422732789206681554705 137431817049591905011166029)
            ·
              refine ⟨51536931393596964379187261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137431817049591905011166029 51536931393596964379187261)
              ·
                refine ⟨19326349272598861642195223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51536931393596964379187261 19326349272598861642195223)
                ·
                  refine ⟨28989523908898292463292835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19326349272598861642195223 28989523908898292463292835)
                  ·
                    refine ⟨43484285863347438694939253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28989523908898292463292835 43484285863347438694939253)
                    ·
                      refine ⟨4076651799688822377650555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43484285863347438694939253 4076651799688822377650555)
                      ·
                        rfl

theorem cell23_7939251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_7939251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939251 prefixEnd_7939251 := by exact prefixLift 7939251
  have htrace : WordTrace (prefixWord ++ tailWord_7939251) baseStart_7939251 baseEnd_7939251 := by
    simpa [prefixWord, tailWord_7939251, baseEnd_7939251] using wordTrace_append hprefix tailTrace_7939251
  have hstable : (prefixWord ++ tailWord_7939251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939251).length < 2 ^ (prefixWord ++ tailWord_7939251).sum := by decide
  have hdescent : baseEnd_7939251 < baseStart_7939251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939258 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_7939258 : Nat := 118140960795 + 7939258 * 2 ^ 59
def prefixEnd_7939258 : Nat := 4983230072969 + 3 ^ 40 * 7939258 * 2
def baseEnd_7939258 : Nat := 1358885131351134616754341

theorem tailTrace_7939258 : CollatzResearch.WordTrace tailWord_7939258 prefixEnd_7939258 1358885131351134616754341 := by
  unfold tailWord_7939258
  simp only [CollatzResearch.WordTrace]
  refine ⟨72392132067857914540354607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193045685514287772107612285 72392132067857914540354607)
  ·
    refine ⟨108588198101786871810531911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72392132067857914540354607 108588198101786871810531911)
    ·
      refine ⟨162882297152680307715797867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108588198101786871810531911 162882297152680307715797867)
      ·
        refine ⟨244323445729020461573696801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162882297152680307715797867 244323445729020461573696801)
        ·
          refine ⟨183242584296765346180272601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244323445729020461573696801 183242584296765346180272601)
          ·
            refine ⟨137431938222574009635204451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183242584296765346180272601 137431938222574009635204451)
            ·
              refine ⟨206147907333861014452806677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137431938222574009635204451 206147907333861014452806677)
              ·
                refine ⟨9663183156274735052475313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206147907333861014452806677 9663183156274735052475313)
                ·
                  refine ⟨7247387367206051289356485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9663183156274735052475313 7247387367206051289356485)
                  ·
                    refine ⟨1358885131351134616754341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7247387367206051289356485 1358885131351134616754341)
                    ·
                      rfl

theorem cell23_7939258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_7939258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939258 prefixEnd_7939258 := by exact prefixLift 7939258
  have htrace : WordTrace (prefixWord ++ tailWord_7939258) baseStart_7939258 baseEnd_7939258 := by
    simpa [prefixWord, tailWord_7939258, baseEnd_7939258] using wordTrace_append hprefix tailTrace_7939258
  have hstable : (prefixWord ++ tailWord_7939258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939258).length < 2 ^ (prefixWord ++ tailWord_7939258).sum := by decide
  have hdescent : baseEnd_7939258 < baseStart_7939258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939261 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7939261 : Nat := 118140960795 + 7939261 * 2 ^ 59
def prefixEnd_7939261 : Nat := 4983230072969 + 3 ^ 40 * 7939261 * 2
def baseEnd_7939261 : Nat := 4076656934495367338525509

theorem tailTrace_7939261 : CollatzResearch.WordTrace tailWord_7939261 prefixEnd_7939261 4076656934495367338525509 := by
  unfold tailWord_7939261
  simp only [CollatzResearch.WordTrace]
  refine ⟨289568637690420789673777637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193045758460280526449185091 289568637690420789673777637)
  ·
    refine ⟨54294119566953898063833307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289568637690420789673777637 54294119566953898063833307)
    ·
      refine ⟨81441179350430847095749961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54294119566953898063833307 81441179350430847095749961)
      ·
        refine ⟨61080884512823135321812471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81441179350430847095749961 61080884512823135321812471)
        ·
          refine ⟨91621326769234702982718707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61080884512823135321812471 91621326769234702982718707)
          ·
            refine ⟨137431990153852054474078061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91621326769234702982718707 137431990153852054474078061)
            ·
              refine ⟨51536996307694520427779273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137431990153852054474078061 51536996307694520427779273)
              ·
                refine ⟨38652747230770890320834455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51536996307694520427779273 38652747230770890320834455)
                ·
                  refine ⟨57979120846156335481251683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38652747230770890320834455 57979120846156335481251683)
                  ·
                    refine ⟨86968681269234503221877525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57979120846156335481251683 86968681269234503221877525)
                    ·
                      refine ⟨4076656934495367338525509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86968681269234503221877525 4076656934495367338525509)
                      ·
                        rfl

theorem cell23_7939261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7939261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939261 prefixEnd_7939261 := by exact prefixLift 7939261
  have htrace : WordTrace (prefixWord ++ tailWord_7939261) baseStart_7939261 baseEnd_7939261 := by
    simpa [prefixWord, tailWord_7939261, baseEnd_7939261] using wordTrace_append hprefix tailTrace_7939261
  have hstable : (prefixWord ++ tailWord_7939261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939261).length < 2 ^ (prefixWord ++ tailWord_7939261).sum := by decide
  have hdescent : baseEnd_7939261 < baseStart_7939261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939266 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 6]
def baseStart_7939266 : Nat := 118140960795 + 7939266 * 2 ^ 59
def prefixEnd_7939266 : Nat := 4983230072969 + 3 ^ 40 * 7939266 * 2
def baseEnd_7939266 : Nat := 452962166877626646551443

theorem tailTrace_7939266 : CollatzResearch.WordTrace tailWord_7939266 prefixEnd_7939266 452962166877626646551443 := by
  unfold tailWord_7939266
  simp only [CollatzResearch.WordTrace]
  refine ⟨72392205013850668881927413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193045880036935117018473101 72392205013850668881927413)
  ·
    refine ⟨6786769220048500207680695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72392205013850668881927413 6786769220048500207680695)
    ·
      refine ⟨10180153830072750311521043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786769220048500207680695 10180153830072750311521043)
      ·
        refine ⟨15270230745109125467281565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180153830072750311521043 15270230745109125467281565)
        ·
          refine ⟨5726336529415922050230587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15270230745109125467281565 5726336529415922050230587)
          ·
            refine ⟨8589504794123883075345881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726336529415922050230587 8589504794123883075345881)
            ·
              refine ⟨6442128595592912306509411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8589504794123883075345881 6442128595592912306509411)
              ·
                refine ⟨9663192893389368459764117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442128595592912306509411 9663192893389368459764117)
                ·
                  refine ⟨452962166877626646551443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9663192893389368459764117 452962166877626646551443)
                  ·
                    rfl

theorem cell23_7939266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_7939266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939266 prefixEnd_7939266 := by exact prefixLift 7939266
  have htrace : WordTrace (prefixWord ++ tailWord_7939266) baseStart_7939266 baseEnd_7939266 := by
    simpa [prefixWord, tailWord_7939266, baseEnd_7939266] using wordTrace_append hprefix tailTrace_7939266
  have hstable : (prefixWord ++ tailWord_7939266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939266).length < 2 ^ (prefixWord ++ tailWord_7939266).sum := by decide
  have hdescent : baseEnd_7939266 < baseStart_7939266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939285 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7939285 : Nat := 118140960795 + 7939285 * 2 ^ 59
def prefixEnd_7939285 : Nat := 4983230072969 + 3 ^ 40 * 7939285 * 2
def baseEnd_7939285 : Nat := 4076669258031075244625399

theorem tailTrace_7939285 : CollatzResearch.WordTrace tailWord_7939285 prefixEnd_7939285 4076669258031075244625399 := by
  unfold tailWord_7939285
  simp only [CollatzResearch.WordTrace]
  refine ⟨289569513042333841772651309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193046342028222561181767539 289569513042333841772651309)
  ·
    refine ⟨108588567390875190664744241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289569513042333841772651309 108588567390875190664744241)
    ·
      refine ⟨81441425543156392998558181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108588567390875190664744241 81441425543156392998558181)
      ·
        refine ⟨15270267289341823687229659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81441425543156392998558181 15270267289341823687229659)
        ·
          refine ⟨22905400934012735530844489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15270267289341823687229659 22905400934012735530844489)
          ·
            refine ⟨17179050700509551648133367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22905400934012735530844489 17179050700509551648133367)
            ·
              refine ⟨25768576050764327472200051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17179050700509551648133367 25768576050764327472200051)
              ·
                refine ⟨38652864076146491208300077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25768576050764327472200051 38652864076146491208300077)
                ·
                  refine ⟨14494824028554934203112529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38652864076146491208300077 14494824028554934203112529)
                  ·
                    refine ⟨10871118021416200652334397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14494824028554934203112529 10871118021416200652334397)
                    ·
                      refine ⟨4076669258031075244625399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10871118021416200652334397 4076669258031075244625399)
                      ·
                        rfl

theorem cell23_7939285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7939285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939285 prefixEnd_7939285 := by exact prefixLift 7939285
  have htrace : WordTrace (prefixWord ++ tailWord_7939285) baseStart_7939285 baseEnd_7939285 := by
    simpa [prefixWord, tailWord_7939285, baseEnd_7939285] using wordTrace_append hprefix tailTrace_7939285
  have hstable : (prefixWord ++ tailWord_7939285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939285).length < 2 ^ (prefixWord ++ tailWord_7939285).sum := by decide
  have hdescent : baseEnd_7939285 < baseStart_7939285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939315 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 3]
def baseStart_7939315 : Nat := 118140960795 + 7939315 * 2 ^ 59
def prefixEnd_7939315 : Nat := 4983230072969 + 3 ^ 40 * 7939315 * 2
def baseEnd_7939315 : Nat := 4076684662450710127250261

theorem tailTrace_7939315 : CollatzResearch.WordTrace tailWord_7939315 prefixEnd_7939315 4076684662450710127250261 := by
  unfold tailWord_7939315
  simp only [CollatzResearch.WordTrace]
  refine ⟨289570607232225156896243399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193047071488150104597495599 289570607232225156896243399)
  ·
    refine ⟨434355910848337735344365099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289570607232225156896243399 434355910848337735344365099)
    ·
      refine ⟨651533866272506603016547649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434355910848337735344365099 651533866272506603016547649)
      ·
        refine ⟨488650399704379952262410737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651533866272506603016547649 488650399704379952262410737)
        ·
          refine ⟨366487799778284964196808053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488650399704379952262410737 366487799778284964196808053)
          ·
            refine ⟨34358231229214215393450755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366487799778284964196808053 34358231229214215393450755)
            ·
              refine ⟨51537346843821323090176133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34358231229214215393450755 51537346843821323090176133)
              ·
                refine ⟨9663252533216498079408025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51537346843821323090176133 9663252533216498079408025)
                ·
                  refine ⟨7247439399912373559556019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9663252533216498079408025 7247439399912373559556019)
                  ·
                    refine ⟨10871159099868560339334029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7247439399912373559556019 10871159099868560339334029)
                    ·
                      refine ⟨4076684662450710127250261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10871159099868560339334029 4076684662450710127250261)
                      ·
                        rfl

theorem cell23_7939315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 3].length) (baseStart_7939315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939315 prefixEnd_7939315 := by exact prefixLift 7939315
  have htrace : WordTrace (prefixWord ++ tailWord_7939315) baseStart_7939315 baseEnd_7939315 := by
    simpa [prefixWord, tailWord_7939315, baseEnd_7939315] using wordTrace_append hprefix tailTrace_7939315
  have hstable : (prefixWord ++ tailWord_7939315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939315).length < 2 ^ (prefixWord ++ tailWord_7939315).sum := by decide
  have hdescent : baseEnd_7939315 < baseStart_7939315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939321 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_7939321 : Nat := 118140960795 + 7939321 * 2 ^ 59
def prefixEnd_7939321 : Nat := 4983230072969 + 3 ^ 40 * 7939321 * 2
def baseEnd_7939321 : Nat := 4076687743334637103775233

theorem tailTrace_7939321 : CollatzResearch.WordTrace tailWord_7939321 prefixEnd_7939321 4076687743334637103775233 := by
  unfold tailWord_7939321
  simp only [CollatzResearch.WordTrace]
  refine ⟨289570826070203419920961817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193047217380135613280641211 289570826070203419920961817)
  ·
    refine ⟨217178119552652564940721363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289570826070203419920961817 217178119552652564940721363)
    ·
      refine ⟨325767179328978847411082045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217178119552652564940721363 325767179328978847411082045)
      ·
        refine ⟨122162692248367067779155767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325767179328978847411082045 122162692248367067779155767)
        ·
          refine ⟨183244038372550601668733651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122162692248367067779155767 183244038372550601668733651)
          ·
            refine ⟨274866057558825902503100477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183244038372550601668733651 274866057558825902503100477)
            ·
              refine ⟨103074771584559713438662679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274866057558825902503100477 103074771584559713438662679)
              ·
                refine ⟨154612157376839570157994019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103074771584559713438662679 154612157376839570157994019)
                ·
                  refine ⟨231918236065259355236991029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154612157376839570157994019 231918236065259355236991029)
                  ·
                    refine ⟨21742334631118064553467909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231918236065259355236991029 21742334631118064553467909)
                    ·
                      refine ⟨4076687743334637103775233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21742334631118064553467909 4076687743334637103775233)
                      ·
                        rfl

theorem cell23_7939321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_7939321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939321 prefixEnd_7939321 := by exact prefixLift 7939321
  have htrace : WordTrace (prefixWord ++ tailWord_7939321) baseStart_7939321 baseEnd_7939321 := by
    simpa [prefixWord, tailWord_7939321, baseEnd_7939321] using wordTrace_append hprefix tailTrace_7939321
  have hstable : (prefixWord ++ tailWord_7939321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939321).length < 2 ^ (prefixWord ++ tailWord_7939321).sum := by decide
  have hdescent : baseEnd_7939321 < baseStart_7939321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939331 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 1, 8]
def baseStart_7939331 : Nat := 118140960795 + 7939331 * 2 ^ 59
def prefixEnd_7939331 : Nat := 4983230072969 + 3 ^ 40 * 7939331 * 2
def baseEnd_7939331 : Nat := 1358897626047060688216729

theorem tailTrace_7939331 : CollatzResearch.WordTrace tailWord_7939331 prefixEnd_7939331 1358897626047060688216729 := by
  unfold tailWord_7939331
  simp only [CollatzResearch.WordTrace]
  refine ⟨289571190800167191628825847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193047460533444794419217231 289571190800167191628825847)
  ·
    refine ⟨434356786200250787443238771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289571190800167191628825847 434356786200250787443238771)
    ·
      refine ⟨651535179300376181164858157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434356786200250787443238771 651535179300376181164858157)
      ·
        refine ⟨244325692237641067936821809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651535179300376181164858157 244325692237641067936821809)
        ·
          refine ⟨183244269178230800952616357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244325692237641067936821809 183244269178230800952616357)
          ·
            refine ⟨34358300470918275178615567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183244269178230800952616357 34358300470918275178615567)
            ·
              refine ⟨51537450706377412767923351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34358300470918275178615567 51537450706377412767923351)
              ·
                refine ⟨77306176059566119151885027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51537450706377412767923351 77306176059566119151885027)
                ·
                  refine ⟨115959264089349178727827541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77306176059566119151885027 115959264089349178727827541)
                  ·
                    refine ⟨1358897626047060688216729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115959264089349178727827541 1358897626047060688216729)
                    ·
                      rfl

theorem cell23_7939331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 8].length) (baseStart_7939331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939331 prefixEnd_7939331 := by exact prefixLift 7939331
  have htrace : WordTrace (prefixWord ++ tailWord_7939331) baseStart_7939331 baseEnd_7939331 := by
    simpa [prefixWord, tailWord_7939331, baseEnd_7939331] using wordTrace_append hprefix tailTrace_7939331
  have hstable : (prefixWord ++ tailWord_7939331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939331).length < 2 ^ (prefixWord ++ tailWord_7939331).sum := by decide
  have hdescent : baseEnd_7939331 < baseStart_7939331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939332 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_7939332 : Nat := 118140960795 + 7939332 * 2 ^ 59
def prefixEnd_7939332 : Nat := 4983230072969 + 3 ^ 40 * 7939332 * 2
def baseEnd_7939332 : Nat := 4076693391621836560737683

theorem tailTrace_7939332 : CollatzResearch.WordTrace tailWord_7939332 prefixEnd_7939332 4076693391621836560737683 := by
  unfold tailWord_7939332
  simp only [CollatzResearch.WordTrace]
  refine ⟨144785613636581784399806125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193047484848775712533074833 144785613636581784399806125)
  ·
    refine ⟨54294605113718169149927297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144785613636581784399806125 54294605113718169149927297)
    ·
      refine ⟨40720953835288626862445473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54294605113718169149927297 40720953835288626862445473)
      ·
        refine ⟨30540715376466470146834105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40720953835288626862445473 30540715376466470146834105)
        ·
          refine ⟨22905536532349852610125579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30540715376466470146834105 22905536532349852610125579)
          ·
            refine ⟨34358304798524778915188369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905536532349852610125579 34358304798524778915188369)
            ·
              refine ⟨25768728598893584186391277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34358304798524778915188369 25768728598893584186391277)
              ·
                refine ⟨9663273224585094069896729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25768728598893584186391277 9663273224585094069896729)
                ·
                  refine ⟨7247454918438820552422547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9663273224585094069896729 7247454918438820552422547)
                  ·
                    refine ⟨10871182377658230828633821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7247454918438820552422547 10871182377658230828633821)
                    ·
                      refine ⟨4076693391621836560737683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10871182377658230828633821 4076693391621836560737683)
                      ·
                        rfl

theorem cell23_7939332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_7939332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939332 prefixEnd_7939332 := by exact prefixLift 7939332
  have htrace : WordTrace (prefixWord ++ tailWord_7939332) baseStart_7939332 baseEnd_7939332 := by
    simpa [prefixWord, tailWord_7939332, baseEnd_7939332] using wordTrace_append hprefix tailTrace_7939332
  have hstable : (prefixWord ++ tailWord_7939332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939332).length < 2 ^ (prefixWord ++ tailWord_7939332).sum := by decide
  have hdescent : baseEnd_7939332 < baseStart_7939332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939355 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 4, 2, 2]
def baseStart_7939355 : Nat := 118140960795 + 7939355 * 2 ^ 59
def prefixEnd_7939355 : Nat := 4983230072969 + 3 ^ 40 * 7939355 * 2
def baseEnd_7939355 : Nat := 4076705201676889970750077

theorem tailTrace_7939355 : CollatzResearch.WordTrace tailWord_7939355 prefixEnd_7939355 4076705201676889970750077 := by
  unfold tailWord_7939355
  simp only [CollatzResearch.WordTrace]
  refine ⟨289572066152080243727699519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193048044101386829151799679 289572066152080243727699519)
  ·
    refine ⟨434358099228120365591549279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289572066152080243727699519 434358099228120365591549279)
    ·
      refine ⟨651537148842180548387323919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434358099228120365591549279 651537148842180548387323919)
      ·
        refine ⟨977305723263270822580985879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651537148842180548387323919 977305723263270822580985879)
        ·
          refine ⟨1465958584894906233871478819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977305723263270822580985879 1465958584894906233871478819)
          ·
            refine ⟨2198937877342359350807218229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465958584894906233871478819 2198937877342359350807218229)
            ·
              refine ⟨206150426000846189138176709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2198937877342359350807218229 206150426000846189138176709)
              ·
                refine ⟨38653204875158660463408133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206150426000846189138176709 38653204875158660463408133)
                ·
                  refine ⟨7247475914092248836889025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38653204875158660463408133 7247475914092248836889025)
                  ·
                    refine ⟨5435606935569186627666769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247475914092248836889025 5435606935569186627666769)
                    ·
                      refine ⟨4076705201676889970750077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435606935569186627666769 4076705201676889970750077)
                      ·
                        rfl

theorem cell23_7939355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 2, 2].length) (baseStart_7939355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939355 prefixEnd_7939355 := by exact prefixLift 7939355
  have htrace : WordTrace (prefixWord ++ tailWord_7939355) baseStart_7939355 baseEnd_7939355 := by
    simpa [prefixWord, tailWord_7939355, baseEnd_7939355] using wordTrace_append hprefix tailTrace_7939355
  have hstable : (prefixWord ++ tailWord_7939355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939355).length < 2 ^ (prefixWord ++ tailWord_7939355).sum := by decide
  have hdescent : baseEnd_7939355 < baseStart_7939355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939361 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 11]
def baseStart_7939361 : Nat := 118140960795 + 7939361 * 2 ^ 59
def prefixEnd_7939361 : Nat := 4983230072969 + 3 ^ 40 * 7939361 * 2
def baseEnd_7939361 : Nat := 452967586951201883030561

theorem tailTrace_7939361 : CollatzResearch.WordTrace tailWord_7939361 prefixEnd_7939361 452967586951201883030561 := by
  unfold tailWord_7939361
  simp only [CollatzResearch.WordTrace]
  refine ⟨289572284990058506752417937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193048189993372337834945291 289572284990058506752417937)
  ·
    refine ⟨217179213742543880064313453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289572284990058506752417937 217179213742543880064313453)
    ·
      refine ⟨81442205153453955024117545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217179213742543880064313453 81442205153453955024117545)
      ·
        refine ⟨61081653865090466268088159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81442205153453955024117545 61081653865090466268088159)
        ·
          refine ⟨91622480797635699402132239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61081653865090466268088159 91622480797635699402132239)
          ·
            refine ⟨137433721196453549103198359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91622480797635699402132239 137433721196453549103198359)
            ·
              refine ⟨206150581794680323654797539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137433721196453549103198359 206150581794680323654797539)
              ·
                refine ⟨309225872692020485482196309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206150581794680323654797539 309225872692020485482196309)
                ·
                  refine ⟨452967586951201883030561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 309225872692020485482196309 452967586951201883030561)
                  ·
                    rfl

theorem cell23_7939361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 11].length) (baseStart_7939361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939361 prefixEnd_7939361 := by exact prefixLift 7939361
  have htrace : WordTrace (prefixWord ++ tailWord_7939361) baseStart_7939361 baseEnd_7939361 := by
    simpa [prefixWord, tailWord_7939361, baseEnd_7939361] using wordTrace_append hprefix tailTrace_7939361
  have hstable : (prefixWord ++ tailWord_7939361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939361).length < 2 ^ (prefixWord ++ tailWord_7939361).sum := by decide
  have hdescent : baseEnd_7939361 < baseStart_7939361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939378 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 7]
def baseStart_7939378 : Nat := 118140960795 + 7939378 * 2 ^ 59
def prefixEnd_7939378 : Nat := 4983230072969 + 3 ^ 40 * 7939378 * 2
def baseEnd_7939378 : Nat := 452968556859104820084719

theorem tailTrace_7939378 : CollatzResearch.WordTrace tailWord_7939378 prefixEnd_7939378 452968556859104820084719 := by
  unfold tailWord_7939378
  simp only [CollatzResearch.WordTrace]
  refine ⟨72393226257749229663946697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193048603353997945770524525 72393226257749229663946697)
  ·
    refine ⟨54294919693311922247960023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72393226257749229663946697 54294919693311922247960023)
    ·
      refine ⟨81442379539967883371940035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54294919693311922247960023 81442379539967883371940035)
      ·
        refine ⟨122163569309951825057910053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81442379539967883371940035 122163569309951825057910053)
        ·
          refine ⟨22905669245615967198358135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122163569309951825057910053 22905669245615967198358135)
          ·
            refine ⟨34358503868423950797537203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905669245615967198358135 34358503868423950797537203)
            ·
              refine ⟨51537755802635926196305805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34358503868423950797537203 51537755802635926196305805)
              ·
                refine ⟨19326658425988472323614677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51537755802635926196305805 19326658425988472323614677)
                ·
                  refine ⟨452968556859104820084719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19326658425988472323614677 452968556859104820084719)
                  ·
                    rfl

theorem cell23_7939378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_7939378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939378 prefixEnd_7939378 := by exact prefixLift 7939378
  have htrace : WordTrace (prefixWord ++ tailWord_7939378) baseStart_7939378 baseEnd_7939378 := by
    simpa [prefixWord, tailWord_7939378, baseEnd_7939378] using wordTrace_append hprefix tailTrace_7939378
  have hstable : (prefixWord ++ tailWord_7939378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939378).length < 2 ^ (prefixWord ++ tailWord_7939378).sum := by decide
  have hdescent : baseEnd_7939378 < baseStart_7939378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939408 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 2, 5]
def baseStart_7939408 : Nat := 118140960795 + 7939408 * 2 ^ 59
def prefixEnd_7939408 : Nat := 4983230072969 + 3 ^ 40 * 7939408 * 2
def baseEnd_7939408 : Nat := 1358910805383859421129111

theorem tailTrace_7939408 : CollatzResearch.WordTrace tailWord_7939408 prefixEnd_7939408 1358910805383859421129111 := by
  unfold tailWord_7939408
  simp only [CollatzResearch.WordTrace]
  refine ⟨144786999610444116889689439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193049332813925489186252585 144786999610444116889689439)
  ·
    refine ⟨217180499415666175334534159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144786999610444116889689439 217180499415666175334534159)
    ·
      refine ⟨325770749123499263001801239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217180499415666175334534159 325770749123499263001801239)
      ·
        refine ⟨488656123685248894502701859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325770749123499263001801239 488656123685248894502701859)
        ·
          refine ⟨732984185527873341754052789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488656123685248894502701859 732984185527873341754052789)
          ·
            refine ⟨68717267393238125789442449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 732984185527873341754052789 68717267393238125789442449)
            ·
              refine ⟨51537950544928594342081837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68717267393238125789442449 51537950544928594342081837)
              ·
                refine ⟨19326731454348222878280689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51537950544928594342081837 19326731454348222878280689)
                ·
                  refine ⟨14495048590761167158710517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19326731454348222878280689 14495048590761167158710517)
                  ·
                    refine ⟨1358910805383859421129111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14495048590761167158710517 1358910805383859421129111)
                    ·
                      rfl

theorem cell23_7939408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_7939408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939408 prefixEnd_7939408 := by exact prefixLift 7939408
  have htrace : WordTrace (prefixWord ++ tailWord_7939408) baseStart_7939408 baseEnd_7939408 := by
    simpa [prefixWord, tailWord_7939408, baseEnd_7939408] using wordTrace_append hprefix tailTrace_7939408
  have hstable : (prefixWord ++ tailWord_7939408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939408).length < 2 ^ (prefixWord ++ tailWord_7939408).sum := by decide
  have hdescent : baseEnd_7939408 < baseStart_7939408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939485 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 6]
def baseStart_7939485 : Nat := 118140960795 + 7939485 * 2 ^ 59
def prefixEnd_7939485 : Nat := 4983230072969 + 3 ^ 40 * 7939485 * 2
def baseEnd_7939485 : Nat := 452974661573552718013831

theorem tailTrace_7939485 : CollatzResearch.WordTrace tailWord_7939485 prefixEnd_7939485 452974661573552718013831 := by
  unfold tailWord_7939485
  simp only [CollatzResearch.WordTrace]
  refine ⟨289576807641609275929931909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193051205094406183953287939 289576807641609275929931909)
  ·
    refine ⟨54295651432801739236862233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289576807641609275929931909 54295651432801739236862233)
    ·
      refine ⟨40721738574601304427646675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54295651432801739236862233 40721738574601304427646675)
      ·
        refine ⟨61082607861901956641470013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40721738574601304427646675 61082607861901956641470013)
        ·
          refine ⟨22905977948213233740551255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61082607861901956641470013 22905977948213233740551255)
          ·
            refine ⟨34358966922319850610826883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905977948213233740551255 34358966922319850610826883)
            ·
              refine ⟨51538450383479775916240325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34358966922319850610826883 51538450383479775916240325)
              ·
                refine ⟨9663459446902457984295061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51538450383479775916240325 9663459446902457984295061)
                ·
                  refine ⟨452974661573552718013831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9663459446902457984295061 452974661573552718013831)
                  ·
                    rfl

theorem cell23_7939485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_7939485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939485 prefixEnd_7939485 := by exact prefixLift 7939485
  have htrace : WordTrace (prefixWord ++ tailWord_7939485) baseStart_7939485 baseEnd_7939485 := by
    simpa [prefixWord, tailWord_7939485, baseEnd_7939485] using wordTrace_append hprefix tailTrace_7939485
  have hstable : (prefixWord ++ tailWord_7939485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939485).length < 2 ^ (prefixWord ++ tailWord_7939485).sum := by decide
  have hdescent : baseEnd_7939485 < baseStart_7939485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939488 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_7939488 : Nat := 118140960795 + 7939488 * 2 ^ 59
def prefixEnd_7939488 : Nat := 4983230072969 + 3 ^ 40 * 7939488 * 2
def baseEnd_7939488 : Nat := 4076773494603937950386965

theorem tailTrace_7939488 : CollatzResearch.WordTrace tailWord_7939488 prefixEnd_7939488 4076773494603937950386965 := by
  unfold tailWord_7939488
  simp only [CollatzResearch.WordTrace]
  refine ⟨144788458530299203721145559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193051278040398938294860745 144788458530299203721145559)
  ·
    refine ⟨217182687795448805581718339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144788458530299203721145559 217182687795448805581718339)
    ·
      refine ⟨325774031693173208372577509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217182687795448805581718339 325774031693173208372577509)
      ·
        refine ⟨61082630942469976569858283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325774031693173208372577509 61082630942469976569858283)
        ·
          refine ⟨91623946413704964854787425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61082630942469976569858283 91623946413704964854787425)
          ·
            refine ⟨68717959810278723641090569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91623946413704964854787425 68717959810278723641090569)
            ·
              refine ⟨51538469857709042730817927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68717959810278723641090569 51538469857709042730817927)
              ·
                refine ⟨77307704786563564096226891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51538469857709042730817927 77307704786563564096226891)
                ·
                  refine ⟨115961557179845346144340337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77307704786563564096226891 115961557179845346144340337)
                  ·
                    refine ⟨86971167884884009608255253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115961557179845346144340337 86971167884884009608255253)
                    ·
                      refine ⟨4076773494603937950386965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86971167884884009608255253 4076773494603937950386965)
                      ·
                        rfl

theorem cell23_7939488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_7939488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939488 prefixEnd_7939488 := by exact prefixLift 7939488
  have htrace : WordTrace (prefixWord ++ tailWord_7939488) baseStart_7939488 baseEnd_7939488 := by
    simpa [prefixWord, tailWord_7939488, baseEnd_7939488] using wordTrace_append hprefix tailTrace_7939488
  have hstable : (prefixWord ++ tailWord_7939488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939488).length < 2 ^ (prefixWord ++ tailWord_7939488).sum := by decide
  have hdescent : baseEnd_7939488 < baseStart_7939488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939516 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7939516 : Nat := 118140960795 + 7939516 * 2 ^ 59
def prefixEnd_7939516 : Nat := 4983230072969 + 3 ^ 40 * 7939516 * 2
def baseEnd_7939516 : Nat := 4076787872062263840836837

theorem tailTrace_7939516 : CollatzResearch.WordTrace tailWord_7939516 prefixEnd_7939516 4076787872062263840836837 := by
  unfold tailWord_7939516
  simp only [CollatzResearch.WordTrace]
  refine ⟨144788969152248484112155201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193051958869664645482873601 144788969152248484112155201)
  ·
    refine ⟨108591726864186363084116401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144788969152248484112155201 108591726864186363084116401)
    ·
      refine ⟨81443795148139772313087301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108591726864186363084116401 81443795148139772313087301)
      ·
        refine ⟨15270711590276207308703869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81443795148139772313087301 15270711590276207308703869)
        ·
          refine ⟨5726516846353577740763951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15270711590276207308703869 5726516846353577740763951)
          ·
            refine ⟨8589775269530366611145927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726516846353577740763951 8589775269530366611145927)
            ·
              refine ⟨12884662904295549916718891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8589775269530366611145927 12884662904295549916718891)
              ·
                refine ⟨19326994356443324875078337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12884662904295549916718891 19326994356443324875078337)
                ·
                  refine ⟨14495245767332493656308753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19326994356443324875078337 14495245767332493656308753)
                  ·
                    refine ⟨10871434325499370242231565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14495245767332493656308753 10871434325499370242231565)
                    ·
                      refine ⟨4076787872062263840836837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10871434325499370242231565 4076787872062263840836837)
                      ·
                        rfl

theorem cell23_7939516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7939516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939516 prefixEnd_7939516 := by exact prefixLift 7939516
  have htrace : WordTrace (prefixWord ++ tailWord_7939516) baseStart_7939516 baseEnd_7939516 := by
    simpa [prefixWord, tailWord_7939516, baseEnd_7939516] using wordTrace_append hprefix tailTrace_7939516
  have hstable : (prefixWord ++ tailWord_7939516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939516).length < 2 ^ (prefixWord ++ tailWord_7939516).sum := by decide
  have hdescent : baseEnd_7939516 < baseStart_7939516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939532 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_7939532 : Nat := 118140960795 + 7939532 * 2 ^ 59
def prefixEnd_7939532 : Nat := 4983230072969 + 3 ^ 40 * 7939532 * 2
def baseEnd_7939532 : Nat := 1358932029250911926078921

theorem tailTrace_7939532 : CollatzResearch.WordTrace tailWord_7939532 prefixEnd_7939532 1358932029250911926078921 := by
  unfold tailWord_7939532
  simp only [CollatzResearch.WordTrace]
  refine ⟨144789260936219501478446425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193052347914959335304595233 144789260936219501478446425)
  ·
    refine ⟨108591945702164626108834819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144789260936219501478446425 108591945702164626108834819)
    ·
      refine ⟨162887918553246939163252229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108591945702164626108834819 162887918553246939163252229)
      ·
        refine ⟨30541484728733801093109793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162887918553246939163252229 30541484728733801093109793)
        ·
          refine ⟨22906113546550350819832345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30541484728733801093109793 22906113546550350819832345)
          ·
            refine ⟨17179585159912763114874259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22906113546550350819832345 17179585159912763114874259)
            ·
              refine ⟨25769377739869144672311389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17179585159912763114874259 25769377739869144672311389)
              ·
                refine ⟨9663516652450929252116771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25769377739869144672311389 9663516652450929252116771)
                ·
                  refine ⟨14495274978676393878175157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9663516652450929252116771 14495274978676393878175157)
                  ·
                    refine ⟨1358932029250911926078921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14495274978676393878175157 1358932029250911926078921)
                    ·
                      rfl

theorem cell23_7939532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_7939532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939532 prefixEnd_7939532 := by exact prefixLift 7939532
  have htrace : WordTrace (prefixWord ++ tailWord_7939532) baseStart_7939532 baseEnd_7939532 := by
    simpa [prefixWord, tailWord_7939532, baseEnd_7939532] using wordTrace_append hprefix tailTrace_7939532
  have hstable : (prefixWord ++ tailWord_7939532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939532).length < 2 ^ (prefixWord ++ tailWord_7939532).sum := by decide
  have hdescent : baseEnd_7939532 < baseStart_7939532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939555 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7939555 : Nat := 118140960795 + 7939555 * 2 ^ 59
def prefixEnd_7939555 : Nat := 4983230072969 + 3 ^ 40 * 7939555 * 2
def baseEnd_7939555 : Nat := 4076807897807789188249157

theorem tailTrace_7939555 : CollatzResearch.WordTrace tailWord_7939555 prefixEnd_7939555 4076807897807789188249157 := by
  unfold tailWord_7939555
  simp only [CollatzResearch.WordTrace]
  refine ⟨289579360751355677884980119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193052907167570451923320079 289579360751355677884980119)
  ·
    refine ⟨434369041127033516827470179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289579360751355677884980119 434369041127033516827470179)
    ·
      refine ⟨651553561690550275241205269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434369041127033516827470179 651553561690550275241205269)
      ·
        refine ⟨30541573204244544151931497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 651553561690550275241205269 30541573204244544151931497)
        ·
          refine ⟨22906179903183408113948623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30541573204244544151931497 22906179903183408113948623)
          ·
            refine ⟨34359269854775112170922935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22906179903183408113948623 34359269854775112170922935)
            ·
              refine ⟨51538904782162668256384403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34359269854775112170922935 51538904782162668256384403)
              ·
                refine ⟨77308357173244002384576605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51538904782162668256384403 77308357173244002384576605)
                ·
                  refine ⟨28990633939966500894216227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77308357173244002384576605 28990633939966500894216227)
                  ·
                    refine ⟨43485950909949751341324341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28990633939966500894216227 43485950909949751341324341)
                    ·
                      refine ⟨4076807897807789188249157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43485950909949751341324341 4076807897807789188249157)
                      ·
                        rfl

theorem cell23_7939555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7939555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939555 prefixEnd_7939555 := by exact prefixLift 7939555
  have htrace : WordTrace (prefixWord ++ tailWord_7939555) baseStart_7939555 baseEnd_7939555 := by
    simpa [prefixWord, tailWord_7939555, baseEnd_7939555] using wordTrace_append hprefix tailTrace_7939555
  have hstable : (prefixWord ++ tailWord_7939555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939555).length < 2 ^ (prefixWord ++ tailWord_7939555).sum := by decide
  have hdescent : baseEnd_7939555 < baseStart_7939555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939569 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 3, 2, 2]
def baseStart_7939569 : Nat := 118140960795 + 7939569 * 2 ^ 59
def prefixEnd_7939569 : Nat := 4983230072969 + 3 ^ 40 * 7939569 * 2
def baseEnd_7939569 : Nat := 4076815086536952133474093

theorem tailTrace_7939569 : CollatzResearch.WordTrace tailWord_7939569 prefixEnd_7939569 4076815086536952133474093 := by
  unfold tailWord_7939569
  simp only [CollatzResearch.WordTrace]
  refine ⟨289579871373304958275989761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193053247582203305517326507 289579871373304958275989761)
  ·
    refine ⟨217184903529978718706992321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289579871373304958275989761 217184903529978718706992321)
    ·
      refine ⟨162888677647484039030244241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217184903529978718706992321 162888677647484039030244241)
      ·
        refine ⟨122166508235613029272683181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162888677647484039030244241 122166508235613029272683181)
        ·
          refine ⟨45812440588354885977256193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122166508235613029272683181 45812440588354885977256193)
          ·
            refine ⟨34359330441266164482942145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45812440588354885977256193 34359330441266164482942145)
            ·
              refine ⟨25769497830949623362206609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34359330441266164482942145 25769497830949623362206609)
              ·
                refine ⟨19327123373212217521654957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25769497830949623362206609 19327123373212217521654957)
                ·
                  refine ⟨7247671264954581570620609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19327123373212217521654957 7247671264954581570620609)
                  ·
                    refine ⟨5435753448715936177965457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247671264954581570620609 5435753448715936177965457)
                    ·
                      refine ⟨4076815086536952133474093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435753448715936177965457 4076815086536952133474093)
                      ·
                        rfl

theorem cell23_7939569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_7939569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939569 prefixEnd_7939569 := by exact prefixLift 7939569
  have htrace : WordTrace (prefixWord ++ tailWord_7939569) baseStart_7939569 baseEnd_7939569 := by
    simpa [prefixWord, tailWord_7939569, baseEnd_7939569] using wordTrace_append hprefix tailTrace_7939569
  have hstable : (prefixWord ++ tailWord_7939569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939569).length < 2 ^ (prefixWord ++ tailWord_7939569).sum := by decide
  have hdescent : baseEnd_7939569 < baseStart_7939569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939590 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7939590 : Nat := 118140960795 + 7939590 * 2 ^ 59
def prefixEnd_7939590 : Nat := 4983230072969 + 3 ^ 40 * 7939590 * 2
def baseEnd_7939590 : Nat := 4076825869630696551311497

theorem tailTrace_7939590 : CollatzResearch.WordTrace tailWord_7939590 prefixEnd_7939590 4076825869630696551311497 := by
  unfold tailWord_7939590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049394915819652464453257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193053758204152585908336149 9049394915819652464453257)
  ·
    refine ⟨6787046186864739348339943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9049394915819652464453257 6787046186864739348339943)
    ·
      refine ⟨10180569280297109022509915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6787046186864739348339943 10180569280297109022509915)
      ·
        refine ⟨15270853920445663533764873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180569280297109022509915 15270853920445663533764873)
        ·
          refine ⟨11453140440334247650323655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15270853920445663533764873 11453140440334247650323655)
          ·
            refine ⟨17179710660501371475485483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453140440334247650323655 17179710660501371475485483)
            ·
              refine ⟨25769565990752057213228225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17179710660501371475485483 25769565990752057213228225)
              ·
                refine ⟨19327174493064042909921169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25769565990752057213228225 19327174493064042909921169)
                ·
                  refine ⟨14495380869798032182440877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19327174493064042909921169 14495380869798032182440877)
                  ·
                    refine ⟨5435767826174262068415329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14495380869798032182440877 5435767826174262068415329)
                    ·
                      refine ⟨4076825869630696551311497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435767826174262068415329 4076825869630696551311497)
                      ·
                        rfl

theorem cell23_7939590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7939590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939590 prefixEnd_7939590 := by exact prefixLift 7939590
  have htrace : WordTrace (prefixWord ++ tailWord_7939590) baseStart_7939590 baseEnd_7939590 := by
    simpa [prefixWord, tailWord_7939590, baseEnd_7939590] using wordTrace_append hprefix tailTrace_7939590
  have hstable : (prefixWord ++ tailWord_7939590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939590).length < 2 ^ (prefixWord ++ tailWord_7939590).sum := by decide
  have hdescent : baseEnd_7939590 < baseStart_7939590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939597 : List Nat := [1, 7, 1, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7939597 : Nat := 118140960795 + 7939597 * 2 ^ 59
def prefixEnd_7939597 : Nat := 4983230072969 + 3 ^ 40 * 7939597 * 2
def baseEnd_7939597 : Nat := 4076829463995278023923965

theorem tailTrace_7939597 : CollatzResearch.WordTrace tailWord_7939597 prefixEnd_7939597 4076829463995278023923965 := by
  unfold tailWord_7939597
  simp only [CollatzResearch.WordTrace]
  refine ⟨289580892617203519058009045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193053928411469012705339363 289580892617203519058009045)
  ·
    refine ⟨6787052170715707477922087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 289580892617203519058009045 6787052170715707477922087)
    ·
      refine ⟨10180578256073561216883131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6787052170715707477922087 10180578256073561216883131)
      ·
        refine ⟨15270867384110341825324697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180578256073561216883131 15270867384110341825324697)
        ·
          refine ⟨11453150538082756368993523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15270867384110341825324697 11453150538082756368993523)
          ·
            refine ⟨17179725807124134553490285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453150538082756368993523 17179725807124134553490285)
            ·
              refine ⟨6442397177671550457558857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17179725807124134553490285 6442397177671550457558857)
              ·
                refine ⟨4831797883253662843169143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442397177671550457558857 4831797883253662843169143)
                ·
                  refine ⟨7247696824880494264753715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831797883253662843169143 7247696824880494264753715)
                  ·
                    refine ⟨10871545237320741397130573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7247696824880494264753715 10871545237320741397130573)
                    ·
                      refine ⟨4076829463995278023923965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10871545237320741397130573 4076829463995278023923965)
                      ·
                        rfl

theorem cell23_7939597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7939597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939597 prefixEnd_7939597 := by exact prefixLift 7939597
  have htrace : WordTrace (prefixWord ++ tailWord_7939597) baseStart_7939597 baseEnd_7939597 := by
    simpa [prefixWord, tailWord_7939597, baseEnd_7939597] using wordTrace_append hprefix tailTrace_7939597
  have hstable : (prefixWord ++ tailWord_7939597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939597).length < 2 ^ (prefixWord ++ tailWord_7939597).sum := by decide
  have hdescent : baseEnd_7939597 < baseStart_7939597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939603 : List Nat := [1, 1, 1, 2, 1, 7, 3, 2, 1, 2, 2]
def baseStart_7939603 : Nat := 118140960795 + 7939603 * 2 ^ 59
def prefixEnd_7939603 : Nat := 4983230072969 + 3 ^ 40 * 7939603 * 2
def baseEnd_7939603 : Nat := 4076832544879205000448937

theorem tailTrace_7939603 : CollatzResearch.WordTrace tailWord_7939603 prefixEnd_7939603 4076832544879205000448937 := by
  unfold tailWord_7939603
  simp only [CollatzResearch.WordTrace]
  refine ⟨289581111455181782082727463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193054074303454521388484975 289581111455181782082727463)
  ·
    refine ⟨434371667182772673124091195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289581111455181782082727463 434371667182772673124091195)
    ·
      refine ⟨651557500774159009686136793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434371667182772673124091195 651557500774159009686136793)
      ·
        refine ⟨488668125580619257264602595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651557500774159009686136793 488668125580619257264602595)
        ·
          refine ⟨733002188370928885896903893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488668125580619257264602595 733002188370928885896903893)
          ·
            refine ⟨17179738789943645763208685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 733002188370928885896903893 17179738789943645763208685)
            ·
              refine ⟨6442402046228867161203257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17179738789943645763208685 6442402046228867161203257)
              ·
                refine ⟨4831801534671650370902443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442402046228867161203257 4831801534671650370902443)
                ·
                  refine ⟨7247702302007475556353665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831801534671650370902443 7247702302007475556353665)
                  ·
                    refine ⟨5435776726505606667265249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247702302007475556353665 5435776726505606667265249)
                    ·
                      refine ⟨4076832544879205000448937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435776726505606667265249 4076832544879205000448937)
                      ·
                        rfl

theorem cell23_7939603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 2, 2].length) (baseStart_7939603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939603 prefixEnd_7939603 := by exact prefixLift 7939603
  have htrace : WordTrace (prefixWord ++ tailWord_7939603) baseStart_7939603 baseEnd_7939603 := by
    simpa [prefixWord, tailWord_7939603, baseEnd_7939603] using wordTrace_append hprefix tailTrace_7939603
  have hstable : (prefixWord ++ tailWord_7939603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939603).length < 2 ^ (prefixWord ++ tailWord_7939603).sum := by decide
  have hdescent : baseEnd_7939603 < baseStart_7939603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939654 : List Nat := [6, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_7939654 : Nat := 118140960795 + 7939654 * 2 ^ 59
def prefixEnd_7939654 : Nat := 4983230072969 + 3 ^ 40 * 7939654 * 2
def baseEnd_7939654 : Nat := 4076858732392584300911203

theorem tailTrace_7939654 : CollatzResearch.WordTrace tailWord_7939654 prefixEnd_7939654 4076858732392584300911203 := by
  unfold tailWord_7939654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049467861812406806026063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193055314385331345195222677 9049467861812406806026063)
  ·
    refine ⟨13574201792718610209039095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049467861812406806026063 13574201792718610209039095)
    ·
      refine ⟨20361302689077915313558643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13574201792718610209039095 20361302689077915313558643)
      ·
        refine ⟨30541954033616872970337965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20361302689077915313558643 30541954033616872970337965)
        ·
          refine ⟨11453232762606327363876737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30541954033616872970337965 11453232762606327363876737)
          ·
            refine ⟨8589924571954745522907553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11453232762606327363876737 8589924571954745522907553)
            ·
              refine ⟨6442443428966059142180665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8589924571954745522907553 6442443428966059142180665)
              ·
                refine ⟨4831832571724544356635499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442443428966059142180665 4831832571724544356635499)
                ·
                  refine ⟨7247748857586816534953249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831832571724544356635499 7247748857586816534953249)
                  ·
                    refine ⟨5435811643190112401214937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247748857586816534953249 5435811643190112401214937)
                    ·
                      refine ⟨4076858732392584300911203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435811643190112401214937 4076858732392584300911203)
                      ·
                        rfl

theorem cell23_7939654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_7939654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939654 prefixEnd_7939654 := by exact prefixLift 7939654
  have htrace : WordTrace (prefixWord ++ tailWord_7939654) baseStart_7939654 baseEnd_7939654 := by
    simpa [prefixWord, tailWord_7939654, baseEnd_7939654] using wordTrace_append hprefix tailTrace_7939654
  have hstable : (prefixWord ++ tailWord_7939654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939654).length < 2 ^ (prefixWord ++ tailWord_7939654).sum := by decide
  have hdescent : baseEnd_7939654 < baseStart_7939654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939665 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 7]
def baseStart_7939665 : Nat := 118140960795 + 7939665 * 2 ^ 59
def prefixEnd_7939665 : Nat := 4983230072969 + 3 ^ 40 * 7939665 * 2
def baseEnd_7939665 : Nat := 452984931186642639763739

theorem tailTrace_7939665 : CollatzResearch.WordTrace tailWord_7939665 prefixEnd_7939665 452984931186642639763739 := by
  unfold tailWord_7939665
  simp only [CollatzResearch.WordTrace]
  refine ⟨289583372780957166671484449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193055581853971444447656299 289583372780957166671484449)
  ·
    refine ⟨217187529585717875003613337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289583372780957166671484449 217187529585717875003613337)
    ·
      refine ⟨162890647189288406252710003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217187529585717875003613337 162890647189288406252710003)
      ·
        refine ⟨244335970783932609379065005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162890647189288406252710003 244335970783932609379065005)
        ·
          refine ⟨91625989043974728517149377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244335970783932609379065005 91625989043974728517149377)
          ·
            refine ⟨68719491782981046387862033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91625989043974728517149377 68719491782981046387862033)
            ·
              refine ⟨51539618837235784790896525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68719491782981046387862033 51539618837235784790896525)
              ·
                refine ⟨19327357063963419296586197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51539618837235784790896525 19327357063963419296586197)
                ·
                  refine ⟨452984931186642639763739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19327357063963419296586197 452984931186642639763739)
                  ·
                    rfl

theorem cell23_7939665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 7].length) (baseStart_7939665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939665 prefixEnd_7939665 := by exact prefixLift 7939665
  have htrace : WordTrace (prefixWord ++ tailWord_7939665) baseStart_7939665 baseEnd_7939665 := by
    simpa [prefixWord, tailWord_7939665, baseEnd_7939665] using wordTrace_append hprefix tailTrace_7939665
  have hstable : (prefixWord ++ tailWord_7939665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939665).length < 2 ^ (prefixWord ++ tailWord_7939665).sum := by decide
  have hdescent : baseEnd_7939665 < baseStart_7939665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939676 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_7939676 : Nat := 118140960795 + 7939676 * 2 ^ 59
def prefixEnd_7939676 : Nat := 4983230072969 + 3 ^ 40 * 7939676 * 2
def baseEnd_7939676 : Nat := 4076870028966983214836101

theorem tailTrace_7939676 : CollatzResearch.WordTrace tailWord_7939676 prefixEnd_7939676 4076870028966983214836101 := by
  unfold tailWord_7939676
  simp only [CollatzResearch.WordTrace]
  refine ⟨144791886991958657775067441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193055849322611543700089921 144791886991958657775067441)
  ·
    refine ⟨108593915243968993331300581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144791886991958657775067441 108593915243968993331300581)
    ·
      refine ⟨20361359108244186249618859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108593915243968993331300581 20361359108244186249618859)
      ·
        refine ⟨30542038662366279374428289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20361359108244186249618859 30542038662366279374428289)
        ·
          refine ⟨22906528996774709530821217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30542038662366279374428289 22906528996774709530821217)
          ·
            refine ⟨17179896747581032148115913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22906528996774709530821217 17179896747581032148115913)
            ·
              refine ⟨12884922560685774111086935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17179896747581032148115913 12884922560685774111086935)
              ·
                refine ⟨19327383841028661166630403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12884922560685774111086935 19327383841028661166630403)
                ·
                  refine ⟨28991075761542991749945605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19327383841028661166630403 28991075761542991749945605)
                  ·
                    refine ⟨5435826705289310953114801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28991075761542991749945605 5435826705289310953114801)
                    ·
                      refine ⟨4076870028966983214836101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435826705289310953114801 4076870028966983214836101)
                      ·
                        rfl

theorem cell23_7939676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_7939676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939676 prefixEnd_7939676 := by exact prefixLift 7939676
  have htrace : WordTrace (prefixWord ++ tailWord_7939676) baseStart_7939676 baseEnd_7939676 := by
    simpa [prefixWord, tailWord_7939676, baseEnd_7939676] using wordTrace_append hprefix tailTrace_7939676
  have hstable : (prefixWord ++ tailWord_7939676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939676).length < 2 ^ (prefixWord ++ tailWord_7939676).sum := by decide
  have hdescent : baseEnd_7939676 < baseStart_7939676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939766 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7939766 : Nat := 118140960795 + 7939766 * 2 ^ 59
def prefixEnd_7939766 : Nat := 4983230072969 + 3 ^ 40 * 7939766 * 2
def baseEnd_7939766 : Nat := 4076916242225887862710687

theorem tailTrace_7939766 : CollatzResearch.WordTrace tailWord_7939766 prefixEnd_7939766 4076916242225887862710687 := by
  unfold tailWord_7939766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18099191034599453807556947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193058037702394173947274101 18099191034599453807556947)
  ·
    refine ⟨27148786551899180711335421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18099191034599453807556947 27148786551899180711335421)
    ·
      refine ⟨10180794956962192766750783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27148786551899180711335421 10180794956962192766750783)
      ·
        refine ⟨15271192435443289150126175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180794956962192766750783 15271192435443289150126175)
        ·
          refine ⟨22906788653164933725189263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15271192435443289150126175 22906788653164933725189263)
          ·
            refine ⟨34360182979747400587783895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22906788653164933725189263 34360182979747400587783895)
            ·
              refine ⟨51540274469621100881675843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34360182979747400587783895 51540274469621100881675843)
              ·
                refine ⟨77310411704431651322513765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51540274469621100881675843 77310411704431651322513765)
                ·
                  refine ⟨14495702194580934622971331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77310411704431651322513765 14495702194580934622971331)
                  ·
                    refine ⟨21743553291871401934456997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14495702194580934622971331 21743553291871401934456997)
                    ·
                      refine ⟨4076916242225887862710687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21743553291871401934456997 4076916242225887862710687)
                      ·
                        rfl

theorem cell23_7939766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7939766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939766 prefixEnd_7939766 := by exact prefixLift 7939766
  have htrace : WordTrace (prefixWord ++ tailWord_7939766) baseStart_7939766 baseEnd_7939766 := by
    simpa [prefixWord, tailWord_7939766, baseEnd_7939766] using wordTrace_append hprefix tailTrace_7939766
  have hstable : (prefixWord ++ tailWord_7939766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939766).length < 2 ^ (prefixWord ++ tailWord_7939766).sum := by decide
  have hdescent : baseEnd_7939766 < baseStart_7939766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939772 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 8]
def baseStart_7939772 : Nat := 118140960795 + 7939772 * 2 ^ 59
def prefixEnd_7939772 : Nat := 4983230072969 + 3 ^ 40 * 7939772 * 2
def baseEnd_7939772 : Nat := 452991035901090537692851

theorem tailTrace_7939772 : CollatzResearch.WordTrace tailWord_7939772 prefixEnd_7939772 452991035901090537692851 := by
  unfold tailWord_7939772
  simp only [CollatzResearch.WordTrace]
  refine ⟨144793637695784761972814785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193058183594379682630419713 144793637695784761972814785)
  ·
    refine ⟨108595228271838571479611089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144793637695784761972814785 108595228271838571479611089)
    ·
      refine ⟨81446421203878928609708317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108595228271838571479611089 81446421203878928609708317)
      ·
        refine ⟨30542407951454598228640619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81446421203878928609708317 30542407951454598228640619)
        ·
          refine ⟨45813611927181897342960929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30542407951454598228640619 45813611927181897342960929)
          ·
            refine ⟨34360208945386423007220697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45813611927181897342960929 34360208945386423007220697)
            ·
              refine ⟨25770156709039817255415523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34360208945386423007220697 25770156709039817255415523)
              ·
                refine ⟨38655235063559725883123285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25770156709039817255415523 38655235063559725883123285)
                ·
                  refine ⟨452991035901090537692851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38655235063559725883123285 452991035901090537692851)
                  ·
                    rfl

theorem cell23_7939772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_7939772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939772 prefixEnd_7939772 := by exact prefixLift 7939772
  have htrace : WordTrace (prefixWord ++ tailWord_7939772) baseStart_7939772 baseEnd_7939772 := by
    simpa [prefixWord, tailWord_7939772, baseEnd_7939772] using wordTrace_append hprefix tailTrace_7939772
  have hstable : (prefixWord ++ tailWord_7939772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939772).length < 2 ^ (prefixWord ++ tailWord_7939772).sum := by decide
  have hdescent : baseEnd_7939772 < baseStart_7939772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939799 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_7939799 : Nat := 118140960795 + 7939799 * 2 ^ 59
def prefixEnd_7939799 : Nat := 4983230072969 + 3 ^ 40 * 7939799 * 2
def baseEnd_7939799 : Nat := 4076933187087486233598035

theorem tailTrace_7939799 : CollatzResearch.WordTrace tailWord_7939799 prefixEnd_7939799 4076933187087486233598035 := by
  unfold tailWord_7939799
  simp only [CollatzResearch.WordTrace]
  refine ⟨289588260162471707556862451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193058840108314471704574967 289588260162471707556862451)
  ·
    refine ⟨434382390243707561335293677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289588260162471707556862451 434382390243707561335293677)
    ·
      refine ⟨162893396341390335500735129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434382390243707561335293677 162893396341390335500735129)
      ·
        refine ⟨122170047256042751625551347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162893396341390335500735129 122170047256042751625551347)
        ·
          refine ⟨183255070884064127438327021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122170047256042751625551347 183255070884064127438327021)
          ·
            refine ⟨68720651581524047789372633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183255070884064127438327021 68720651581524047789372633)
            ·
              refine ⟨51540488686143035842029475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68720651581524047789372633 51540488686143035842029475)
              ·
                refine ⟨77310733029214553763044213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51540488686143035842029475 77310733029214553763044213)
                ·
                  refine ⟨7247881221488864415285395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77310733029214553763044213 7247881221488864415285395)
                  ·
                    refine ⟨10871821832233296622928093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7247881221488864415285395 10871821832233296622928093)
                    ·
                      refine ⟨4076933187087486233598035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10871821832233296622928093 4076933187087486233598035)
                      ·
                        rfl

theorem cell23_7939799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_7939799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939799 prefixEnd_7939799 := by exact prefixLift 7939799
  have htrace : WordTrace (prefixWord ++ tailWord_7939799) baseStart_7939799 baseEnd_7939799 := by
    simpa [prefixWord, tailWord_7939799, baseEnd_7939799] using wordTrace_append hprefix tailTrace_7939799
  have hstable : (prefixWord ++ tailWord_7939799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939799).length < 2 ^ (prefixWord ++ tailWord_7939799).sum := by decide
  have hdescent : baseEnd_7939799 < baseStart_7939799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939826 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_7939826 : Nat := 118140960795 + 7939826 * 2 ^ 59
def prefixEnd_7939826 : Nat := 4983230072969 + 3 ^ 40 * 7939826 * 2
def baseEnd_7939826 : Nat := 4076947051065157627960411

theorem tailTrace_7939826 : CollatzResearch.WordTrace tailWord_7939826 prefixEnd_7939826 4076947051065157627960411 := by
  unfold tailWord_7939826
  simp only [CollatzResearch.WordTrace]
  refine ⟨72397311233343472792023833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193059496622249260778730221 72397311233343472792023833)
  ·
    refine ⟨54297983425007604594017875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72397311233343472792023833 54297983425007604594017875)
    ·
      refine ⟨81446975137511406891026813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54297983425007604594017875 81446975137511406891026813)
      ·
        refine ⟨30542615676566777584135055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81446975137511406891026813 30542615676566777584135055)
        ·
          refine ⟨45813923514850166376202583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30542615676566777584135055 45813923514850166376202583)
          ·
            refine ⟨68720885272275249564303875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45813923514850166376202583 68720885272275249564303875)
            ·
              refine ⟨103081327908412874346455813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68720885272275249564303875 103081327908412874346455813)
              ·
                refine ⟨19327748982827413939960465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103081327908412874346455813 19327748982827413939960465)
                ·
                  refine ⟨14495811737120560454970349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19327748982827413939960465 14495811737120560454970349)
                  ·
                    refine ⟨5435929401420210170613881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14495811737120560454970349 5435929401420210170613881)
                    ·
                      refine ⟨4076947051065157627960411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435929401420210170613881 4076947051065157627960411)
                      ·
                        rfl

theorem cell23_7939826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_7939826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939826 prefixEnd_7939826 := by exact prefixLift 7939826
  have htrace : WordTrace (prefixWord ++ tailWord_7939826) baseStart_7939826 baseEnd_7939826 := by
    simpa [prefixWord, tailWord_7939826, baseEnd_7939826] using wordTrace_append hprefix tailTrace_7939826
  have hstable : (prefixWord ++ tailWord_7939826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939826).length < 2 ^ (prefixWord ++ tailWord_7939826).sum := by decide
  have hdescent : baseEnd_7939826 < baseStart_7939826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939852 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_7939852 : Nat := 118140960795 + 7939852 * 2 ^ 59
def prefixEnd_7939852 : Nat := 4983230072969 + 3 ^ 40 * 7939852 * 2
def baseEnd_7939852 : Nat := 4076960401562174526235291

theorem tailTrace_7939852 : CollatzResearch.WordTrace tailWord_7939852 prefixEnd_7939852 4076960401562174526235291 := by
  unfold tailWord_7939852
  simp only [CollatzResearch.WordTrace]
  refine ⟨144795096615639848804270905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193060128820853131739027873 144795096615639848804270905)
  ·
    refine ⟨108596322461729886603203179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144795096615639848804270905 108596322461729886603203179)
    ·
      refine ⟨162894483692594829904804769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108596322461729886603203179 162894483692594829904804769)
      ·
        refine ⟨122170862769446122428603577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162894483692594829904804769 122170862769446122428603577)
        ·
          refine ⟨91628147077084591821452683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122170862769446122428603577 91628147077084591821452683)
          ·
            refine ⟨137442220615626887732179025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91628147077084591821452683 137442220615626887732179025)
            ·
              refine ⟨103081665461720165799134269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137442220615626887732179025 103081665461720165799134269)
              ·
                refine ⟨38655624548145062174675351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103081665461720165799134269 38655624548145062174675351)
                ·
                  refine ⟨57983436822217593262013027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38655624548145062174675351 57983436822217593262013027)
                  ·
                    refine ⟨86975155233326389893019541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57983436822217593262013027 86975155233326389893019541)
                    ·
                      refine ⟨4076960401562174526235291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86975155233326389893019541 4076960401562174526235291)
                      ·
                        rfl

theorem cell23_7939852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_7939852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939852 prefixEnd_7939852 := by exact prefixLift 7939852
  have htrace : WordTrace (prefixWord ++ tailWord_7939852) baseStart_7939852 baseEnd_7939852 := by
    simpa [prefixWord, tailWord_7939852, baseEnd_7939852] using wordTrace_append hprefix tailTrace_7939852
  have hstable : (prefixWord ++ tailWord_7939852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939852).length < 2 ^ (prefixWord ++ tailWord_7939852).sum := by decide
  have hdescent : baseEnd_7939852 < baseStart_7939852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939870 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7939870 : Nat := 118140960795 + 7939870 * 2 ^ 59
def prefixEnd_7939870 : Nat := 4983230072969 + 3 ^ 40 * 7939870 * 2
def baseEnd_7939870 : Nat := 1358989881404651818603403

theorem tailTrace_7939870 : CollatzResearch.WordTrace tailWord_7939870 prefixEnd_7939870 1358989881404651818603403 := by
  unfold tailWord_7939870
  simp only [CollatzResearch.WordTrace]
  refine ⟨36198856218151810835337133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193060566496809657788464709 36198856218151810835337133)
  ·
    refine ⟨13574571081806929063251425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36198856218151810835337133 13574571081806929063251425)
    ·
      refine ⟨10180928311355196797438569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13574571081806929063251425 10180928311355196797438569)
      ·
        refine ⟨7635696233516397598078927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10180928311355196797438569 7635696233516397598078927)
        ·
          refine ⟨11453544350274596397118391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7635696233516397598078927 11453544350274596397118391)
          ·
            refine ⟨17180316525411894595677587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453544350274596397118391 17180316525411894595677587)
            ·
              refine ⟨25770474788117841893516381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17180316525411894595677587 25770474788117841893516381)
              ·
                refine ⟨9663928045544190710068643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25770474788117841893516381 9663928045544190710068643)
                ·
                  refine ⟨14495892068316286065102965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9663928045544190710068643 14495892068316286065102965)
                  ·
                    refine ⟨1358989881404651818603403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14495892068316286065102965 1358989881404651818603403)
                    ·
                      rfl

theorem cell23_7939870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7939870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939870 prefixEnd_7939870 := by exact prefixLift 7939870
  have htrace : WordTrace (prefixWord ++ tailWord_7939870) baseStart_7939870 baseEnd_7939870 := by
    simpa [prefixWord, tailWord_7939870, baseEnd_7939870] using wordTrace_append hprefix tailTrace_7939870
  have hstable : (prefixWord ++ tailWord_7939870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939870).length < 2 ^ (prefixWord ++ tailWord_7939870).sum := by decide
  have hdescent : baseEnd_7939870 < baseStart_7939870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939873 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_7939873 : Nat := 118140960795 + 7939873 * 2 ^ 59
def prefixEnd_7939873 : Nat := 4983230072969 + 3 ^ 40 * 7939873 * 2
def baseEnd_7939873 : Nat := 4076971184655918944072695

theorem tailTrace_7939873 : CollatzResearch.WordTrace tailWord_7939873 prefixEnd_7939873 4076971184655918944072695 := by
  unfold tailWord_7939873
  simp only [CollatzResearch.WordTrace]
  refine ⟨289590959164203618195056273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193060639442802412130037515 289590959164203618195056273)
  ·
    refine ⟨217193219373152713646292205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289590959164203618195056273 217193219373152713646292205)
    ·
      refine ⟨81447457264932267617359577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217193219373152713646292205 81447457264932267617359577)
      ·
        refine ⟨61085592948699200713019683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81447457264932267617359577 61085592948699200713019683)
        ·
          refine ⟨91628389423048801069529525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61085592948699200713019683 91628389423048801069529525)
          ·
            refine ⟨8590161508410825100268393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91628389423048801069529525 8590161508410825100268393)
            ·
              refine ⟨6442621131308118825201295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8590161508410825100268393 6442621131308118825201295)
              ·
                refine ⟨9663931696962178237801943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442621131308118825201295 9663931696962178237801943)
                ·
                  refine ⟨14495897545443267356702915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9663931696962178237801943 14495897545443267356702915)
                  ·
                    refine ⟨21743846318164901035054373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14495897545443267356702915 21743846318164901035054373)
                    ·
                      refine ⟨4076971184655918944072695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21743846318164901035054373 4076971184655918944072695)
                      ·
                        rfl

theorem cell23_7939873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_7939873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939873 prefixEnd_7939873 := by exact prefixLift 7939873
  have htrace : WordTrace (prefixWord ++ tailWord_7939873) baseStart_7939873 baseEnd_7939873 := by
    simpa [prefixWord, tailWord_7939873, baseEnd_7939873] using wordTrace_append hprefix tailTrace_7939873
  have hstable : (prefixWord ++ tailWord_7939873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939873).length < 2 ^ (prefixWord ++ tailWord_7939873).sum := by decide
  have hdescent : baseEnd_7939873 < baseStart_7939873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939890 : List Nat := [3, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_7939890 : Nat := 118140960795 + 7939890 * 2 ^ 59
def prefixEnd_7939890 : Nat := 4983230072969 + 3 ^ 40 * 7939890 * 2
def baseEnd_7939890 : Nat := 4076979913827045377560117

theorem tailTrace_7939890 : CollatzResearch.WordTrace tailWord_7939890 prefixEnd_7939890 4076979913827045377560117 := by
  unfold tailWord_7939890
  simp only [CollatzResearch.WordTrace]
  refine ⟨72397894801285507524606281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193061052803428020065616749 72397894801285507524606281)
  ·
    refine ⟨54298421100964130643454711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72397894801285507524606281 54298421100964130643454711)
    ·
      refine ⟨81447631651446195965182067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54298421100964130643454711 81447631651446195965182067)
      ·
        refine ⟨122171447477169293947773101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81447631651446195965182067 122171447477169293947773101)
        ·
          refine ⟨45814292803938485230414913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122171447477169293947773101 45814292803938485230414913)
          ·
            refine ⟨34360719602953863922811185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45814292803938485230414913 34360719602953863922811185)
            ·
              refine ⟨25770539702215397942108389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34360719602953863922811185 25770539702215397942108389)
              ·
                refine ⟨4831976194165387114145323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25770539702215397942108389 4831976194165387114145323)
                ·
                  refine ⟨7247964291248080671217985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831976194165387114145323 7247964291248080671217985)
                  ·
                    refine ⟨5435973218436060503413489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247964291248080671217985 5435973218436060503413489)
                    ·
                      refine ⟨4076979913827045377560117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5435973218436060503413489 4076979913827045377560117)
                      ·
                        rfl

theorem cell23_7939890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_7939890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939890 prefixEnd_7939890 := by exact prefixLift 7939890
  have htrace : WordTrace (prefixWord ++ tailWord_7939890) baseStart_7939890 baseEnd_7939890 := by
    simpa [prefixWord, tailWord_7939890, baseEnd_7939890] using wordTrace_append hprefix tailTrace_7939890
  have hstable : (prefixWord ++ tailWord_7939890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939890).length < 2 ^ (prefixWord ++ tailWord_7939890).sum := by decide
  have hdescent : baseEnd_7939890 < baseStart_7939890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939903 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 1, 2, 4]
def baseStart_7939903 : Nat := 118140960795 + 7939903 * 2 ^ 59
def prefixEnd_7939903 : Nat := 4983230072969 + 3 ^ 40 * 7939903 * 2
def baseEnd_7939903 : Nat := 4076986589075553826697557

theorem tailTrace_7939903 : CollatzResearch.WordTrace tailWord_7939903 prefixEnd_7939903 4076986589075553826697557 := by
  unfold tailWord_7939903
  simp only [CollatzResearch.WordTrace]
  refine ⟨289592053354094933318648363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193061368902729955545765575 289592053354094933318648363)
  ·
    refine ⟨434388080031142399977972545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289592053354094933318648363 434388080031142399977972545)
    ·
      refine ⟨325791060023356799983479409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434388080031142399977972545 325791060023356799983479409)
      ·
        refine ⟨244343295017517599987609557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325791060023356799983479409 244343295017517599987609557)
        ·
          refine ⟨5726795976973068749709599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 244343295017517599987609557 5726795976973068749709599)
          ·
            refine ⟨8590193965459603124564399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726795976973068749709599 8590193965459603124564399)
            ·
              refine ⟨12885290948189404686846599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590193965459603124564399 12885290948189404686846599)
              ·
                refine ⟨19327936422284107030269899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12885290948189404686846599 19327936422284107030269899)
                ·
                  refine ⟨28991904633426160545404849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19327936422284107030269899 28991904633426160545404849)
                  ·
                    refine ⟨21743928475069620409053637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28991904633426160545404849 21743928475069620409053637)
                    ·
                      refine ⟨4076986589075553826697557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21743928475069620409053637 4076986589075553826697557)
                      ·
                        rfl

theorem cell23_7939903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_7939903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939903 prefixEnd_7939903 := by exact prefixLift 7939903
  have htrace : WordTrace (prefixWord ++ tailWord_7939903) baseStart_7939903 baseEnd_7939903 := by
    simpa [prefixWord, tailWord_7939903, baseEnd_7939903] using wordTrace_append hprefix tailTrace_7939903
  have hstable : (prefixWord ++ tailWord_7939903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939903).length < 2 ^ (prefixWord ++ tailWord_7939903).sum := by decide
  have hdescent : baseEnd_7939903 < baseStart_7939903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939910 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7939910 : Nat := 118140960795 + 7939910 * 2 ^ 59
def prefixEnd_7939910 : Nat := 4983230072969 + 3 ^ 40 * 7939910 * 2
def baseEnd_7939910 : Nat := 4076990183440135299310025

theorem tailTrace_7939910 : CollatzResearch.WordTrace tailWord_7939910 prefixEnd_7939910 4076990183440135299310025 := by
  unfold tailWord_7939910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049759645783424172317287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193061539110046382342768789 9049759645783424172317287)
  ·
    refine ⟨13574639468675136258475931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049759645783424172317287 13574639468675136258475931)
    ·
      refine ⟨20361959203012704387713897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13574639468675136258475931 20361959203012704387713897)
      ·
        refine ⟨15271469402259528290785423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20361959203012704387713897 15271469402259528290785423)
        ·
          refine ⟨22907204103389292436178135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15271469402259528290785423 22907204103389292436178135)
          ·
            refine ⟨34360806155083938654267203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22907204103389292436178135 34360806155083938654267203)
            ·
              refine ⟨51541209232625907981400805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34360806155083938654267203 51541209232625907981400805)
              ·
                refine ⟨9663976731117357746512651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51541209232625907981400805 9663976731117357746512651)
                ·
                  refine ⟨14495965096676036619768977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9663976731117357746512651 14495965096676036619768977)
                  ·
                    refine ⟨10871973822507027464826733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14495965096676036619768977 10871973822507027464826733)
                    ·
                      refine ⟨4076990183440135299310025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10871973822507027464826733 4076990183440135299310025)
                      ·
                        rfl

theorem cell23_7939910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7939910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939910 prefixEnd_7939910 := by exact prefixLift 7939910
  have htrace : WordTrace (prefixWord ++ tailWord_7939910) baseStart_7939910 baseEnd_7939910 := by
    simpa [prefixWord, tailWord_7939910, baseEnd_7939910] using wordTrace_append hprefix tailTrace_7939910
  have hstable : (prefixWord ++ tailWord_7939910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939910).length < 2 ^ (prefixWord ++ tailWord_7939910).sum := by decide
  have hdescent : baseEnd_7939910 < baseStart_7939910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939979 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 3]
def baseStart_7939979 : Nat := 118140960795 + 7939979 * 2 ^ 59
def prefixEnd_7939979 : Nat := 4983230072969 + 3 ^ 40 * 7939979 * 2
def baseEnd_7939979 : Nat := 4077025613605295529347207

theorem tailTrace_7939979 : CollatzResearch.WordTrace tailWord_7939979 prefixEnd_7939979 4077025613605295529347207 := by
  unfold tailWord_7939979
  simp only [CollatzResearch.WordTrace]
  refine ⟨289594825301819598298414991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193063216867879732198943327 289594825301819598298414991)
  ·
    refine ⟨434392237952729397447622487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289594825301819598298414991 434392237952729397447622487)
    ·
      refine ⟨651588356929094096171433731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434392237952729397447622487 651588356929094096171433731)
      ·
        refine ⟨977382535393641144257150597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651588356929094096171433731 977382535393641144257150597)
        ·
          refine ⟨183259225386307714548215737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 977382535393641144257150597 183259225386307714548215737)
          ·
            refine ⟨137444419039730785911161803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183259225386307714548215737 137444419039730785911161803)
            ·
              refine ⟨206166628559596178866742705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137444419039730785911161803 206166628559596178866742705)
              ·
                refine ⟨154624971419697134150057029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206166628559596178866742705 154624971419697134150057029)
                ·
                  refine ⟨28992182141193212653135693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154624971419697134150057029 28992182141193212653135693)
                  ·
                    refine ⟨10872068302947454744925885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28992182141193212653135693 10872068302947454744925885)
                    ·
                      refine ⟨4077025613605295529347207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10872068302947454744925885 4077025613605295529347207)
                      ·
                        rfl

theorem cell23_7939979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 3].length) (baseStart_7939979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939979 prefixEnd_7939979 := by exact prefixLift 7939979
  have htrace : WordTrace (prefixWord ++ tailWord_7939979) baseStart_7939979 baseEnd_7939979 := by
    simpa [prefixWord, tailWord_7939979, baseEnd_7939979] using wordTrace_append hprefix tailTrace_7939979
  have hstable : (prefixWord ++ tailWord_7939979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939979).length < 2 ^ (prefixWord ++ tailWord_7939979).sum := by decide
  have hdescent : baseEnd_7939979 < baseStart_7939979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940014 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7940014 : Nat := 118140960795 + 7940014 * 2 ^ 59
def prefixEnd_7940014 : Nat := 4983230072969 + 3 ^ 40 * 7940014 * 2
def baseEnd_7940014 : Nat := 4077043585428202892409547

theorem tailTrace_7940014 : CollatzResearch.WordTrace tailWord_7940014 prefixEnd_7940014 4077043585428202892409547 := by
  unfold tailWord_7940014
  simp only [CollatzResearch.WordTrace]
  refine ⟨36199512732086599909492387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193064067904461866183959397 36199512732086599909492387)
  ·
    refine ⟨54299269098129899864238581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36199512732086599909492387 54299269098129899864238581)
    ·
      refine ⟨5090556477949678112272367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54299269098129899864238581 5090556477949678112272367)
      ·
        refine ⟨7635834716924517168408551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5090556477949678112272367 7635834716924517168408551)
        ·
          refine ⟨11453752075386775752612827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7635834716924517168408551 11453752075386775752612827)
          ·
            refine ⟨17180628113080163628919241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453752075386775752612827 17180628113080163628919241)
            ·
              refine ⟨12885471084810122721689431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17180628113080163628919241 12885471084810122721689431)
              ·
                refine ⟨19328206627215184082534147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12885471084810122721689431 19328206627215184082534147)
                ·
                  refine ⟨28992309940822776123801221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19328206627215184082534147 28992309940822776123801221)
                  ·
                    refine ⟨5436058113904270523212729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28992309940822776123801221 5436058113904270523212729)
                    ·
                      refine ⟨4077043585428202892409547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436058113904270523212729 4077043585428202892409547)
                      ·
                        rfl

theorem cell23_7940014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7940014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940014 prefixEnd_7940014 := by exact prefixLift 7940014
  have htrace : WordTrace (prefixWord ++ tailWord_7940014) baseStart_7940014 baseEnd_7940014 := by
    simpa [prefixWord, tailWord_7940014, baseEnd_7940014] using wordTrace_append hprefix tailTrace_7940014
  have hstable : (prefixWord ++ tailWord_7940014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940014).length < 2 ^ (prefixWord ++ tailWord_7940014).sum := by decide
  have hdescent : baseEnd_7940014 < baseStart_7940014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940019 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4]
def baseStart_7940019 : Nat := 118140960795 + 7940019 * 2 ^ 59
def prefixEnd_7940019 : Nat := 4983230072969 + 3 ^ 40 * 7940019 * 2
def baseEnd_7940019 : Nat := 4077046152831475372847023

theorem tailTrace_7940019 : CollatzResearch.WordTrace tailWord_7940019 prefixEnd_7940019 4077046152831475372847023 := by
  unfold tailWord_7940019
  simp only [CollatzResearch.WordTrace]
  refine ⟨289596284221674685129871111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193064189481116456753247407 289596284221674685129871111)
  ·
    refine ⟨434394426332512027694806667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289596284221674685129871111 434394426332512027694806667)
    ·
      refine ⟨651591639498768041542210001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434394426332512027694806667 651591639498768041542210001)
      ·
        refine ⟨488693729624076031156657501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651591639498768041542210001 488693729624076031156657501)
        ·
          refine ⟨183260148609028511683746563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488693729624076031156657501 183260148609028511683746563)
          ·
            refine ⟨274890222913542767525619845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183260148609028511683746563 274890222913542767525619845)
            ·
              refine ⟨51541916796289268911053721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274890222913542767525619845 51541916796289268911053721)
              ·
                refine ⟨38656437597216951683290291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51541916796289268911053721 38656437597216951683290291)
                ·
                  refine ⟨57984656395825427524935437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38656437597216951683290291 57984656395825427524935437)
                  ·
                    refine ⟨21744246148434535321850789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57984656395825427524935437 21744246148434535321850789)
                    ·
                      refine ⟨4077046152831475372847023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21744246148434535321850789 4077046152831475372847023)
                      ·
                        rfl

theorem cell23_7940019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_7940019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940019 prefixEnd_7940019 := by exact prefixLift 7940019
  have htrace : WordTrace (prefixWord ++ tailWord_7940019) baseStart_7940019 baseEnd_7940019 := by
    simpa [prefixWord, tailWord_7940019, baseEnd_7940019] using wordTrace_append hprefix tailTrace_7940019
  have hstable : (prefixWord ++ tailWord_7940019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940019).length < 2 ^ (prefixWord ++ tailWord_7940019).sum := by decide
  have hdescent : baseEnd_7940019 < baseStart_7940019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940046 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_7940046 : Nat := 118140960795 + 7940046 * 2 ^ 59
def prefixEnd_7940046 : Nat := 4983230072969 + 3 ^ 40 * 7940046 * 2
def baseEnd_7940046 : Nat := 1359020005603048922403133

theorem tailTrace_7940046 : CollatzResearch.WordTrace tailWord_7940046 prefixEnd_7940046 1359020005603048922403133 := by
  unfold tailWord_7940046
  simp only [CollatzResearch.WordTrace]
  refine ⟨36199658624072108592637999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193064845995051245827402661 36199658624072108592637999)
  ·
    refine ⟨54299487936108162888956999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36199658624072108592637999 54299487936108162888956999)
    ·
      refine ⟨81449231904162244333435499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54299487936108162888956999 81449231904162244333435499)
      ·
        refine ⟨122173847856243366500153249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81449231904162244333435499 122173847856243366500153249)
        ·
          refine ⟨91630385892182524875114937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122173847856243366500153249 91630385892182524875114937)
          ·
            refine ⟨68722789419136893656336203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91630385892182524875114937 68722789419136893656336203)
            ·
              refine ⟨103084184128705340484504305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68722789419136893656336203 103084184128705340484504305)
              ·
                refine ⟨77313138096529005363378229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103084184128705340484504305 77313138096529005363378229)
                ·
                  refine ⟨7248106696549594252816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77313138096529005363378229 7248106696549594252816709)
                  ·
                    refine ⟨1359020005603048922403133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7248106696549594252816709 1359020005603048922403133)
                    ·
                      rfl

theorem cell23_7940046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_7940046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940046 prefixEnd_7940046 := by exact prefixLift 7940046
  have htrace : WordTrace (prefixWord ++ tailWord_7940046) baseStart_7940046 baseEnd_7940046 := by
    simpa [prefixWord, tailWord_7940046, baseEnd_7940046] using wordTrace_append hprefix tailTrace_7940046
  have hstable : (prefixWord ++ tailWord_7940046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940046).length < 2 ^ (prefixWord ++ tailWord_7940046).sum := by decide
  have hdescent : baseEnd_7940046 < baseStart_7940046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940053 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7940053 : Nat := 118140960795 + 7940053 * 2 ^ 59
def prefixEnd_7940053 : Nat := 4983230072969 + 3 ^ 40 * 7940053 * 2
def baseEnd_7940053 : Nat := 4077063611173728239821867

theorem tailTrace_7940053 : CollatzResearch.WordTrace tailWord_7940053 prefixEnd_7940053 4077063611173728239821867 := by
  unfold tailWord_7940053
  simp only [CollatzResearch.WordTrace]
  refine ⟨289597524303551508936608813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193065016202367672624405875 289597524303551508936608813)
  ·
    refine ⟨108599071613831815851228305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289597524303551508936608813 108599071613831815851228305)
    ·
      refine ⟨81449303710373861888421229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108599071613831815851228305 81449303710373861888421229)
      ·
        refine ⟨30543488891390198208157961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81449303710373861888421229 30543488891390198208157961)
        ·
          refine ⟨22907616668542648656118471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30543488891390198208157961 22907616668542648656118471)
          ·
            refine ⟨34361425002813972984177707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22907616668542648656118471 34361425002813972984177707)
            ·
              refine ⟨51542137504220959476266561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34361425002813972984177707 51542137504220959476266561)
              ·
                refine ⟨38656603128165719607199921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51542137504220959476266561 38656603128165719607199921)
                ·
                  refine ⟨28992452346124289705399941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38656603128165719607199921 28992452346124289705399941)
                  ·
                    refine ⟨5436084814898304319762489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28992452346124289705399941 5436084814898304319762489)
                    ·
                      refine ⟨4077063611173728239821867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436084814898304319762489 4077063611173728239821867)
                      ·
                        rfl

theorem cell23_7940053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7940053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940053 prefixEnd_7940053 := by exact prefixLift 7940053
  have htrace : WordTrace (prefixWord ++ tailWord_7940053) baseStart_7940053 baseEnd_7940053 := by
    simpa [prefixWord, tailWord_7940053, baseEnd_7940053] using wordTrace_append hprefix tailTrace_7940053
  have hstable : (prefixWord ++ tailWord_7940053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940053).length < 2 ^ (prefixWord ++ tailWord_7940053).sum := by decide
  have hdescent : baseEnd_7940053 < baseStart_7940053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940056 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_7940056 : Nat := 118140960795 + 7940056 * 2 ^ 59
def prefixEnd_7940056 : Nat := 4983230072969 + 3 ^ 40 * 7940056 * 2
def baseEnd_7940056 : Nat := 4077065151615691728084353

theorem tailTrace_7940056 : CollatzResearch.WordTrace tailWord_7940056 prefixEnd_7940056 4077065151615691728084353 := by
  unfold tailWord_7940056
  simp only [CollatzResearch.WordTrace]
  refine ⟨144798816861270320224484011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193065089148360426965978681 144798816861270320224484011)
  ·
    refine ⟨217198225291905480336726017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144798816861270320224484011 217198225291905480336726017)
    ·
      refine ⟨162898668968929110252544513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217198225291905480336726017 162898668968929110252544513)
      ·
        refine ⟨122174001726696832689408385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162898668968929110252544513 122174001726696832689408385)
        ·
          refine ⟨91630501295022624517056289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122174001726696832689408385 91630501295022624517056289)
          ·
            refine ⟨68722875971266968387792217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91630501295022624517056289 68722875971266968387792217)
            ·
              refine ⟨51542156978450226290844163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68722875971266968387792217 51542156978450226290844163)
              ·
                refine ⟨77313235467675339436266245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51542156978450226290844163 77313235467675339436266245)
                ·
                  refine ⟨14496231650189126144299921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77313235467675339436266245 14496231650189126144299921)
                  ·
                    refine ⟨10872173737641844608224941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14496231650189126144299921 10872173737641844608224941)
                    ·
                      refine ⟨4077065151615691728084353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10872173737641844608224941 4077065151615691728084353)
                      ·
                        rfl

theorem cell23_7940056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_7940056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940056 prefixEnd_7940056 := by exact prefixLift 7940056
  have htrace : WordTrace (prefixWord ++ tailWord_7940056) baseStart_7940056 baseEnd_7940056 := by
    simpa [prefixWord, tailWord_7940056, baseEnd_7940056] using wordTrace_append hprefix tailTrace_7940056
  have hstable : (prefixWord ++ tailWord_7940056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940056).length < 2 ^ (prefixWord ++ tailWord_7940056).sum := by decide
  have hdescent : baseEnd_7940056 < baseStart_7940056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940063 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 3, 4]
def baseStart_7940063 : Nat := 118140960795 + 7940063 * 2 ^ 59
def prefixEnd_7940063 : Nat := 4983230072969 + 3 ^ 40 * 7940063 * 2
def baseEnd_7940063 : Nat := 1359022915326757733565607

theorem tailTrace_7940063 : CollatzResearch.WordTrace tailWord_7940063 prefixEnd_7940063 1359022915326757733565607 := by
  unfold tailWord_7940063
  simp only [CollatzResearch.WordTrace]
  refine ⟨289597889033515280644472843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193065259355676853762981895 289597889033515280644472843)
  ·
    refine ⟨434396833550272920966709265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289597889033515280644472843 434396833550272920966709265)
    ·
      refine ⟨325797625162704690725031949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434396833550272920966709265 325797625162704690725031949)
      ·
        refine ⟨122174109436014259021886981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325797625162704690725031949 122174109436014259021886981)
        ·
          refine ⟨22907645519252673566603809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122174109436014259021886981 22907645519252673566603809)
          ·
            refine ⟨17180734139439505174952857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22907645519252673566603809 17180734139439505174952857)
            ·
              refine ⟨12885550604579628881214643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17180734139439505174952857 12885550604579628881214643)
              ·
                refine ⟨19328325906869443321821965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12885550604579628881214643 19328325906869443321821965)
                ·
                  refine ⟨7248122215076041245683237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19328325906869443321821965 7248122215076041245683237)
                  ·
                    refine ⟨1359022915326757733565607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7248122215076041245683237 1359022915326757733565607)
                    ·
                      rfl

theorem cell23_7940063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_7940063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940063 prefixEnd_7940063 := by exact prefixLift 7940063
  have htrace : WordTrace (prefixWord ++ tailWord_7940063) baseStart_7940063 baseEnd_7940063 := by
    simpa [prefixWord, tailWord_7940063, baseEnd_7940063] using wordTrace_append hprefix tailTrace_7940063
  have hstable : (prefixWord ++ tailWord_7940063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940063).length < 2 ^ (prefixWord ++ tailWord_7940063).sum := by decide
  have hdescent : baseEnd_7940063 < baseStart_7940063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940079 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_7940079 : Nat := 118140960795 + 7940079 * 2 ^ 59
def prefixEnd_7940079 : Nat := 4983230072969 + 3 ^ 40 * 7940079 * 2
def baseEnd_7940079 : Nat := 4077076961670745138096747

theorem tailTrace_7940079 : CollatzResearch.WordTrace tailWord_7940079 prefixEnd_7940079 4077076961670745138096747 := by
  unfold tailWord_7940079
  simp only [CollatzResearch.WordTrace]
  refine ⟨289598472601457315377055291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193065648400971543584703527 289598472601457315377055291)
  ·
    refine ⟨434397708902185973065582937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289598472601457315377055291 434397708902185973065582937)
    ·
      refine ⟨325798281676639479799187203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434397708902185973065582937 325798281676639479799187203)
      ·
        refine ⟨488697422514959219698780805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325798281676639479799187203 488697422514959219698780805)
        ·
          refine ⟨91630766721554853693521401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488697422514959219698780805 91630766721554853693521401)
          ·
            refine ⟨68723075041166140270141051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91630766721554853693521401 68723075041166140270141051)
            ·
              refine ⟨103084612561749210405211577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68723075041166140270141051 103084612561749210405211577)
              ·
                refine ⟨77313459421311907803908683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103084612561749210405211577 77313459421311907803908683)
                ·
                  refine ⟨115970189131967861705863025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77313459421311907803908683 115970189131967861705863025)
                  ·
                    refine ⟨86977641848975896279397269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115970189131967861705863025 86977641848975896279397269)
                    ·
                      refine ⟨4077076961670745138096747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86977641848975896279397269 4077076961670745138096747)
                      ·
                        rfl

theorem cell23_7940079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_7940079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940079 prefixEnd_7940079 := by exact prefixLift 7940079
  have htrace : WordTrace (prefixWord ++ tailWord_7940079) baseStart_7940079 baseEnd_7940079 := by
    simpa [prefixWord, tailWord_7940079, baseEnd_7940079] using wordTrace_append hprefix tailTrace_7940079
  have hstable : (prefixWord ++ tailWord_7940079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940079).length < 2 ^ (prefixWord ++ tailWord_7940079).sum := by decide
  have hdescent : baseEnd_7940079 < baseStart_7940079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940153 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 1, 6]
def baseStart_7940153 : Nat := 118140960795 + 7940153 * 2 ^ 59
def prefixEnd_7940153 : Nat := 4983230072969 + 3 ^ 40 * 7940153 * 2
def baseEnd_7940153 : Nat := 1359038319746392616190469

theorem tailTrace_7940153 : CollatzResearch.WordTrace tailWord_7940153 prefixEnd_7940153 1359038319746392616190469 := by
  unfold tailWord_7940153
  simp only [CollatzResearch.WordTrace]
  refine ⟨289601171603189226015249113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193067447735459484010166075 289601171603189226015249113)
  ·
    refine ⟨217200878702391919511436835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289601171603189226015249113 217200878702391919511436835)
    ·
      refine ⟨325801318053587879267155253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217200878702391919511436835 325801318053587879267155253)
      ·
        refine ⟨30543873567523863681295805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325801318053587879267155253 30543873567523863681295805)
        ·
          refine ⟨11453952587821448880485927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30543873567523863681295805 11453952587821448880485927)
          ·
            refine ⟨17180928881732173320728891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453952587821448880485927 17180928881732173320728891)
            ·
              refine ⟨25771393322598259981093337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17180928881732173320728891 25771393322598259981093337)
              ·
                refine ⟨19328544991948694985820003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25771393322598259981093337 19328544991948694985820003)
                ·
                  refine ⟨28992817487923042478730005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19328544991948694985820003 28992817487923042478730005)
                  ·
                    refine ⟨1359038319746392616190469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28992817487923042478730005 1359038319746392616190469)
                    ·
                      rfl

theorem cell23_7940153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_7940153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940153 prefixEnd_7940153 := by exact prefixLift 7940153
  have htrace : WordTrace (prefixWord ++ tailWord_7940153) baseStart_7940153 baseEnd_7940153 := by
    simpa [prefixWord, tailWord_7940153, baseEnd_7940153] using wordTrace_append hprefix tailTrace_7940153
  have hstable : (prefixWord ++ tailWord_7940153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940153).length < 2 ^ (prefixWord ++ tailWord_7940153).sum := by decide
  have hdescent : baseEnd_7940153 < baseStart_7940153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940160 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 1, 1, 4]
def baseStart_7940160 : Nat := 118140960795 + 7940160 * 2 ^ 59
def prefixEnd_7940160 : Nat := 4983230072969 + 3 ^ 40 * 7940160 * 2
def baseEnd_7940160 : Nat := 4077118553603759321183875

theorem tailTrace_7940160 : CollatzResearch.WordTrace tailWord_7940160 prefixEnd_7940160 4077118553603759321183875 := by
  unfold tailWord_7940160
  simp only [CollatzResearch.WordTrace]
  refine ⟨144800713457081933105376967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193067617942775910807169289 144800713457081933105376967)
  ·
    refine ⟨217201070185622899658065451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144800713457081933105376967 217201070185622899658065451)
    ·
      refine ⟨325801605278434349487098177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217201070185622899658065451 325801605278434349487098177)
      ·
        refine ⟨244351203958825762115323633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325801605278434349487098177 244351203958825762115323633)
        ·
          refine ⟨183263402969119321586492725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244351203958825762115323633 183263402969119321586492725)
          ·
            refine ⟨17180944028354936398733693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183263402969119321586492725 17180944028354936398733693)
            ·
              refine ⟨6442854010633101149525135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17180944028354936398733693 6442854010633101149525135)
              ·
                refine ⟨9664281015949651724287703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442854010633101149525135 9664281015949651724287703)
                ·
                  refine ⟨14496421523924477586431555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664281015949651724287703 14496421523924477586431555)
                  ·
                    refine ⟨21744632285886716379647333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14496421523924477586431555 21744632285886716379647333)
                    ·
                      refine ⟨4077118553603759321183875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21744632285886716379647333 4077118553603759321183875)
                      ·
                        rfl

theorem cell23_7940160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_7940160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940160 prefixEnd_7940160 := by exact prefixLift 7940160
  have htrace : WordTrace (prefixWord ++ tailWord_7940160) baseStart_7940160 baseEnd_7940160 := by
    simpa [prefixWord, tailWord_7940160, baseEnd_7940160] using wordTrace_append hprefix tailTrace_7940160
  have hstable : (prefixWord ++ tailWord_7940160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940160).length < 2 ^ (prefixWord ++ tailWord_7940160).sum := by decide
  have hdescent : baseEnd_7940160 < baseStart_7940160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940173 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_7940173 : Nat := 118140960795 + 7940173 * 2 ^ 59
def prefixEnd_7940173 : Nat := 4983230072969 + 3 ^ 40 * 7940173 * 2
def baseEnd_7940173 : Nat := 4077125228852267770321315

theorem tailTrace_7940173 : CollatzResearch.WordTrace tailWord_7940173 prefixEnd_7940173 4077125228852267770321315 := by
  unfold tailWord_7940173
  simp only [CollatzResearch.WordTrace]
  refine ⟨289601901063116769430977173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193067934042077846287318115 289601901063116769430977173)
  ·
    refine ⟨13575089112333598567077055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289601901063116769430977173 13575089112333598567077055)
    ·
      refine ⟨20362633668500397850615583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13575089112333598567077055 20362633668500397850615583)
      ·
        refine ⟨30543950502750596775923375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20362633668500397850615583 30543950502750596775923375)
        ·
          refine ⟨45815925754125895163885063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30543950502750596775923375 45815925754125895163885063)
          ·
            refine ⟨68723888631188842745827595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45815925754125895163885063 68723888631188842745827595)
            ·
              refine ⟨103085832946783264118741393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68723888631188842745827595 103085832946783264118741393)
              ·
                refine ⟨77314374710087448089056045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103085832946783264118741393 77314374710087448089056045)
                ·
                  refine ⟨28992890516282793033396017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77314374710087448089056045 28992890516282793033396017)
                  ·
                    refine ⟨21744667887212094775047013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28992890516282793033396017 21744667887212094775047013)
                    ·
                      refine ⟨4077125228852267770321315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21744667887212094775047013 4077125228852267770321315)
                      ·
                        rfl

theorem cell23_7940173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_7940173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940173 prefixEnd_7940173 := by exact prefixLift 7940173
  have htrace : WordTrace (prefixWord ++ tailWord_7940173) baseStart_7940173 baseEnd_7940173 := by
    simpa [prefixWord, tailWord_7940173, baseEnd_7940173] using wordTrace_append hprefix tailTrace_7940173
  have hstable : (prefixWord ++ tailWord_7940173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940173).length < 2 ^ (prefixWord ++ tailWord_7940173).sum := by decide
  have hdescent : baseEnd_7940173 < baseStart_7940173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940193 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_7940193 : Nat := 118140960795 + 7940193 * 2 ^ 59
def prefixEnd_7940193 : Nat := 4983230072969 + 3 ^ 40 * 7940193 * 2
def baseEnd_7940193 : Nat := 4077135498465357692071223

theorem tailTrace_7940193 : CollatzResearch.WordTrace tailWord_7940193 prefixEnd_7940193 4077135498465357692071223 := by
  unfold tailWord_7940193
  simp only [CollatzResearch.WordTrace]
  refine ⟨289602630523044312846705233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193068420348696208564470155 289602630523044312846705233)
  ·
    refine ⟨217201972892283234635028925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289602630523044312846705233 217201972892283234635028925)
    ·
      refine ⟨81450739834606212988135847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217201972892283234635028925 81450739834606212988135847)
      ·
        refine ⟨122176109751909319482203771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81450739834606212988135847 122176109751909319482203771)
        ·
          refine ⟨183264164627863979223305657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122176109751909319482203771 183264164627863979223305657)
          ·
            refine ⟨137448123470897984417479243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183264164627863979223305657 137448123470897984417479243)
            ·
              refine ⟨206172185206346976626218865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137448123470897984417479243 206172185206346976626218865)
              ·
                refine ⟨154629138904760232469664149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206172185206346976626218865 154629138904760232469664149)
                ·
                  refine ⟨7248240886160635897015507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154629138904760232469664149 7248240886160635897015507)
                  ·
                    refine ⟨10872361329240953845523261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7248240886160635897015507 10872361329240953845523261)
                    ·
                      refine ⟨4077135498465357692071223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10872361329240953845523261 4077135498465357692071223)
                      ·
                        rfl

theorem cell23_7940193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_7940193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940193 prefixEnd_7940193 := by exact prefixLift 7940193
  have htrace : WordTrace (prefixWord ++ tailWord_7940193) baseStart_7940193 baseEnd_7940193 := by
    simpa [prefixWord, tailWord_7940193, baseEnd_7940193] using wordTrace_append hprefix tailTrace_7940193
  have hstable : (prefixWord ++ tailWord_7940193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940193).length < 2 ^ (prefixWord ++ tailWord_7940193).sum := by decide
  have hdescent : baseEnd_7940193 < baseStart_7940193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940194 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7940194 : Nat := 118140960795 + 7940194 * 2 ^ 59
def prefixEnd_7940194 : Nat := 4983230072969 + 3 ^ 40 * 7940194 * 2
def baseEnd_7940194 : Nat := 4077136011946012188158719

theorem tailTrace_7940194 : CollatzResearch.WordTrace tailWord_7940194 prefixEnd_7940194 4077136011946012188158719 := by
  unfold tailWord_7940194
  simp only [CollatzResearch.WordTrace]
  refine ⟨72400666749010172504372909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193068444664027126678327757 72400666749010172504372909)
  ·
    refine ⟨27150250030878814689139841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72400666749010172504372909 27150250030878814689139841)
    ·
      refine ⟨20362687523159111016854881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27150250030878814689139841 20362687523159111016854881)
      ·
        refine ⟨15272015642369333262641161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20362687523159111016854881 15272015642369333262641161)
        ·
          refine ⟨11454011731776999946980871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15272015642369333262641161 11454011731776999946980871)
          ·
            refine ⟨17181017597665499920471307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11454011731776999946980871 17181017597665499920471307)
            ·
              refine ⟨25771526396498249880706961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17181017597665499920471307 25771526396498249880706961)
              ·
                refine ⟨19328644797373687410530221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25771526396498249880706961 19328644797373687410530221)
                ·
                  refine ⟨7248241799015132778948833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19328644797373687410530221 7248241799015132778948833)
                  ·
                    refine ⟨5436181349261349584211625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7248241799015132778948833 5436181349261349584211625)
                    ·
                      refine ⟨4077136011946012188158719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436181349261349584211625 4077136011946012188158719)
                      ·
                        rfl

theorem cell23_7940194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7940194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940194 prefixEnd_7940194 := by exact prefixLift 7940194
  have htrace : WordTrace (prefixWord ++ tailWord_7940194) baseStart_7940194 baseEnd_7940194 := by
    simpa [prefixWord, tailWord_7940194, baseEnd_7940194] using wordTrace_append hprefix tailTrace_7940194
  have hstable : (prefixWord ++ tailWord_7940194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940194).length < 2 ^ (prefixWord ++ tailWord_7940194).sum := by decide
  have hdescent : baseEnd_7940194 < baseStart_7940194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940214 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7940214 : Nat := 118140960795 + 7940214 * 2 ^ 59
def prefixEnd_7940214 : Nat := 4983230072969 + 3 ^ 40 * 7940214 * 2
def baseEnd_7940214 : Nat := 4077146281559102109908627

theorem tailTrace_7940214 : CollatzResearch.WordTrace tailWord_7940214 prefixEnd_7940214 4077146281559102109908627 := by
  unfold tailWord_7940214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18100212278498014589576231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193068930970645488955479797 18100212278498014589576231)
  ·
    refine ⟨27150318417747021884364347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18100212278498014589576231 27150318417747021884364347)
    ·
      refine ⟨40725477626620532826546521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27150318417747021884364347 40725477626620532826546521)
      ·
        refine ⟨30544108219965399619909891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40725477626620532826546521 30544108219965399619909891)
        ·
          refine ⟨45816162329948099429864837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30544108219965399619909891 45816162329948099429864837)
          ·
            refine ⟨8590530436865268643099657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45816162329948099429864837 8590530436865268643099657)
            ·
              refine ⟨6442897827648951482324743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8590530436865268643099657 6442897827648951482324743)
              ·
                refine ⟨9664346741473427223487115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442897827648951482324743 9664346741473427223487115)
                ·
                  refine ⟨14496520112210140835230673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664346741473427223487115 14496520112210140835230673)
                  ·
                    refine ⟨10872390084157605626423005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14496520112210140835230673 10872390084157605626423005)
                    ·
                      refine ⟨4077146281559102109908627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10872390084157605626423005 4077146281559102109908627)
                      ·
                        rfl

theorem cell23_7940214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7940214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940214 prefixEnd_7940214 := by exact prefixLift 7940214
  have htrace : WordTrace (prefixWord ++ tailWord_7940214) baseStart_7940214 baseEnd_7940214 := by
    simpa [prefixWord, tailWord_7940214, baseEnd_7940214] using wordTrace_append hprefix tailTrace_7940214
  have hstable : (prefixWord ++ tailWord_7940214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940214).length < 2 ^ (prefixWord ++ tailWord_7940214).sum := by decide
  have hdescent : baseEnd_7940214 < baseStart_7940214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940227 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 3]
def baseStart_7940227 : Nat := 118140960795 + 7940227 * 2 ^ 59
def prefixEnd_7940227 : Nat := 4983230072969 + 3 ^ 40 * 7940227 * 2
def baseEnd_7940227 : Nat := 4077152956807610559046067

theorem tailTrace_7940227 : CollatzResearch.WordTrace tailWord_7940227 prefixEnd_7940227 4077152956807610559046067 := by
  unfold tailWord_7940227
  simp only [CollatzResearch.WordTrace]
  refine ⟨289603870604921136653442935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193069247069947424435628623 289603870604921136653442935)
  ·
    refine ⟨434405805907381704980164403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289603870604921136653442935 434405805907381704980164403)
    ·
      refine ⟨651608708861072557470246605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434405805907381704980164403 651608708861072557470246605)
      ·
        refine ⟨244353265822902209051342477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651608708861072557470246605 244353265822902209051342477)
        ·
          refine ⟨91632474683588328394253429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244353265822902209051342477 91632474683588328394253429)
          ·
            refine ⟨8590544501586405786961259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91632474683588328394253429 8590544501586405786961259)
            ·
              refine ⟨12885816752379608680441889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590544501586405786961259 12885816752379608680441889)
              ·
                refine ⟨9664362564284706510331417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12885816752379608680441889 9664362564284706510331417)
                ·
                  refine ⟨7248271923213529882748563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9664362564284706510331417 7248271923213529882748563)
                  ·
                    refine ⟨10872407884820294824122845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7248271923213529882748563 10872407884820294824122845)
                    ·
                      refine ⟨4077152956807610559046067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10872407884820294824122845 4077152956807610559046067)
                      ·
                        rfl

theorem cell23_7940227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_7940227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940227 prefixEnd_7940227 := by exact prefixLift 7940227
  have htrace : WordTrace (prefixWord ++ tailWord_7940227) baseStart_7940227 baseEnd_7940227 := by
    simpa [prefixWord, tailWord_7940227, baseEnd_7940227] using wordTrace_append hprefix tailTrace_7940227
  have hstable : (prefixWord ++ tailWord_7940227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940227).length < 2 ^ (prefixWord ++ tailWord_7940227).sum := by decide
  have hdescent : baseEnd_7940227 < baseStart_7940227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940236 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_7940236 : Nat := 118140960795 + 7940236 * 2 ^ 59
def prefixEnd_7940236 : Nat := 4983230072969 + 3 ^ 40 * 7940236 * 2
def baseEnd_7940236 : Nat := 4077157578133501023833525

theorem tailTrace_7940236 : CollatzResearch.WordTrace tailWord_7940236 prefixEnd_7940236 4077157578133501023833525 := by
  unfold tailWord_7940236
  simp only [CollatzResearch.WordTrace]
  refine ⟨144802099430944265595260281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193069465907925687460347041 144802099430944265595260281)
  ·
    refine ⟨108601574573208199196445211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144802099430944265595260281 108601574573208199196445211)
    ·
      refine ⟨162902361859812298794667817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108601574573208199196445211 162902361859812298794667817)
      ·
        refine ⟨122176771394859224096000863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162902361859812298794667817 122176771394859224096000863)
        ·
          refine ⟨183265157092288836144001295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122176771394859224096000863 183265157092288836144001295)
          ·
            refine ⟨274897735638433254216001943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183265157092288836144001295 274897735638433254216001943)
            ·
              refine ⟨412346603457649881324002915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274897735638433254216001943 412346603457649881324002915)
              ·
                refine ⟨618519905186474821986004373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412346603457649881324002915 618519905186474821986004373)
                ·
                  refine ⟨28993120555616007280593955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 618519905186474821986004373 28993120555616007280593955)
                  ·
                    refine ⟨43489680833424010920890933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28993120555616007280593955 43489680833424010920890933)
                    ·
                      refine ⟨4077157578133501023833525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43489680833424010920890933 4077157578133501023833525)
                      ·
                        rfl

theorem cell23_7940236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_7940236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940236 prefixEnd_7940236 := by exact prefixLift 7940236
  have htrace : WordTrace (prefixWord ++ tailWord_7940236) baseStart_7940236 baseEnd_7940236 := by
    simpa [prefixWord, tailWord_7940236, baseEnd_7940236] using wordTrace_append hprefix tailTrace_7940236
  have hstable : (prefixWord ++ tailWord_7940236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940236).length < 2 ^ (prefixWord ++ tailWord_7940236).sum := by decide
  have hdescent : baseEnd_7940236 < baseStart_7940236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940244 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7940244 : Nat := 118140960795 + 7940244 * 2 ^ 59
def prefixEnd_7940244 : Nat := 4983230072969 + 3 ^ 40 * 7940244 * 2
def baseEnd_7940244 : Nat := 4077161685978736992533489

theorem tailTrace_7940244 : CollatzResearch.WordTrace tailWord_7940244 prefixEnd_7940244 4077161685978736992533489 := by
  unfold tailWord_7940244
  simp only [CollatzResearch.WordTrace]
  refine ⟨144802245322929774278405893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193069660430573032371207857 144802245322929774278405893)
  ·
    refine ⟨27150420998049332677201105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144802245322929774278405893 27150420998049332677201105)
    ·
      refine ⟨20362815748536999507900829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27150420998049332677201105 20362815748536999507900829)
      ·
        refine ⟨7636055905701374815462811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20362815748536999507900829 7636055905701374815462811)
        ·
          refine ⟨11454083858552062223194217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7636055905701374815462811 11454083858552062223194217)
          ·
            refine ⟨8590562893914046667395663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11454083858552062223194217 8590562893914046667395663)
            ·
              refine ⟨12885844340871070001093495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590562893914046667395663 12885844340871070001093495)
              ·
                refine ⟨19328766511306605001640243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12885844340871070001093495 19328766511306605001640243)
                ·
                  refine ⟨28993149766959907502460365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19328766511306605001640243 28993149766959907502460365)
                  ·
                    refine ⟨10872431162609965313422637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28993149766959907502460365 10872431162609965313422637)
                    ·
                      refine ⟨4077161685978736992533489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10872431162609965313422637 4077161685978736992533489)
                      ·
                        rfl

theorem cell23_7940244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7940244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940244 prefixEnd_7940244 := by exact prefixLift 7940244
  have htrace : WordTrace (prefixWord ++ tailWord_7940244) baseStart_7940244 baseEnd_7940244 := by
    simpa [prefixWord, tailWord_7940244, baseEnd_7940244] using wordTrace_append hprefix tailTrace_7940244
  have hstable : (prefixWord ++ tailWord_7940244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940244).length < 2 ^ (prefixWord ++ tailWord_7940244).sum := by decide
  have hdescent : baseEnd_7940244 < baseStart_7940244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940363 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 6]
def baseStart_7940363 : Nat := 118140960795 + 7940363 * 2 ^ 59
def prefixEnd_7940363 : Nat := 4983230072969 + 3 ^ 40 * 7940363 * 2
def baseEnd_7940363 : Nat := 453024754464069114105049

theorem tailTrace_7940363 : CollatzResearch.WordTrace tailWord_7940363 prefixEnd_7940363 453024754464069114105049 := by
  unfold tailWord_7940363
  simp only [CollatzResearch.WordTrace]
  refine ⟨289608830932428431880393743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193072553954952287920262495 289608830932428431880393743)
  ·
    refine ⟨434413246398642647820590615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289608830932428431880393743 434413246398642647820590615)
    ·
      refine ⟨651619869597963971730885923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434413246398642647820590615 651619869597963971730885923)
      ·
        refine ⟨977429804396945957596328885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651619869597963971730885923 977429804396945957596328885)
        ·
          refine ⟨91634044162213683524655833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 977429804396945957596328885 91634044162213683524655833)
          ·
            refine ⟨68725533121660262643491875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91634044162213683524655833 68725533121660262643491875)
            ·
              refine ⟨103088299682490393965237813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68725533121660262643491875 103088299682490393965237813)
              ·
                refine ⟨9664528095233474434241045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103088299682490393965237813 9664528095233474434241045)
                ·
                  refine ⟨453024754464069114105049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9664528095233474434241045 453024754464069114105049)
                  ·
                    rfl

theorem cell23_7940363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 6].length) (baseStart_7940363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940363 prefixEnd_7940363 := by exact prefixLift 7940363
  have htrace : WordTrace (prefixWord ++ tailWord_7940363) baseStart_7940363 baseEnd_7940363 := by
    simpa [prefixWord, tailWord_7940363, baseEnd_7940363] using wordTrace_append hprefix tailTrace_7940363
  have hstable : (prefixWord ++ tailWord_7940363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940363).length < 2 ^ (prefixWord ++ tailWord_7940363).sum := by decide
  have hdescent : baseEnd_7940363 < baseStart_7940363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940384 : List Nat := [2, 1, 1, 5, 2, 2, 2, 3, 1, 4]
def baseStart_7940384 : Nat := 118140960795 + 7940384 * 2 ^ 59
def prefixEnd_7940384 : Nat := 4983230072969 + 3 ^ 40 * 7940384 * 2
def baseEnd_7940384 : Nat := 1359077857756788814927615

theorem tailTrace_7940384 : CollatzResearch.WordTrace tailWord_7940384 prefixEnd_7940384 1359077857756788814927615 := by
  unfold tailWord_7940384
  simp only [CollatzResearch.WordTrace]
  refine ⟨144804798432676176233454103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193073064576901568311272137 144804798432676176233454103)
  ·
    refine ⟨217207197649014264350181155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144804798432676176233454103 217207197649014264350181155)
    ·
      refine ⟨325810796473521396525271733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217207197649014264350181155 325810796473521396525271733)
      ·
        refine ⟨30544762169392630924244225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325810796473521396525271733 30544762169392630924244225)
        ·
          refine ⟨22908571627044473193183169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30544762169392630924244225 22908571627044473193183169)
          ·
            refine ⟨17181428720283354894887377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22908571627044473193183169 17181428720283354894887377)
            ·
              refine ⟨12886071540212516171165533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17181428720283354894887377 12886071540212516171165533)
              ·
                refine ⟨4832276827579693564187075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12886071540212516171165533 4832276827579693564187075)
                ·
                  refine ⟨7248415241369540346280613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832276827579693564187075 7248415241369540346280613)
                  ·
                    refine ⟨1359077857756788814927615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7248415241369540346280613 1359077857756788814927615)
                    ·
                      rfl

theorem cell23_7940384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 4].length) (baseStart_7940384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940384 prefixEnd_7940384 := by exact prefixLift 7940384
  have htrace : WordTrace (prefixWord ++ tailWord_7940384) baseStart_7940384 baseEnd_7940384 := by
    simpa [prefixWord, tailWord_7940384, baseEnd_7940384] using wordTrace_append hprefix tailTrace_7940384
  have hstable : (prefixWord ++ tailWord_7940384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940384).length < 2 ^ (prefixWord ++ tailWord_7940384).sum := by decide
  have hdescent : baseEnd_7940384 < baseStart_7940384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940397 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 8]
def baseStart_7940397 : Nat := 118140960795 + 7940397 * 2 ^ 59
def prefixEnd_7940397 : Nat := 4983230072969 + 3 ^ 40 * 7940397 * 2
def baseEnd_7940397 : Nat := 453026694279874988213365

theorem tailTrace_7940397 : CollatzResearch.WordTrace tailWord_7940397 prefixEnd_7940397 453026694279874988213365 := by
  unfold tailWord_7940397
  simp only [CollatzResearch.WordTrace]
  refine ⟨289610071014305255687131445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193073380676203503791420963 289610071014305255687131445)
  ·
    refine ⟨27150944157591117720668573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289610071014305255687131445 27150944157591117720668573)
    ·
      refine ⟨10181604059096669145250715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27150944157591117720668573 10181604059096669145250715)
      ·
        refine ⟨15272406088645003717876073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10181604059096669145250715 15272406088645003717876073)
        ·
          refine ⟨11454304566483752788407055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15272406088645003717876073 11454304566483752788407055)
          ·
            refine ⟨17181456849725629182610583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11454304566483752788407055 17181456849725629182610583)
            ·
              refine ⟨25772185274588443773915875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17181456849725629182610583 25772185274588443773915875)
              ·
                refine ⟨38658277911882665660873813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25772185274588443773915875 38658277911882665660873813)
                ·
                  refine ⟨453026694279874988213365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38658277911882665660873813 453026694279874988213365)
                  ·
                    rfl

theorem cell23_7940397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_7940397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940397 prefixEnd_7940397 := by exact prefixLift 7940397
  have htrace : WordTrace (prefixWord ++ tailWord_7940397) baseStart_7940397 baseEnd_7940397 := by
    simpa [prefixWord, tailWord_7940397, baseEnd_7940397] using wordTrace_append hprefix tailTrace_7940397
  have hstable : (prefixWord ++ tailWord_7940397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940397).length < 2 ^ (prefixWord ++ tailWord_7940397).sum := by decide
  have hdescent : baseEnd_7940397 < baseStart_7940397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940447 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 5, 2, 2]
def baseStart_7940447 : Nat := 118140960795 + 7940447 * 2 ^ 59
def prefixEnd_7940447 : Nat := 4983230072969 + 3 ^ 40 * 7940447 * 2
def baseEnd_7940447 : Nat := 4077265922551599698295055

theorem tailTrace_7940447 : CollatzResearch.WordTrace tailWord_7940447 prefixEnd_7940447 4077265922551599698295055 := by
  unfold tailWord_7940447
  simp only [CollatzResearch.WordTrace]
  refine ⟨289611894664124114226451595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193074596442749409484301063 289611894664124114226451595)
  ·
    refine ⟨434417841996186171339677393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289611894664124114226451595 434417841996186171339677393)
    ·
      refine ⟨325813381497139628504758045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434417841996186171339677393 325813381497139628504758045)
      ·
        refine ⟨122180018061427360689284267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325813381497139628504758045 122180018061427360689284267)
        ·
          refine ⟨183270027092141041033926401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122180018061427360689284267 183270027092141041033926401)
          ·
            refine ⟨137452520319105780775444801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183270027092141041033926401 137452520319105780775444801)
            ·
              refine ⟨103089390239329335581583601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137452520319105780775444801 103089390239329335581583601)
              ·
                refine ⟨77317042679497001686187701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103089390239329335581583601 77317042679497001686187701)
                ·
                  refine ⟨7248472751202843908080097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77317042679497001686187701 7248472751202843908080097)
                  ·
                    refine ⟨5436354563402132931060073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7248472751202843908080097 5436354563402132931060073)
                    ·
                      refine ⟨4077265922551599698295055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436354563402132931060073 4077265922551599698295055)
                      ·
                        rfl

theorem cell23_7940447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_7940447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940447 prefixEnd_7940447 := by exact prefixLift 7940447
  have htrace : WordTrace (prefixWord ++ tailWord_7940447) baseStart_7940447 baseEnd_7940447 := by
    simpa [prefixWord, tailWord_7940447, baseEnd_7940447] using wordTrace_append hprefix tailTrace_7940447
  have hstable : (prefixWord ++ tailWord_7940447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940447).length < 2 ^ (prefixWord ++ tailWord_7940447).sum := by decide
  have hdescent : baseEnd_7940447 < baseStart_7940447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940453 : List Nat := [1, 3, 1, 3, 1, 3, 11]
def baseStart_7940453 : Nat := 118140960795 + 7940453 * 2 ^ 59
def prefixEnd_7940453 : Nat := 4983230072969 + 3 ^ 40 * 7940453 * 2
def baseEnd_7940453 : Nat := 50336654363401563886667

theorem tailTrace_7940453 : CollatzResearch.WordTrace tailWord_7940453 prefixEnd_7940453 50336654363401563886667 := by
  unfold tailWord_7940453
  simp only [CollatzResearch.WordTrace]
  refine ⟨289612113502102377251170013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193074742334734918167446675 289612113502102377251170013)
  ·
    refine ⟨108604542563288391469188755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289612113502102377251170013 108604542563288391469188755)
    ·
      refine ⟨162906813844932587203783133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108604542563288391469188755 162906813844932587203783133)
      ·
        refine ⟨61090055191849720201418675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162906813844932587203783133 61090055191849720201418675)
        ·
          refine ⟨91635082787774580302128013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61090055191849720201418675 91635082787774580302128013)
          ·
            refine ⟨34363156045415467613298005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91635082787774580302128013 34363156045415467613298005)
            ·
              refine ⟨50336654363401563886667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34363156045415467613298005 50336654363401563886667)
              ·
                rfl

theorem cell23_7940453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 11].length) (baseStart_7940453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940453 prefixEnd_7940453 := by exact prefixLift 7940453
  have htrace : WordTrace (prefixWord ++ tailWord_7940453) baseStart_7940453 baseEnd_7940453 := by
    simpa [prefixWord, tailWord_7940453, baseEnd_7940453] using wordTrace_append hprefix tailTrace_7940453
  have hstable : (prefixWord ++ tailWord_7940453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940453).length < 2 ^ (prefixWord ++ tailWord_7940453).sum := by decide
  have hdescent : baseEnd_7940453 < baseStart_7940453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940458 : List Nat := [3, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7940458 : Nat := 118140960795 + 7940458 * 2 ^ 59
def prefixEnd_7940458 : Nat := 4983230072969 + 3 ^ 40 * 7940458 * 2
def baseEnd_7940458 : Nat := 4077271570838799155257505

theorem tailTrace_7940458 : CollatzResearch.WordTrace tailWord_7940458 prefixEnd_7940458 4077271570838799155257505 := by
  unfold tailWord_7940458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72403073966771065776275507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193074863911389508736734685 72403073966771065776275507)
  ·
    refine ⟨108604610950156598664413261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72403073966771065776275507 108604610950156598664413261)
    ·
      refine ⟨40726729106308724499154973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108604610950156598664413261 40726729106308724499154973)
      ·
        refine ⟨15272523414865771687183115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40726729106308724499154973 15272523414865771687183115)
        ·
          refine ⟨22908785122298657530774673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15272523414865771687183115 22908785122298657530774673)
          ·
            refine ⟨17181588841723993148081005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22908785122298657530774673 17181588841723993148081005)
            ·
              refine ⟨6443095815646497430530377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17181588841723993148081005 6443095815646497430530377)
              ·
                refine ⟨4832321861734873072897783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443095815646497430530377 4832321861734873072897783)
                ·
                  refine ⟨7248482792602309609346675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832321861734873072897783 7248482792602309609346675)
                  ·
                    refine ⟨10872724188903464414020013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7248482792602309609346675 10872724188903464414020013)
                    ·
                      refine ⟨4077271570838799155257505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10872724188903464414020013 4077271570838799155257505)
                      ·
                        rfl

theorem cell23_7940458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7940458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940458 prefixEnd_7940458 := by exact prefixLift 7940458
  have htrace : WordTrace (prefixWord ++ tailWord_7940458) baseStart_7940458 baseEnd_7940458 := by
    simpa [prefixWord, tailWord_7940458, baseEnd_7940458] using wordTrace_append hprefix tailTrace_7940458
  have hstable : (prefixWord ++ tailWord_7940458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940458).length < 2 ^ (prefixWord ++ tailWord_7940458).sum := by decide
  have hdescent : baseEnd_7940458 < baseStart_7940458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940464 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 3, 2, 2]
def baseStart_7940464 : Nat := 118140960795 + 7940464 * 2 ^ 59
def prefixEnd_7940464 : Nat := 4983230072969 + 3 ^ 40 * 7940464 * 2
def baseEnd_7940464 : Nat := 4077274651722726131782477

theorem tailTrace_7940464 : CollatzResearch.WordTrace tailWord_7940464 prefixEnd_7940464 4077274651722726131782477 := by
  unfold tailWord_7940464
  simp only [CollatzResearch.WordTrace]
  refine ⟨144806257352531263064910223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193075009803375017419880297 144806257352531263064910223)
  ·
    refine ⟨217209386028796894597365335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144806257352531263064910223 217209386028796894597365335)
    ·
      refine ⟨325814079043195341896048003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217209386028796894597365335 325814079043195341896048003)
      ·
        refine ⟨488721118564793012844072005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325814079043195341896048003 488721118564793012844072005)
        ·
          refine ⟨91635209730898689908263501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488721118564793012844072005 91635209730898689908263501)
          ·
            refine ⟨34363203649087008715598813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91635209730898689908263501 34363203649087008715598813)
            ·
              refine ⟨12886201368407628268349555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34363203649087008715598813 12886201368407628268349555)
              ·
                refine ⟨19329302052611442402524333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12886201368407628268349555 19329302052611442402524333)
                ·
                  refine ⟨7248488269729290900946625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19329302052611442402524333 7248488269729290900946625)
                  ·
                    refine ⟨5436366202296968175709969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7248488269729290900946625 5436366202296968175709969)
                    ·
                      refine ⟨4077274651722726131782477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436366202296968175709969 4077274651722726131782477)
                      ·
                        rfl

theorem cell23_7940464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 2, 2].length) (baseStart_7940464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940464 prefixEnd_7940464 := by exact prefixLift 7940464
  have htrace : WordTrace (prefixWord ++ tailWord_7940464) baseStart_7940464 baseEnd_7940464 := by
    simpa [prefixWord, tailWord_7940464, baseEnd_7940464] using wordTrace_append hprefix tailTrace_7940464
  have hstable : (prefixWord ++ tailWord_7940464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940464).length < 2 ^ (prefixWord ++ tailWord_7940464).sum := by decide
  have hdescent : baseEnd_7940464 < baseStart_7940464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940473 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_7940473 : Nat := 118140960795 + 7940473 * 2 ^ 59
def prefixEnd_7940473 : Nat := 4983230072969 + 3 ^ 40 * 7940473 * 2
def baseEnd_7940473 : Nat := 4077279273048616596569935

theorem tailTrace_7940473 : CollatzResearch.WordTrace tailWord_7940473 prefixEnd_7940473 4077279273048616596569935 := by
  unfold tailWord_7940473
  simp only [CollatzResearch.WordTrace]
  refine ⟨289612842962029920666898073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193075228641353280444598715 289612842962029920666898073)
  ·
    refine ⟨217209632221522440500173555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289612842962029920666898073 217209632221522440500173555)
    ·
      refine ⟨325814448332283660750260333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217209632221522440500173555 325814448332283660750260333)
      ·
        refine ⟨122180418124606372781347625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325814448332283660750260333 122180418124606372781347625)
        ·
          refine ⟨91635313593454779586010719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122180418124606372781347625 91635313593454779586010719)
          ·
            refine ⟨137452970390182169379016079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91635313593454779586010719 137452970390182169379016079)
            ·
              refine ⟨206179455585273254068524119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137452970390182169379016079 206179455585273254068524119)
              ·
                refine ⟨309269183377909881102786179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206179455585273254068524119 309269183377909881102786179)
                ·
                  refine ⟨463903775066864821654179269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309269183377909881102786179 463903775066864821654179269)
                  ·
                    refine ⟨86981957825037154060158613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 463903775066864821654179269 86981957825037154060158613)
                    ·
                      refine ⟨4077279273048616596569935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86981957825037154060158613 4077279273048616596569935)
                      ·
                        rfl

theorem cell23_7940473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_7940473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940473 prefixEnd_7940473 := by exact prefixLift 7940473
  have htrace : WordTrace (prefixWord ++ tailWord_7940473) baseStart_7940473 baseEnd_7940473 := by
    simpa [prefixWord, tailWord_7940473, baseEnd_7940473] using wordTrace_append hprefix tailTrace_7940473
  have hstable : (prefixWord ++ tailWord_7940473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940473).length < 2 ^ (prefixWord ++ tailWord_7940473).sum := by decide
  have hdescent : baseEnd_7940473 < baseStart_7940473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940530 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_7940530 : Nat := 118140960795 + 7940530 * 2 ^ 59
def prefixEnd_7940530 : Nat := 4983230072969 + 3 ^ 40 * 7940530 * 2
def baseEnd_7940530 : Nat := 1359102847148640957852391

theorem tailTrace_7940530 : CollatzResearch.WordTrace tailWord_7940530 prefixEnd_7940530 1359102847148640957852391 := by
  unfold tailWord_7940530
  simp only [CollatzResearch.WordTrace]
  refine ⟨72403730480705854850430761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193076614615215612934482029 72403730480705854850430761)
  ·
    refine ⟨54302797860529391137823071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72403730480705854850430761 54302797860529391137823071)
    ·
      refine ⟨81454196790794086706734607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54302797860529391137823071 81454196790794086706734607)
      ·
        refine ⟨122181295186191130060101911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81454196790794086706734607 122181295186191130060101911)
        ·
          refine ⟨183271942779286695090152867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122181295186191130060101911 183271942779286695090152867)
          ·
            refine ⟨274907914168930042635229301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183271942779286695090152867 274907914168930042635229301)
            ·
              refine ⟨25772616953337191497052747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274907914168930042635229301 25772616953337191497052747)
              ·
                refine ⟨38658925430005787245579121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25772616953337191497052747 38658925430005787245579121)
                ·
                  refine ⟨28994194072504340434184341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38658925430005787245579121 28994194072504340434184341)
                  ·
                    refine ⟨1359102847148640957852391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28994194072504340434184341 1359102847148640957852391)
                    ·
                      rfl

theorem cell23_7940530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_7940530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940530 prefixEnd_7940530 := by exact prefixLift 7940530
  have htrace : WordTrace (prefixWord ++ tailWord_7940530) baseStart_7940530 baseEnd_7940530 := by
    simpa [prefixWord, tailWord_7940530, baseEnd_7940530] using wordTrace_append hprefix tailTrace_7940530
  have hstable : (prefixWord ++ tailWord_7940530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940530).length < 2 ^ (prefixWord ++ tailWord_7940530).sum := by decide
  have hdescent : baseEnd_7940530 < baseStart_7940530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940554 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_7940554 : Nat := 118140960795 + 7940554 * 2 ^ 59
def prefixEnd_7940554 : Nat := 4983230072969 + 3 ^ 40 * 7940554 * 2
def baseEnd_7940554 : Nat := 4077320864981630779657063

theorem tailTrace_7940554 : CollatzResearch.WordTrace tailWord_7940554 prefixEnd_7940554 4077320864981630779657063 := by
  unfold tailWord_7940554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72403949318684117875149179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193077198183157647667064477 72403949318684117875149179)
  ·
    refine ⟨108605923978026176812723769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72403949318684117875149179 108605923978026176812723769)
    ·
      refine ⟨81454442983519632609542827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108605923978026176812723769 81454442983519632609542827)
      ·
        refine ⟨122181664475279448914314241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81454442983519632609542827 122181664475279448914314241)
        ·
          refine ⟨91636248356459586685735681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122181664475279448914314241 91636248356459586685735681)
          ·
            refine ⟨68727186267344690014301761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91636248356459586685735681 68727186267344690014301761)
            ·
              refine ⟨51545389700508517510726321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68727186267344690014301761 51545389700508517510726321)
              ·
                refine ⟨38659042275381388133044741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51545389700508517510726321 38659042275381388133044741)
                ·
                  refine ⟨7248570426634010274945889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38659042275381388133044741 7248570426634010274945889)
                  ·
                    refine ⟨5436427819975507706209417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7248570426634010274945889 5436427819975507706209417)
                    ·
                      refine ⟨4077320864981630779657063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436427819975507706209417 4077320864981630779657063)
                      ·
                        rfl

theorem cell23_7940554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_7940554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940554 prefixEnd_7940554 := by exact prefixLift 7940554
  have htrace : WordTrace (prefixWord ++ tailWord_7940554) baseStart_7940554 baseEnd_7940554 := by
    simpa [prefixWord, tailWord_7940554, baseEnd_7940554] using wordTrace_append hprefix tailTrace_7940554
  have hstable : (prefixWord ++ tailWord_7940554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940554).length < 2 ^ (prefixWord ++ tailWord_7940554).sum := by decide
  have hdescent : baseEnd_7940554 < baseStart_7940554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940577 : List Nat := [1, 2, 3, 1, 2, 2, 1, 6, 5]
def baseStart_7940577 : Nat := 118140960795 + 7940577 * 2 ^ 59
def prefixEnd_7940577 : Nat := 4983230072969 + 3 ^ 40 * 7940577 * 2
def baseEnd_7940577 : Nat := 453036963892964909963273

theorem tailTrace_7940577 : CollatzResearch.WordTrace tailWord_7940577 prefixEnd_7940577 453036963892964909963273 := by
  unfold tailWord_7940577
  simp only [CollatzResearch.WordTrace]
  refine ⟨289616636153653146428683985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193077757435768764285789323 289616636153653146428683985)
  ·
    refine ⟨217212477115239859821512989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289616636153653146428683985 217212477115239859821512989)
    ·
      refine ⟨81454678918214947433067371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217212477115239859821512989 81454678918214947433067371)
      ·
        refine ⟨122182018377322421149601057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81454678918214947433067371 122182018377322421149601057)
        ·
          refine ⟨91636513782991815862200793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122182018377322421149601057 91636513782991815862200793)
          ·
            refine ⟨68727385337243861896650595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91636513782991815862200793 68727385337243861896650595)
            ·
              refine ⟨103091078005865792844975893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68727385337243861896650595 103091078005865792844975893)
              ·
                refine ⟨4832394281524959039608245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103091078005865792844975893 4832394281524959039608245)
                ·
                  refine ⟨453036963892964909963273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832394281524959039608245 453036963892964909963273)
                  ·
                    rfl

theorem cell23_7940577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 5].length) (baseStart_7940577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940577 prefixEnd_7940577 := by exact prefixLift 7940577
  have htrace : WordTrace (prefixWord ++ tailWord_7940577) baseStart_7940577 baseEnd_7940577 := by
    simpa [prefixWord, tailWord_7940577, baseEnd_7940577] using wordTrace_append hprefix tailTrace_7940577
  have hstable : (prefixWord ++ tailWord_7940577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940577).length < 2 ^ (prefixWord ++ tailWord_7940577).sum := by decide
  have hdescent : baseEnd_7940577 < baseStart_7940577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940627 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 4]
def baseStart_7940627 : Nat := 118140960795 + 7940627 * 2 ^ 59
def prefixEnd_7940627 : Nat := 4983230072969 + 3 ^ 40 * 7940627 * 2
def baseEnd_7940627 : Nat := 4077358349069408994044227

theorem tailTrace_7940627 : CollatzResearch.WordTrace tailWord_7940627 prefixEnd_7940627 4077358349069408994044227 := by
  unfold tailWord_7940627
  simp only [CollatzResearch.WordTrace]
  refine ⟨289618459803472004968004135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193078973202314669978669423 289618459803472004968004135)
  ·
    refine ⟨434427689705208007452006203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289618459803472004968004135 434427689705208007452006203)
    ·
      refine ⟨651641534557812011178009305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434427689705208007452006203 651641534557812011178009305)
      ·
        refine ⟨488731150918359008383506979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651641534557812011178009305 488731150918359008383506979)
        ·
          refine ⟨733096726377538512575260469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488731150918359008383506979 733096726377538512575260469)
          ·
            refine ⟨68727818097894235553930669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 733096726377538512575260469 68727818097894235553930669)
            ·
              refine ⟨25772931786710338332724001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68727818097894235553930669 25772931786710338332724001)
              ·
                refine ⟨19329698840032753749543001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25772931786710338332724001 19329698840032753749543001)
                ·
                  refine ⟨14497274130024565312157251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19329698840032753749543001 14497274130024565312157251)
                  ·
                    refine ⟨21745911195036847968235877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14497274130024565312157251 21745911195036847968235877)
                    ·
                      refine ⟨4077358349069408994044227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21745911195036847968235877 4077358349069408994044227)
                      ·
                        rfl

theorem cell23_7940627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_7940627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940627 prefixEnd_7940627 := by exact prefixLift 7940627
  have htrace : WordTrace (prefixWord ++ tailWord_7940627) baseStart_7940627 baseEnd_7940627 := by
    simpa [prefixWord, tailWord_7940627, baseEnd_7940627] using wordTrace_append hprefix tailTrace_7940627
  have hstable : (prefixWord ++ tailWord_7940627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940627).length < 2 ^ (prefixWord ++ tailWord_7940627).sum := by decide
  have hdescent : baseEnd_7940627 < baseStart_7940627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940628 : List Nat := [2, 4, 3, 1, 1, 2, 3, 2, 5]
def baseStart_7940628 : Nat := 118140960795 + 7940628 * 2 ^ 59
def prefixEnd_7940628 : Nat := 4983230072969 + 3 ^ 40 * 7940628 * 2
def baseEnd_7940628 : Nat := 453039873616673721125747

theorem tailTrace_7940628 : CollatzResearch.WordTrace tailWord_7940628 prefixEnd_7940628 453039873616673721125747 := by
  unfold tailWord_7940628
  simp only [CollatzResearch.WordTrace]
  refine ⟨144809248138234191069395269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193078997517645588092527025 144809248138234191069395269)
  ·
    refine ⟨27151734025918910825511613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144809248138234191069395269 27151734025918910825511613)
    ·
      refine ⟨10181900259719591559566855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27151734025918910825511613 10181900259719591559566855)
      ·
        refine ⟨15272850389579387339350283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10181900259719591559566855 15272850389579387339350283)
        ·
          refine ⟨22909275584369081009025425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15272850389579387339350283 22909275584369081009025425)
          ·
            refine ⟨17181956688276810756769069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22909275584369081009025425 17181956688276810756769069)
            ·
              refine ⟨6443233758103804033788401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17181956688276810756769069 6443233758103804033788401)
              ·
                refine ⟨4832425318577853025341301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443233758103804033788401 4832425318577853025341301)
                ·
                  refine ⟨453039873616673721125747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832425318577853025341301 453039873616673721125747)
                  ·
                    rfl

theorem cell23_7940628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_7940628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940628 prefixEnd_7940628 := by exact prefixLift 7940628
  have htrace : WordTrace (prefixWord ++ tailWord_7940628) baseStart_7940628 baseEnd_7940628 := by
    simpa [prefixWord, tailWord_7940628, baseEnd_7940628] using wordTrace_append hprefix tailTrace_7940628
  have hstable : (prefixWord ++ tailWord_7940628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940628).length < 2 ^ (prefixWord ++ tailWord_7940628).sum := by decide
  have hdescent : baseEnd_7940628 < baseStart_7940628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940664 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_7940664 : Nat := 118140960795 + 7940664 * 2 ^ 59
def prefixEnd_7940664 : Nat := 4983230072969 + 3 ^ 40 * 7940664 * 2
def baseEnd_7940664 : Nat := 4077377347853625349281557

theorem tailTrace_7940664 : CollatzResearch.WordTrace tailWord_7940664 prefixEnd_7940664 4077377347853625349281557 := by
  unfold tailWord_7940664
  simp only [CollatzResearch.WordTrace]
  refine ⟨144809904652168980143550523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193079872869558640191400697 144809904652168980143550523)
  ·
    refine ⟨217214856978253470215325785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144809904652168980143550523 217214856978253470215325785)
    ·
      refine ⟨162911142733690102661494339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217214856978253470215325785 162911142733690102661494339)
      ·
        refine ⟨244366714100535153992241509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162911142733690102661494339 244366714100535153992241509)
        ·
          refine ⟨45818758893850341373545283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244366714100535153992241509 45818758893850341373545283)
          ·
            refine ⟨68728138340775512060317925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45818758893850341373545283 68728138340775512060317925)
            ·
              refine ⟨12886525938895408511309611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68728138340775512060317925 12886525938895408511309611)
              ·
                refine ⟨19329788908343112766964417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12886525938895408511309611 19329788908343112766964417)
                ·
                  refine ⟨14497341681257334575223313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19329788908343112766964417 14497341681257334575223313)
                  ·
                    refine ⟨10873006260943000931417485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14497341681257334575223313 10873006260943000931417485)
                    ·
                      refine ⟨4077377347853625349281557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10873006260943000931417485 4077377347853625349281557)
                      ·
                        rfl

theorem cell23_7940664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_7940664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940664 prefixEnd_7940664 := by exact prefixLift 7940664
  have htrace : WordTrace (prefixWord ++ tailWord_7940664) baseStart_7940664 baseEnd_7940664 := by
    simpa [prefixWord, tailWord_7940664, baseEnd_7940664] using wordTrace_append hprefix tailTrace_7940664
  have hstable : (prefixWord ++ tailWord_7940664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940664).length < 2 ^ (prefixWord ++ tailWord_7940664).sum := by decide
  have hdescent : baseEnd_7940664 < baseStart_7940664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940704 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 4, 3, 2]
def baseStart_7940704 : Nat := 118140960795 + 7940704 * 2 ^ 59
def prefixEnd_7940704 : Nat := 4983230072969 + 3 ^ 40 * 7940704 * 2
def baseEnd_7940704 : Nat := 4077397887079805192781373

theorem tailTrace_7940704 : CollatzResearch.WordTrace tailWord_7940704 prefixEnd_7940704 4077397887079805192781373 := by
  unfold tailWord_7940704
  simp only [CollatzResearch.WordTrace]
  refine ⟨144810634112096523559278583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193080845482795364745704777 144810634112096523559278583)
  ·
    refine ⟨217215951168144785338917875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144810634112096523559278583 217215951168144785338917875)
    ·
      refine ⟨325823926752217178008376813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217215951168144785338917875 325823926752217178008376813)
      ·
        refine ⟨122183972532081441753141305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325823926752217178008376813 122183972532081441753141305)
        ·
          refine ⟨91637979399061081314855979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122183972532081441753141305 91637979399061081314855979)
          ·
            refine ⟨137456969098591621972283969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91637979399061081314855979 137456969098591621972283969)
            ·
              refine ⟨103092726823943716479212977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137456969098591621972283969 103092726823943716479212977)
              ·
                refine ⟨77319545117957787359409733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103092726823943716479212977 77319545117957787359409733)
                ·
                  refine ⟨14497414709617085129889325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77319545117957787359409733 14497414709617085129889325)
                  ·
                    refine ⟨5436530516106406923708497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14497414709617085129889325 5436530516106406923708497)
                    ·
                      refine ⟨4077397887079805192781373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436530516106406923708497 4077397887079805192781373)
                      ·
                        rfl

theorem cell23_7940704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_7940704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940704 prefixEnd_7940704 := by exact prefixLift 7940704
  have htrace : WordTrace (prefixWord ++ tailWord_7940704) baseStart_7940704 baseEnd_7940704 := by
    simpa [prefixWord, tailWord_7940704, baseEnd_7940704] using wordTrace_append hprefix tailTrace_7940704
  have hstable : (prefixWord ++ tailWord_7940704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940704).length < 2 ^ (prefixWord ++ tailWord_7940704).sum := by decide
  have hdescent : baseEnd_7940704 < baseStart_7940704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940714 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_7940714 : Nat := 118140960795 + 7940714 * 2 ^ 59
def prefixEnd_7940714 : Nat := 4983230072969 + 3 ^ 40 * 7940714 * 2
def baseEnd_7940714 : Nat := 1359134340628783384552109

theorem tailTrace_7940714 : CollatzResearch.WordTrace tailWord_7940714 prefixEnd_7940714 1359134340628783384552109 := by
  unfold tailWord_7940714
  simp only [CollatzResearch.WordTrace]
  refine ⟨72405408238539204706605299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193081088636104545884280797 72405408238539204706605299)
  ·
    refine ⟨108608112357808807059907949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72405408238539204706605299 108608112357808807059907949)
    ·
      refine ⟨40728042134178302647465481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108608112357808807059907949 40728042134178302647465481)
      ·
        refine ⟨30546031600633726985599111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40728042134178302647465481 30546031600633726985599111)
        ·
          refine ⟨45819047400950590478398667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30546031600633726985599111 45819047400950590478398667)
          ·
            refine ⟨68728571101425885717598001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45819047400950590478398667 68728571101425885717598001)
            ·
              refine ⟨51546428326069414288198501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68728571101425885717598001 51546428326069414288198501)
              ·
                refine ⟨9664955311138015179037219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51546428326069414288198501 9664955311138015179037219)
                ·
                  refine ⟨14497432966707022768555829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664955311138015179037219 14497432966707022768555829)
                  ·
                    refine ⟨1359134340628783384552109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14497432966707022768555829 1359134340628783384552109)
                    ·
                      rfl

theorem cell23_7940714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_7940714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940714 prefixEnd_7940714 := by exact prefixLift 7940714
  have htrace : WordTrace (prefixWord ++ tailWord_7940714) baseStart_7940714 baseEnd_7940714 := by
    simpa [prefixWord, tailWord_7940714, baseEnd_7940714] using wordTrace_append hprefix tailTrace_7940714
  have hstable : (prefixWord ++ tailWord_7940714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940714).length < 2 ^ (prefixWord ++ tailWord_7940714).sum := by decide
  have hdescent : baseEnd_7940714 < baseStart_7940714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940727 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 1, 6]
def baseStart_7940727 : Nat := 118140960795 + 7940727 * 2 ^ 59
def prefixEnd_7940727 : Nat := 4983230072969 + 3 ^ 40 * 7940727 * 2
def baseEnd_7940727 : Nat := 1359136565711619534264589

theorem tailTrace_7940727 : CollatzResearch.WordTrace tailWord_7940727 prefixEnd_7940727 1359136565711619534264589 := by
  unfold tailWord_7940727
  simp only [CollatzResearch.WordTrace]
  refine ⟨289622107103109722046644435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193081404735406481364429623 289622107103109722046644435)
  ·
    refine ⟨434433160654664583069966653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289622107103109722046644435 434433160654664583069966653)
    ·
      refine ⟨162912435245499218651237495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434433160654664583069966653 162912435245499218651237495)
      ·
        refine ⟨244368652868248827976856243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162912435245499218651237495 244368652868248827976856243)
        ·
          refine ⟨366552979302373241965284365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244368652868248827976856243 366552979302373241965284365)
          ·
            refine ⟨137457367238389965736981637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366552979302373241965284365 137457367238389965736981637)
            ·
              refine ⟨25773256357198118575684057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137457367238389965736981637 25773256357198118575684057)
              ·
                refine ⟨19329942267898588931763043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25773256357198118575684057 19329942267898588931763043)
                ·
                  refine ⟨28994913401847883397644565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19329942267898588931763043 28994913401847883397644565)
                  ·
                    refine ⟨1359136565711619534264589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28994913401847883397644565 1359136565711619534264589)
                    ·
                      rfl

theorem cell23_7940727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_7940727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940727 prefixEnd_7940727 := by exact prefixLift 7940727
  have htrace : WordTrace (prefixWord ++ tailWord_7940727) baseStart_7940727 baseEnd_7940727 := by
    simpa [prefixWord, tailWord_7940727, baseEnd_7940727] using wordTrace_append hprefix tailTrace_7940727
  have hstable : (prefixWord ++ tailWord_7940727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940727).length < 2 ^ (prefixWord ++ tailWord_7940727).sum := by decide
  have hdescent : baseEnd_7940727 < baseStart_7940727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940754 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7940754 : Nat := 118140960795 + 7940754 * 2 ^ 59
def prefixEnd_7940754 : Nat := 4983230072969 + 3 ^ 40 * 7940754 * 2
def baseEnd_7940754 : Nat := 4077423561112529997156143

theorem tailTrace_7940754 : CollatzResearch.WordTrace tailWord_7940754 prefixEnd_7940754 4077423561112529997156143 := by
  unfold tailWord_7940754
  simp only [CollatzResearch.WordTrace]
  refine ⟨72405772968502976414469329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193082061249341270438584877 72405772968502976414469329)
  ·
    refine ⟨54304329726377232310851997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72405772968502976414469329 54304329726377232310851997)
    ·
      refine ⟨20364123647391462116569499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54304329726377232310851997 20364123647391462116569499)
      ·
        refine ⟨30546185471087193174854249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20364123647391462116569499 30546185471087193174854249)
        ·
          refine ⟨22909639103315394881140687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30546185471087193174854249 22909639103315394881140687)
          ·
            refine ⟨34364458654973092321711031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22909639103315394881140687 34364458654973092321711031)
            ·
              refine ⟨51546687982459638482566547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34364458654973092321711031 51546687982459638482566547)
              ·
                refine ⟨77320031973689457723849821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51546687982459638482566547 77320031973689457723849821)
                ·
                  refine ⟨28995011990133546646443683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77320031973689457723849821 28995011990133546646443683)
                  ·
                    refine ⟨43492517985200319969665525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28995011990133546646443683 43492517985200319969665525)
                    ·
                      refine ⟨4077423561112529997156143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43492517985200319969665525 4077423561112529997156143)
                      ·
                        rfl

theorem cell23_7940754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7940754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940754 prefixEnd_7940754 := by exact prefixLift 7940754
  have htrace : WordTrace (prefixWord ++ tailWord_7940754) baseStart_7940754 baseEnd_7940754 := by
    simpa [prefixWord, tailWord_7940754, baseEnd_7940754] using wordTrace_append hprefix tailTrace_7940754
  have hstable : (prefixWord ++ tailWord_7940754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940754).length < 2 ^ (prefixWord ++ tailWord_7940754).sum := by decide
  have hdescent : baseEnd_7940754 < baseStart_7940754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940761 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 2, 4]
def baseStart_7940761 : Nat := 118140960795 + 7940761 * 2 ^ 59
def prefixEnd_7940761 : Nat := 4983230072969 + 3 ^ 40 * 7940761 * 2
def baseEnd_7940761 : Nat := 1359142385159037156589537

theorem tailTrace_7940761 : CollatzResearch.WordTrace tailWord_7940761 prefixEnd_7940761 1359142385159037156589537 := by
  unfold tailWord_7940761
  simp only [CollatzResearch.WordTrace]
  refine ⟨289623347184986545853382137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193082231456657697235588091 289623347184986545853382137)
  ·
    refine ⟨217217510388739909390036603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289623347184986545853382137 217217510388739909390036603)
    ·
      refine ⟨325826265583109864085054905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217217510388739909390036603 325826265583109864085054905)
      ·
        refine ⟨244369699187332398063791179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325826265583109864085054905 244369699187332398063791179)
        ·
          refine ⟨366554548780998597095686769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244369699187332398063791179 366554548780998597095686769)
          ·
            refine ⟨274915911585748947821765077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366554548780998597095686769 274915911585748947821765077)
            ·
              refine ⟨6443341677790990964572619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 274915911585748947821765077 6443341677790990964572619)
              ·
                refine ⟨9665012516686486446858929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443341677790990964572619 9665012516686486446858929)
                ·
                  refine ⟨7248759387514864835144197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9665012516686486446858929 7248759387514864835144197)
                  ·
                    refine ⟨1359142385159037156589537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7248759387514864835144197 1359142385159037156589537)
                    ·
                      rfl

theorem cell23_7940761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 4].length) (baseStart_7940761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940761 prefixEnd_7940761 := by exact prefixLift 7940761
  have htrace : WordTrace (prefixWord ++ tailWord_7940761) baseStart_7940761 baseEnd_7940761 := by
    simpa [prefixWord, tailWord_7940761, baseEnd_7940761] using wordTrace_append hprefix tailTrace_7940761
  have hstable : (prefixWord ++ tailWord_7940761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940761).length < 2 ^ (prefixWord ++ tailWord_7940761).sum := by decide
  have hdescent : baseEnd_7940761 < baseStart_7940761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940764 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7940764 : Nat := 118140960795 + 7940764 * 2 ^ 59
def prefixEnd_7940764 : Nat := 4983230072969 + 3 ^ 40 * 7940764 * 2
def baseEnd_7940764 : Nat := 4077428695919074958031097

theorem tailTrace_7940764 : CollatzResearch.WordTrace tailWord_7940764 prefixEnd_7940764 4077428695919074958031097 := by
  unfold tailWord_7940764
  simp only [CollatzResearch.WordTrace]
  refine ⟨144811728301987838682870673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193082304402650451577160897 144811728301987838682870673)
  ·
    refine ⟨108608796226490879012153005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144811728301987838682870673 108608796226490879012153005)
    ·
      refine ⟨40728298584934079629557377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108608796226490879012153005 40728298584934079629557377)
      ·
        refine ⟨30546223938700559722168033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40728298584934079629557377 30546223938700559722168033)
        ·
          refine ⟨22909667954025419791626025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30546223938700559722168033 22909667954025419791626025)
          ·
            refine ⟨17182250965519064843719519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22909667954025419791626025 17182250965519064843719519)
            ·
              refine ⟨25773376448278597265579279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182250965519064843719519 25773376448278597265579279)
              ·
                refine ⟨38660064672417895898368919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25773376448278597265579279 38660064672417895898368919)
                ·
                  refine ⟨57990097008626843847553379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38660064672417895898368919 57990097008626843847553379)
                  ·
                    refine ⟨86985145512940265771330069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57990097008626843847553379 86985145512940265771330069)
                    ·
                      refine ⟨4077428695919074958031097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86985145512940265771330069 4077428695919074958031097)
                      ·
                        rfl

theorem cell23_7940764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7940764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940764 prefixEnd_7940764 := by exact prefixLift 7940764
  have htrace : WordTrace (prefixWord ++ tailWord_7940764) baseStart_7940764 baseEnd_7940764 := by
    simpa [prefixWord, tailWord_7940764, baseEnd_7940764] using wordTrace_append hprefix tailTrace_7940764
  have hstable : (prefixWord ++ tailWord_7940764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940764).length < 2 ^ (prefixWord ++ tailWord_7940764).sum := by decide
  have hdescent : baseEnd_7940764 < baseStart_7940764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940817 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 1, 8]
def baseStart_7940817 : Nat := 118140960795 + 7940817 * 2 ^ 59
def prefixEnd_7940817 : Nat := 4983230072969 + 3 ^ 40 * 7940817 * 2
def baseEnd_7940817 : Nat := 1359151970131254416889451

theorem tailTrace_7940817 : CollatzResearch.WordTrace tailWord_7940817 prefixEnd_7940817 1359151970131254416889451 := by
  unfold tailWord_7940817
  simp only [CollatzResearch.WordTrace]
  refine ⟨289625389672783667417420705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193083593115189111611613803 289625389672783667417420705)
  ·
    refine ⟨217219042254587750563065529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289625389672783667417420705 217219042254587750563065529)
    ·
      refine ⟨162914281690940812922299147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217219042254587750563065529 162914281690940812922299147)
      ·
        refine ⟨244371422536411219383448721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162914281690940812922299147 244371422536411219383448721)
        ·
          refine ⟨183278566902308414537586541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244371422536411219383448721 183278566902308414537586541)
          ·
            refine ⟨68729462588365655451594953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183278566902308414537586541 68729462588365655451594953)
            ·
              refine ⟨51547096941274241588696215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68729462588365655451594953 51547096941274241588696215)
              ·
                refine ⟨77320645411911362383044323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51547096941274241588696215 77320645411911362383044323)
                ·
                  refine ⟨115980968117867043574566485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77320645411911362383044323 115980968117867043574566485)
                  ·
                    refine ⟨1359151970131254416889451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115980968117867043574566485 1359151970131254416889451)
                    ·
                      rfl

theorem cell23_7940817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_7940817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940817 prefixEnd_7940817 := by exact prefixLift 7940817
  have htrace : WordTrace (prefixWord ++ tailWord_7940817) baseStart_7940817 baseEnd_7940817 := by
    simpa [prefixWord, tailWord_7940817, baseEnd_7940817] using wordTrace_append hprefix tailTrace_7940817
  have hstable : (prefixWord ++ tailWord_7940817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940817).length < 2 ^ (prefixWord ++ tailWord_7940817).sum := by decide
  have hdescent : baseEnd_7940817 < baseStart_7940817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940841 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 6, 2, 2]
def baseStart_7940841 : Nat := 118140960795 + 7940841 * 2 ^ 59
def prefixEnd_7940841 : Nat := 4983230072969 + 3 ^ 40 * 7940841 * 2
def baseEnd_7940841 : Nat := 4077468233929471156768243

theorem tailTrace_7940841 : CollatzResearch.WordTrace tailWord_7940841 prefixEnd_7940841 4077468233929471156768243 := by
  unfold tailWord_7940841
  simp only [CollatzResearch.WordTrace]
  refine ⟨289626265024696719516294377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193084176683131146344196251 289626265024696719516294377)
  ·
    refine ⟨217219698768522539637220783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289626265024696719516294377 217219698768522539637220783)
    ·
      refine ⟨325829548152783809455831175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217219698768522539637220783 325829548152783809455831175)
      ·
        refine ⟨488744322229175714183746763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325829548152783809455831175 488744322229175714183746763)
        ·
          refine ⟨733116483343763571275620145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488744322229175714183746763 733116483343763571275620145)
          ·
            refine ⟨549837362507822678456715109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733116483343763571275620145 549837362507822678456715109)
            ·
              refine ⟨103094505470216752210634083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 549837362507822678456715109 103094505470216752210634083)
              ·
                refine ⟨154641758205325128315951125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103094505470216752210634083 154641758205325128315951125)
                ·
                  refine ⟨7248832415874615389810209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154641758205325128315951125 7248832415874615389810209)
                  ·
                    refine ⟨5436624311905961542357657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7248832415874615389810209 5436624311905961542357657)
                    ·
                      refine ⟨4077468233929471156768243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436624311905961542357657 4077468233929471156768243)
                      ·
                        rfl

theorem cell23_7940841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 2, 2].length) (baseStart_7940841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940841 prefixEnd_7940841 := by exact prefixLift 7940841
  have htrace : WordTrace (prefixWord ++ tailWord_7940841) baseStart_7940841 baseEnd_7940841 := by
    simpa [prefixWord, tailWord_7940841, baseEnd_7940841] using wordTrace_append hprefix tailTrace_7940841
  have hstable : (prefixWord ++ tailWord_7940841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940841).length < 2 ^ (prefixWord ++ tailWord_7940841).sum := by decide
  have hdescent : baseEnd_7940841 < baseStart_7940841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940845 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_7940845 : Nat := 118140960795 + 7940845 * 2 ^ 59
def prefixEnd_7940845 : Nat := 4983230072969 + 3 ^ 40 * 7940845 * 2
def baseEnd_7940845 : Nat := 4077470287852089141118225

theorem tailTrace_7940845 : CollatzResearch.WordTrace tailWord_7940845 prefixEnd_7940845 4077470287852089141118225 := by
  unfold tailWord_7940845
  simp only [CollatzResearch.WordTrace]
  refine ⟨289626410916682228199439989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193084273944454818799626659 289626410916682228199439989)
  ·
    refine ⟨27152476023438958893697499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289626410916682228199439989 27152476023438958893697499)
    ·
      refine ⟨40728714035158438340546249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27152476023438958893697499 40728714035158438340546249)
      ·
        refine ⟨30546535526368828755409687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40728714035158438340546249 30546535526368828755409687)
        ·
          refine ⟨45819803289553243133114531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30546535526368828755409687 45819803289553243133114531)
          ·
            refine ⟨68729704934329864699671797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45819803289553243133114531 68729704934329864699671797)
            ·
              refine ⟨6443409837593424815594231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68729704934329864699671797 6443409837593424815594231)
              ·
                refine ⟨9665114756390137223391347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443409837593424815594231 9665114756390137223391347)
                ·
                  refine ⟨14497672134585205835087021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665114756390137223391347 14497672134585205835087021)
                  ·
                    refine ⟨5436627050469452188157633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14497672134585205835087021 5436627050469452188157633)
                    ·
                      refine ⟨4077470287852089141118225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436627050469452188157633 4077470287852089141118225)
                      ·
                        rfl

theorem cell23_7940845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_7940845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940845 prefixEnd_7940845 := by exact prefixLift 7940845
  have htrace : WordTrace (prefixWord ++ tailWord_7940845) baseStart_7940845 baseEnd_7940845 := by
    simpa [prefixWord, tailWord_7940845, baseEnd_7940845] using wordTrace_append hprefix tailTrace_7940845
  have hstable : (prefixWord ++ tailWord_7940845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940845).length < 2 ^ (prefixWord ++ tailWord_7940845).sum := by decide
  have hdescent : baseEnd_7940845 < baseStart_7940845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940853 : List Nat := [1, 3, 6, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7940853 : Nat := 118140960795 + 7940853 * 2 ^ 59
def prefixEnd_7940853 : Nat := 4983230072969 + 3 ^ 40 * 7940853 * 2
def baseEnd_7940853 : Nat := 4077474395697325109818189

theorem tailTrace_7940853 : CollatzResearch.WordTrace tailWord_7940853 prefixEnd_7940853 4077474395697325109818189 := by
  unfold tailWord_7940853
  simp only [CollatzResearch.WordTrace]
  refine ⟨289626702700653245565731213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193084468467102163710487475 289626702700653245565731213)
  ·
    refine ⟨108610013512744967087149205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289626702700653245565731213 108610013512744967087149205)
    ·
      refine ⟨5091094383409920332210119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108610013512744967087149205 5091094383409920332210119)
      ·
        refine ⟨7636641575114880498315179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091094383409920332210119 7636641575114880498315179)
        ·
          refine ⟨11454962362672320747472769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7636641575114880498315179 11454962362672320747472769)
          ·
            refine ⟨8591221772004240560604577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11454962362672320747472769 8591221772004240560604577)
            ·
              refine ⟨6443416329003180420453433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8591221772004240560604577 6443416329003180420453433)
              ·
                refine ⟨4832562246752385315340075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443416329003180420453433 4832562246752385315340075)
                ·
                  refine ⟨7248843370128577973010113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832562246752385315340075 7248843370128577973010113)
                  ·
                    refine ⟨5436632527596433479757585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7248843370128577973010113 5436632527596433479757585)
                    ·
                      refine ⟨4077474395697325109818189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436632527596433479757585 4077474395697325109818189)
                      ·
                        rfl

theorem cell23_7940853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7940853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940853 prefixEnd_7940853 := by exact prefixLift 7940853
  have htrace : WordTrace (prefixWord ++ tailWord_7940853) baseStart_7940853 baseEnd_7940853 := by
    simpa [prefixWord, tailWord_7940853, baseEnd_7940853] using wordTrace_append hprefix tailTrace_7940853
  have hstable : (prefixWord ++ tailWord_7940853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940853).length < 2 ^ (prefixWord ++ tailWord_7940853).sum := by decide
  have hdescent : baseEnd_7940853 < baseStart_7940853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940857 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_7940857 : Nat := 118140960795 + 7940857 * 2 ^ 59
def prefixEnd_7940857 : Nat := 4983230072969 + 3 ^ 40 * 7940857 * 2
def baseEnd_7940857 : Nat := 4077476449619943094168169

theorem tailTrace_7940857 : CollatzResearch.WordTrace tailWord_7940857 prefixEnd_7940857 4077476449619943094168169 := by
  unfold tailWord_7940857
  simp only [CollatzResearch.WordTrace]
  refine ⟨289626848592638754248876825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193084565728425836165917883 289626848592638754248876825)
  ·
    refine ⟨217220136444479065686657619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289626848592638754248876825 217220136444479065686657619)
    ·
      refine ⟨325830204666718598529986429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217220136444479065686657619 325830204666718598529986429)
      ·
        refine ⟨122186326750019474448744911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325830204666718598529986429 122186326750019474448744911)
        ·
          refine ⟨183279490125029211673117367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122186326750019474448744911 183279490125029211673117367)
          ·
            refine ⟨274919235187543817509676051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183279490125029211673117367 274919235187543817509676051)
            ·
              refine ⟨412378852781315726264514077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274919235187543817509676051 412378852781315726264514077)
              ·
                refine ⟨154642069792993397349192779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412378852781315726264514077 154642069792993397349192779)
                ·
                  refine ⟨231963104689490096023789169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154642069792993397349192779 231963104689490096023789169)
                  ·
                    refine ⟨173972328517117572017841877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231963104689490096023789169 173972328517117572017841877)
                    ·
                      refine ⟨4077476449619943094168169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173972328517117572017841877 4077476449619943094168169)
                      ·
                        rfl

theorem cell23_7940857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_7940857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940857 prefixEnd_7940857 := by exact prefixLift 7940857
  have htrace : WordTrace (prefixWord ++ tailWord_7940857) baseStart_7940857 baseEnd_7940857 := by
    simpa [prefixWord, tailWord_7940857, baseEnd_7940857] using wordTrace_append hprefix tailTrace_7940857
  have hstable : (prefixWord ++ tailWord_7940857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940857).length < 2 ^ (prefixWord ++ tailWord_7940857).sum := by decide
  have hdescent : baseEnd_7940857 < baseStart_7940857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940858 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2]
def baseStart_7940858 : Nat := 118140960795 + 7940858 * 2 ^ 59
def prefixEnd_7940858 : Nat := 4983230072969 + 3 ^ 40 * 7940858 * 2
def baseEnd_7940858 : Nat := 4077476963100597590255665

theorem tailTrace_7940858 : CollatzResearch.WordTrace tailWord_7940858 prefixEnd_7940858 4077476963100597590255665 := by
  unfold tailWord_7940858
  simp only [CollatzResearch.WordTrace]
  refine ⟨72406721266408782854915807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193084590043756754279775485 72406721266408782854915807)
  ·
    refine ⟨108610081899613174282373711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72406721266408782854915807 108610081899613174282373711)
    ·
      refine ⟨162915122849419761423560567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108610081899613174282373711 162915122849419761423560567)
      ·
        refine ⟨244372684274129642135340851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162915122849419761423560567 244372684274129642135340851)
        ·
          refine ⟨366559026411194463203011277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244372684274129642135340851 366559026411194463203011277)
          ·
            refine ⟨137459634904197923701129229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366559026411194463203011277 137459634904197923701129229)
            ·
              refine ⟨51547363089074221387923461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137459634904197923701129229 51547363089074221387923461)
              ·
                refine ⟨9665130579201416510235649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51547363089074221387923461 9665130579201416510235649)
                ·
                  refine ⟨7248847934401062382676737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9665130579201416510235649 7248847934401062382676737)
                  ·
                    refine ⟨5436635950800796787007553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7248847934401062382676737 5436635950800796787007553)
                    ·
                      refine ⟨4077476963100597590255665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436635950800796787007553 4077476963100597590255665)
                      ·
                        rfl

theorem cell23_7940858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_7940858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940858 prefixEnd_7940858 := by exact prefixLift 7940858
  have htrace : WordTrace (prefixWord ++ tailWord_7940858) baseStart_7940858 baseEnd_7940858 := by
    simpa [prefixWord, tailWord_7940858, baseEnd_7940858] using wordTrace_append hprefix tailTrace_7940858
  have hstable : (prefixWord ++ tailWord_7940858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940858).length < 2 ^ (prefixWord ++ tailWord_7940858).sum := by decide
  have hdescent : baseEnd_7940858 < baseStart_7940858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940867 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8]
def baseStart_7940867 : Nat := 118140960795 + 7940867 * 2 ^ 59
def prefixEnd_7940867 : Nat := 4983230072969 + 3 ^ 40 * 7940867 * 2
def baseEnd_7940867 : Nat := 4077481584426488055043123

theorem tailTrace_7940867 : CollatzResearch.WordTrace tailWord_7940867 prefixEnd_7940867 4077481584426488055043123 := by
  unfold tailWord_7940867
  simp only [CollatzResearch.WordTrace]
  refine ⟨289627213322602525956740855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193084808881735017304493903 289627213322602525956740855)
  ·
    refine ⟨434440819983903788935111283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289627213322602525956740855 434440819983903788935111283)
    ·
      refine ⟨651661229975855683402666925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434440819983903788935111283 651661229975855683402666925)
      ·
        refine ⟨244372961240945881276000097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651661229975855683402666925 244372961240945881276000097)
        ·
          refine ⟨183279720930709410957000073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244372961240945881276000097 183279720930709410957000073)
          ·
            refine ⟨137459790698032058217750055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183279720930709410957000073 137459790698032058217750055)
            ·
              refine ⟨206189686047048087326625083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137459790698032058217750055 206189686047048087326625083)
              ·
                refine ⟨309284529070572130989937625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206189686047048087326625083 309284529070572130989937625)
                ·
                  refine ⟨231963396802929098242453219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309284529070572130989937625 231963396802929098242453219)
                  ·
                    refine ⟨347945095204393647363679829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231963396802929098242453219 347945095204393647363679829)
                    ·
                      refine ⟨4077481584426488055043123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 347945095204393647363679829 4077481584426488055043123)
                      ·
                        rfl

theorem cell23_7940867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_7940867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940867 prefixEnd_7940867 := by exact prefixLift 7940867
  have htrace : WordTrace (prefixWord ++ tailWord_7940867) baseStart_7940867 baseEnd_7940867 := by
    simpa [prefixWord, tailWord_7940867, baseEnd_7940867] using wordTrace_append hprefix tailTrace_7940867
  have hstable : (prefixWord ++ tailWord_7940867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940867).length < 2 ^ (prefixWord ++ tailWord_7940867).sum := by decide
  have hdescent : baseEnd_7940867 < baseStart_7940867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940871 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7940871 : Nat := 118140960795 + 7940871 * 2 ^ 59
def prefixEnd_7940871 : Nat := 4983230072969 + 3 ^ 40 * 7940871 * 2
def baseEnd_7940871 : Nat := 4077483638349106039393105

theorem tailTrace_7940871 : CollatzResearch.WordTrace tailWord_7940871 prefixEnd_7940871 4077483638349106039393105 := by
  unfold tailWord_7940871
  simp only [CollatzResearch.WordTrace]
  refine ⟨289627359214588034639886467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193084906143058689759924311 289627359214588034639886467)
  ·
    refine ⟨434441038821882051959829701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289627359214588034639886467 434441038821882051959829701)
    ·
      refine ⟨81457694779102884742468069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434441038821882051959829701 81457694779102884742468069)
      ·
        refine ⟨15273317771081790889212763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81457694779102884742468069 15273317771081790889212763)
        ·
          refine ⟨22909976656622686333819145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15273317771081790889212763 22909976656622686333819145)
          ·
            refine ⟨17182482492467014750364359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22909976656622686333819145 17182482492467014750364359)
            ·
              refine ⟨25773723738700522125546539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182482492467014750364359 25773723738700522125546539)
              ·
                refine ⟨38660585608050783188319809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25773723738700522125546539 38660585608050783188319809)
                ·
                  refine ⟨28995439206038087391239857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38660585608050783188319809 28995439206038087391239857)
                  ·
                    refine ⟨21746579404528565543429893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28995439206038087391239857 21746579404528565543429893)
                    ·
                      refine ⟨4077483638349106039393105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21746579404528565543429893 4077483638349106039393105)
                      ·
                        rfl

theorem cell23_7940871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7940871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940871 prefixEnd_7940871 := by exact prefixLift 7940871
  have htrace : WordTrace (prefixWord ++ tailWord_7940871) baseStart_7940871 baseEnd_7940871 := by
    simpa [prefixWord, tailWord_7940871, baseEnd_7940871] using wordTrace_append hprefix tailTrace_7940871
  have hstable : (prefixWord ++ tailWord_7940871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940871).length < 2 ^ (prefixWord ++ tailWord_7940871).sum := by decide
  have hdescent : baseEnd_7940871 < baseStart_7940871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940898 : List Nat := [3, 3, 1, 1, 2, 3, 2, 3, 5]
def baseStart_7940898 : Nat := 118140960795 + 7940898 * 2 ^ 59
def prefixEnd_7940898 : Nat := 4983230072969 + 3 ^ 40 * 7940898 * 2
def baseEnd_7940898 : Nat := 453055278036308603750609

theorem tailTrace_7940898 : CollatzResearch.WordTrace tailWord_7940898 prefixEnd_7940898 453055278036308603750609 := by
  unfold tailWord_7940898
  simp only [CollatzResearch.WordTrace]
  refine ⟨72407085996372554562779837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193085562656993478834079565 72407085996372554562779837)
  ·
    refine ⟨27152657248639707961042439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72407085996372554562779837 27152657248639707961042439)
    ·
      refine ⟨40728985872959561941563659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27152657248639707961042439 40728985872959561941563659)
      ·
        refine ⟨61093478809439342912345489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40728985872959561941563659 61093478809439342912345489)
        ·
          refine ⟨45820109107079507184259117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61093478809439342912345489 45820109107079507184259117)
          ·
            refine ⟨17182540915154815194097169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45820109107079507184259117 17182540915154815194097169)
            ·
              refine ⟨12886905686366111395572877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17182540915154815194097169 12886905686366111395572877)
              ·
                refine ⟨4832589632387291773339829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12886905686366111395572877 4832589632387291773339829)
                ·
                  refine ⟨453055278036308603750609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832589632387291773339829 453055278036308603750609)
                  ·
                    rfl

theorem cell23_7940898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_7940898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940898 prefixEnd_7940898 := by exact prefixLift 7940898
  have htrace : WordTrace (prefixWord ++ tailWord_7940898) baseStart_7940898 baseEnd_7940898 := by
    simpa [prefixWord, tailWord_7940898, baseEnd_7940898] using wordTrace_append hprefix tailTrace_7940898
  have hstable : (prefixWord ++ tailWord_7940898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940898).length < 2 ^ (prefixWord ++ tailWord_7940898).sum := by decide
  have hdescent : baseEnd_7940898 < baseStart_7940898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940931 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 2, 4, 2]
def baseStart_7940931 : Nat := 118140960795 + 7940931 * 2 ^ 59
def prefixEnd_7940931 : Nat := 4983230072969 + 3 ^ 40 * 7940931 * 2
def baseEnd_7940931 : Nat := 4077514447188375804642829

theorem tailTrace_7940931 : CollatzResearch.WordTrace tailWord_7940931 prefixEnd_7940931 4077514447188375804642829 := by
  unfold tailWord_7940931
  simp only [CollatzResearch.WordTrace]
  refine ⟨289629547594370664887070647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193086365062913776591380431 289629547594370664887070647)
  ·
    refine ⟨434444321391555997330605971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289629547594370664887070647 434444321391555997330605971)
    ·
      refine ⟨651666482087333995995908957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434444321391555997330605971 651666482087333995995908957)
      ·
        refine ⟨244374930782750248498465859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651666482087333995995908957 244374930782750248498465859)
        ·
          refine ⟨366562396174125372747698789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244374930782750248498465859 366562396174125372747698789)
          ·
            refine ⟨68730449282648507390193523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366562396174125372747698789 68730449282648507390193523)
            ·
              refine ⟨103095673923972761085290285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68730449282648507390193523 103095673923972761085290285)
              ·
                refine ⟨38660877721489785406983857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103095673923972761085290285 38660877721489785406983857)
                ·
                  refine ⟨28995658291117339055237893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38660877721489785406983857 28995658291117339055237893)
                  ·
                    refine ⟨5436685929584501072857105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28995658291117339055237893 5436685929584501072857105)
                    ·
                      refine ⟨4077514447188375804642829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436685929584501072857105 4077514447188375804642829)
                      ·
                        rfl

theorem cell23_7940931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_7940931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940931 prefixEnd_7940931 := by exact prefixLift 7940931
  have htrace : WordTrace (prefixWord ++ tailWord_7940931) baseStart_7940931 baseEnd_7940931 := by
    simpa [prefixWord, tailWord_7940931, baseEnd_7940931] using wordTrace_append hprefix tailTrace_7940931
  have hstable : (prefixWord ++ tailWord_7940931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940931).length < 2 ^ (prefixWord ++ tailWord_7940931).sum := by decide
  have hdescent : baseEnd_7940931 < baseStart_7940931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940951 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_7940951 : Nat := 118140960795 + 7940951 * 2 ^ 59
def prefixEnd_7940951 : Nat := 4983230072969 + 3 ^ 40 * 7940951 * 2
def baseEnd_7940951 : Nat := 4077524716801465726392737

theorem tailTrace_7940951 : CollatzResearch.WordTrace tailWord_7940951 prefixEnd_7940951 4077524716801465726392737 := by
  unfold tailWord_7940951
  simp only [CollatzResearch.WordTrace]
  refine ⟨289630277054298208302798707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193086851369532138868532471 289630277054298208302798707)
  ·
    refine ⟨434445415581447312454198061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289630277054298208302798707 434445415581447312454198061)
    ·
      refine ⟨162917030843042742170324273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434445415581447312454198061 162917030843042742170324273)
      ·
        refine ⟨122187773132282056627743205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162917030843042742170324273 122187773132282056627743205)
        ·
          refine ⟨22910207462302885617701851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122187773132282056627743205 22910207462302885617701851)
          ·
            refine ⟨34365311193454328426552777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22910207462302885617701851 34365311193454328426552777)
            ·
              refine ⟨25773983395090746319914583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34365311193454328426552777 25773983395090746319914583)
              ·
                refine ⟨38660975092636119479871875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25773983395090746319914583 38660975092636119479871875)
                ·
                  refine ⟨57991462638954179219807813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38660975092636119479871875 57991462638954179219807813)
                  ·
                    refine ⟨10873399244803908603713965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57991462638954179219807813 10873399244803908603713965)
                    ·
                      refine ⟨4077524716801465726392737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10873399244803908603713965 4077524716801465726392737)
                      ·
                        rfl

theorem cell23_7940951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_7940951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940951 prefixEnd_7940951 := by exact prefixLift 7940951
  have htrace : WordTrace (prefixWord ++ tailWord_7940951) baseStart_7940951 baseEnd_7940951 := by
    simpa [prefixWord, tailWord_7940951, baseEnd_7940951] using wordTrace_append hprefix tailTrace_7940951
  have hstable : (prefixWord ++ tailWord_7940951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940951).length < 2 ^ (prefixWord ++ tailWord_7940951).sum := by decide
  have hdescent : baseEnd_7940951 < baseStart_7940951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940954 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 8]
def baseStart_7940954 : Nat := 118140960795 + 7940954 * 2 ^ 59
def prefixEnd_7940954 : Nat := 4983230072969 + 3 ^ 40 * 7940954 * 2
def baseEnd_7940954 : Nat := 453058473027047690517247

theorem tailTrace_7940954 : CollatzResearch.WordTrace tailWord_7940954 prefixEnd_7940954 453058473027047690517247 := by
  unfold tailWord_7940954
  simp only [CollatzResearch.WordTrace]
  refine ⟨72407596618321834953789479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193086924315524893210105277 72407596618321834953789479)
  ·
    refine ⟨108611394927482752430684219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72407596618321834953789479 108611394927482752430684219)
    ·
      refine ⟨162917092391224128646026329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108611394927482752430684219 162917092391224128646026329)
      ·
        refine ⟨122187819293418096484519747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162917092391224128646026329 122187819293418096484519747)
        ·
          refine ⟨183281728940127144726779621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122187819293418096484519747 183281728940127144726779621)
          ·
            refine ⟨34365324176273839636271179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183281728940127144726779621 34365324176273839636271179)
            ·
              refine ⟨51547986264410759454406769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34365324176273839636271179 51547986264410759454406769)
              ·
                refine ⟨38660989698308069590805077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51547986264410759454406769 38660989698308069590805077)
                ·
                  refine ⟨453058473027047690517247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38660989698308069590805077 453058473027047690517247)
                  ·
                    rfl

theorem cell23_7940954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_7940954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940954 prefixEnd_7940954 := by exact prefixLift 7940954
  have htrace : WordTrace (prefixWord ++ tailWord_7940954) baseStart_7940954 baseEnd_7940954 := by
    simpa [prefixWord, tailWord_7940954, baseEnd_7940954] using wordTrace_append hprefix tailTrace_7940954
  have hstable : (prefixWord ++ tailWord_7940954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940954).length < 2 ^ (prefixWord ++ tailWord_7940954).sum := by decide
  have hdescent : baseEnd_7940954 < baseStart_7940954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940968 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7940968 : Nat := 118140960795 + 7940968 * 2 ^ 59
def prefixEnd_7940968 : Nat := 4983230072969 + 3 ^ 40 * 7940968 * 2
def baseEnd_7940968 : Nat := 4077533445972592159880159

theorem tailTrace_7940968 : CollatzResearch.WordTrace tailWord_7940968 prefixEnd_7940968 4077533445972592159880159 := by
  unfold tailWord_7940968
  simp only [CollatzResearch.WordTrace]
  refine ⟨144815448547618310103083779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193087264730157746804111705 144815448547618310103083779)
  ·
    refine ⟨217223172821427465154625669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144815448547618310103083779 217223172821427465154625669)
    ·
      refine ⟨40729344904017649716492313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217223172821427465154625669 40729344904017649716492313)
      ·
        refine ⟨30547008678013237287369235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40729344904017649716492313 30547008678013237287369235)
        ·
          refine ⟨45820513017019855931053853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30547008678013237287369235 45820513017019855931053853)
          ·
            refine ⟨17182692381382445974145195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45820513017019855931053853 17182692381382445974145195)
            ·
              refine ⟨25774038572073668961217793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182692381382445974145195 25774038572073668961217793)
              ·
                refine ⟨19330528929055251720913345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25774038572073668961217793 19330528929055251720913345)
                ·
                  refine ⟨14497896696791438790685009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19330528929055251720913345 14497896696791438790685009)
                  ·
                    refine ⟨10873422522593579093013757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14497896696791438790685009 10873422522593579093013757)
                    ·
                      refine ⟨4077533445972592159880159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10873422522593579093013757 4077533445972592159880159)
                      ·
                        rfl

theorem cell23_7940968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7940968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940968 prefixEnd_7940968 := by exact prefixLift 7940968
  have htrace : WordTrace (prefixWord ++ tailWord_7940968) baseStart_7940968 baseEnd_7940968 := by
    simpa [prefixWord, tailWord_7940968, baseEnd_7940968] using wordTrace_append hprefix tailTrace_7940968
  have hstable : (prefixWord ++ tailWord_7940968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940968).length < 2 ^ (prefixWord ++ tailWord_7940968).sum := by decide
  have hdescent : baseEnd_7940968 < baseStart_7940968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7940991 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 3, 5, 2]
def baseStart_7940991 : Nat := 118140960795 + 7940991 * 2 ^ 59
def prefixEnd_7940991 : Nat := 4983230072969 + 3 ^ 40 * 7940991 * 2
def baseEnd_7940991 : Nat := 4077545256027645569892553

theorem tailTrace_7940991 : CollatzResearch.WordTrace tailWord_7940991 prefixEnd_7940991 4077545256027645569892553 := by
  unfold tailWord_7940991
  simp only [CollatzResearch.WordTrace]
  refine ⟨289631735974153295134254827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193087823982768863422836551 289631735974153295134254827)
  ·
    refine ⟨434447603961229942701382241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289631735974153295134254827 434447603961229942701382241)
    ·
      refine ⟨325835702970922457026036681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434447603961229942701382241 325835702970922457026036681)
      ·
        refine ⟨244376777228191842769527511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325835702970922457026036681 244376777228191842769527511)
        ·
          refine ⟨366565165842287764154291267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244376777228191842769527511 366565165842287764154291267)
          ·
            refine ⟨549847748763431646231436901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366565165842287764154291267 549847748763431646231436901)
            ·
              refine ⟨103096452893143433668394419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 549847748763431646231436901 103096452893143433668394419)
              ·
                refine ⟨154644679339715150502591629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103096452893143433668394419 154644679339715150502591629)
                ·
                  refine ⟨57991754752393181438471861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154644679339715150502591629 57991754752393181438471861)
                  ·
                    refine ⟨5436727008036860759856737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57991754752393181438471861 5436727008036860759856737)
                    ·
                      refine ⟨4077545256027645569892553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436727008036860759856737 4077545256027645569892553)
                      ·
                        rfl

theorem cell23_7940991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_7940991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7940991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7940991 prefixEnd_7940991 := by exact prefixLift 7940991
  have htrace : WordTrace (prefixWord ++ tailWord_7940991) baseStart_7940991 baseEnd_7940991 := by
    simpa [prefixWord, tailWord_7940991, baseEnd_7940991] using wordTrace_append hprefix tailTrace_7940991
  have hstable : (prefixWord ++ tailWord_7940991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7940991).length < 2 ^ (prefixWord ++ tailWord_7940991).sum := by decide
  have hdescent : baseEnd_7940991 < baseStart_7940991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7940991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941001 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 3, 5]
def baseStart_7941001 : Nat := 118140960795 + 7941001 * 2 ^ 59
def prefixEnd_7941001 : Nat := 4983230072969 + 3 ^ 40 * 7941001 * 2
def baseEnd_7941001 : Nat := 1359183463611396843589169

theorem tailTrace_7941001 : CollatzResearch.WordTrace tailWord_7941001 prefixEnd_7941001 1359183463611396843589169 := by
  unfold tailWord_7941001
  simp only [CollatzResearch.WordTrace]
  refine ⟨289632100704117066842118857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193088067136078044561412571 289632100704117066842118857)
  ·
    refine ⟨217224075528087800131589143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289632100704117066842118857 217224075528087800131589143)
    ·
      refine ⟨325836113292131700197383715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217224075528087800131589143 325836113292131700197383715)
      ·
        refine ⟨488754169938197550296075573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325836113292131700197383715 488754169938197550296075573)
        ·
          refine ⟨45820703431706020340257085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 488754169938197550296075573 45820703431706020340257085)
          ·
            refine ⟨17182763786889757627596407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45820703431706020340257085 17182763786889757627596407)
            ·
              refine ⟨25774145680334636441394611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182763786889757627596407 25774145680334636441394611)
              ·
                refine ⟨38661218520501954662091917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25774145680334636441394611 38661218520501954662091917)
                ·
                  refine ⟨14497956945188232998284469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38661218520501954662091917 14497956945188232998284469)
                  ·
                    refine ⟨1359183463611396843589169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14497956945188232998284469 1359183463611396843589169)
                    ·
                      rfl

theorem cell23_7941001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_7941001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941001 prefixEnd_7941001 := by exact prefixLift 7941001
  have htrace : WordTrace (prefixWord ++ tailWord_7941001) baseStart_7941001 baseEnd_7941001 := by
    simpa [prefixWord, tailWord_7941001, baseEnd_7941001] using wordTrace_append hprefix tailTrace_7941001
  have hstable : (prefixWord ++ tailWord_7941001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941001).length < 2 ^ (prefixWord ++ tailWord_7941001).sum := by decide
  have hdescent : baseEnd_7941001 < baseStart_7941001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941015 : List Nat := [1, 1, 3, 3, 1, 2, 2, 5, 1, 1, 3]
def baseStart_7941015 : Nat := 118140960795 + 7941015 * 2 ^ 59
def prefixEnd_7941015 : Nat := 4983230072969 + 3 ^ 40 * 7941015 * 2
def baseEnd_7941015 : Nat := 4077557579563353475992443

theorem tailTrace_7941015 : CollatzResearch.WordTrace tailWord_7941015 prefixEnd_7941015 4077557579563353475992443 := by
  unfold tailWord_7941015
  simp only [CollatzResearch.WordTrace]
  refine ⟨289632611326066347233128499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193088407550710898155418999 289632611326066347233128499)
  ·
    refine ⟨434448916989099520849692749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289632611326066347233128499 434448916989099520849692749)
    ·
      refine ⟨162918343870912320318634781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434448916989099520849692749 162918343870912320318634781)
      ·
        refine ⟨61094378951592120119488043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162918343870912320318634781 61094378951592120119488043)
        ·
          refine ⟨91641568427388180179232065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61094378951592120119488043 91641568427388180179232065)
          ·
            refine ⟨68731176320541135134424049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91641568427388180179232065 68731176320541135134424049)
            ·
              refine ⟨51548382240405851350818037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68731176320541135134424049 51548382240405851350818037)
              ·
                refine ⟨4832660835038048564139191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51548382240405851350818037 4832660835038048564139191)
                ·
                  refine ⟨7248991252557072846208787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832660835038048564139191 7248991252557072846208787)
                  ·
                    refine ⟨10873486878835609269313181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7248991252557072846208787 10873486878835609269313181)
                    ·
                      refine ⟨4077557579563353475992443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10873486878835609269313181 4077557579563353475992443)
                      ·
                        rfl

theorem cell23_7941015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_7941015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941015 prefixEnd_7941015 := by exact prefixLift 7941015
  have htrace : WordTrace (prefixWord ++ tailWord_7941015) baseStart_7941015 baseEnd_7941015 := by
    simpa [prefixWord, tailWord_7941015, baseEnd_7941015] using wordTrace_append hprefix tailTrace_7941015
  have hstable : (prefixWord ++ tailWord_7941015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941015).length < 2 ^ (prefixWord ++ tailWord_7941015).sum := by decide
  have hdescent : baseEnd_7941015 < baseStart_7941015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941025 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7941025 : Nat := 118140960795 + 7941025 * 2 ^ 59
def prefixEnd_7941025 : Nat := 4983230072969 + 3 ^ 40 * 7941025 * 2
def baseEnd_7941025 : Nat := 4077562714369898436867397

theorem tailTrace_7941025 : CollatzResearch.WordTrace tailWord_7941025 prefixEnd_7941025 4077562714369898436867397 := by
  unfold tailWord_7941025
  simp only [CollatzResearch.WordTrace]
  refine ⟨289632976056030118940992529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193088650704020079293995019 289632976056030118940992529)
  ·
    refine ⟨217224732042022589205744397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289632976056030118940992529 217224732042022589205744397)
    ·
      refine ⟨81459274515758470952154149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217224732042022589205744397 81459274515758470952154149)
      ·
        refine ⟨15273613971704713303528903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81459274515758470952154149 15273613971704713303528903)
        ·
          refine ⟨22910420957557069955293355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15273613971704713303528903 22910420957557069955293355)
          ·
            refine ⟨34365631436335604932940033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22910420957557069955293355 34365631436335604932940033)
            ·
              refine ⟨25774223577251703699705025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34365631436335604932940033 25774223577251703699705025)
              ·
                refine ⟨19330667682938777774778769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25774223577251703699705025 19330667682938777774778769)
                ·
                  refine ⟨14498000762204083331084077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19330667682938777774778769 14498000762204083331084077)
                  ·
                    refine ⟨5436750285826531249156529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14498000762204083331084077 5436750285826531249156529)
                    ·
                      refine ⟨4077562714369898436867397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436750285826531249156529 4077562714369898436867397)
                      ·
                        rfl

theorem cell23_7941025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7941025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941025 prefixEnd_7941025 := by exact prefixLift 7941025
  have htrace : WordTrace (prefixWord ++ tailWord_7941025) baseStart_7941025 baseEnd_7941025 := by
    simpa [prefixWord, tailWord_7941025, baseEnd_7941025] using wordTrace_append hprefix tailTrace_7941025
  have hstable : (prefixWord ++ tailWord_7941025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941025).length < 2 ^ (prefixWord ++ tailWord_7941025).sum := by decide
  have hdescent : baseEnd_7941025 < baseStart_7941025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941048 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 2, 4]
def baseStart_7941048 : Nat := 118140960795 + 7941048 * 2 ^ 59
def prefixEnd_7941048 : Nat := 4983230072969 + 3 ^ 40 * 7941048 * 2
def baseEnd_7941048 : Nat := 1359191508141650615626597

theorem tailTrace_7941048 : CollatzResearch.WordTrace tailWord_7941048 prefixEnd_7941048 1359191508141650615626597 := by
  unfold tailWord_7941048
  simp only [CollatzResearch.WordTrace]
  refine ⟨144816907467473396934539899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193089209956631195912719865 144816907467473396934539899)
  ·
    refine ⟨217225361201210095401809849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144816907467473396934539899 217225361201210095401809849)
    ·
      refine ⟨162919020900907571551357387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217225361201210095401809849 162919020900907571551357387)
      ·
        refine ⟨244378531351361357327036081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162919020900907571551357387 244378531351361357327036081)
        ·
          refine ⟨183283898513521017995277061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244378531351361357327036081 183283898513521017995277061)
          ·
            refine ⟨34365730971285190874114449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183283898513521017995277061 34365730971285190874114449)
            ·
              refine ⟨25774298228463893155585837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34365730971285190874114449 25774298228463893155585837)
              ·
                refine ⟨9665361835673959933344689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25774298228463893155585837 9665361835673959933344689)
                ·
                  refine ⟨7249021376755469950008517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9665361835673959933344689 7249021376755469950008517)
                  ·
                    refine ⟨1359191508141650615626597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249021376755469950008517 1359191508141650615626597)
                    ·
                      rfl

theorem cell23_7941048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_7941048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941048 prefixEnd_7941048 := by exact prefixLift 7941048
  have htrace : WordTrace (prefixWord ++ tailWord_7941048) baseStart_7941048 baseEnd_7941048 := by
    simpa [prefixWord, tailWord_7941048, baseEnd_7941048] using wordTrace_append hprefix tailTrace_7941048
  have hstable : (prefixWord ++ tailWord_7941048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941048).length < 2 ^ (prefixWord ++ tailWord_7941048).sum := by decide
  have hdescent : baseEnd_7941048 < baseStart_7941048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941069 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7941069 : Nat := 118140960795 + 7941069 * 2 ^ 59
def prefixEnd_7941069 : Nat := 4983230072969 + 3 ^ 40 * 7941069 * 2
def baseEnd_7941069 : Nat := 1359195102506232088239065

theorem tailTrace_7941069 : CollatzResearch.WordTrace tailWord_7941069 prefixEnd_7941069 1359195102506232088239065 := by
  unfold tailWord_7941069
  simp only [CollatzResearch.WordTrace]
  refine ⟨289634580867870714455594261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193089720578580476303729507 289634580867870714455594261)
  ·
    refine ⟨13576620978181439740105981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289634580867870714455594261 13576620978181439740105981)
    ·
      refine ⟨5091232866818039902539743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13576620978181439740105981 5091232866818039902539743)
      ·
        refine ⟨7636849300227059853809615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091232866818039902539743 7636849300227059853809615)
        ·
          refine ⟨11455273950340589780714423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7636849300227059853809615 11455273950340589780714423)
          ·
            refine ⟨17182910925510884671071635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455273950340589780714423 17182910925510884671071635)
            ·
              refine ⟨25774366388266327006607453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182910925510884671071635 25774366388266327006607453)
              ·
                refine ⟨9665387395599872627477795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25774366388266327006607453 9665387395599872627477795)
                ·
                  refine ⟨14498081093399808941216693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665387395599872627477795 14498081093399808941216693)
                  ·
                    refine ⟨1359195102506232088239065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14498081093399808941216693 1359195102506232088239065)
                    ·
                      rfl

theorem cell23_7941069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7941069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941069 prefixEnd_7941069 := by exact prefixLift 7941069
  have htrace : WordTrace (prefixWord ++ tailWord_7941069) baseStart_7941069 baseEnd_7941069 := by
    simpa [prefixWord, tailWord_7941069, baseEnd_7941069] using wordTrace_append hprefix tailTrace_7941069
  have hstable : (prefixWord ++ tailWord_7941069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941069).length < 2 ^ (prefixWord ++ tailWord_7941069).sum := by decide
  have hdescent : baseEnd_7941069 < baseStart_7941069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941078 : List Nat := [5, 2, 1, 1, 2, 2, 10]
def baseStart_7941078 : Nat := 118140960795 + 7941078 * 2 ^ 59
def prefixEnd_7941078 : Nat := 4983230072969 + 3 ^ 40 * 7941078 * 2
def baseEnd_7941078 : Nat := 50340616405488725055613

theorem tailTrace_7941078 : CollatzResearch.WordTrace tailWord_7941078 prefixEnd_7941078 50340616405488725055613 := by
  unfold tailWord_7941078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102181820302381812041993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193089939416558739328447925 18102181820302381812041993)
  ·
    refine ⟨13576636365226786359031495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18102181820302381812041993 13576636365226786359031495)
    ·
      refine ⟨20364954547840179538547243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13576636365226786359031495 20364954547840179538547243)
      ·
        refine ⟨30547431821760269307820865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20364954547840179538547243 30547431821760269307820865)
        ·
          refine ⟨22910573866320201980865649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30547431821760269307820865 22910573866320201980865649)
          ·
            refine ⟨17182930399740151485649237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22910573866320201980865649 17182930399740151485649237)
            ·
              refine ⟨50340616405488725055613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17182930399740151485649237 50340616405488725055613)
              ·
                rfl

theorem cell23_7941078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 10].length) (baseStart_7941078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941078 prefixEnd_7941078 := by exact prefixLift 7941078
  have htrace : WordTrace (prefixWord ++ tailWord_7941078) baseStart_7941078 baseEnd_7941078 := by
    simpa [prefixWord, tailWord_7941078, baseEnd_7941078] using wordTrace_append hprefix tailTrace_7941078
  have hstable : (prefixWord ++ tailWord_7941078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941078).length < 2 ^ (prefixWord ++ tailWord_7941078).sum := by decide
  have hdescent : baseEnd_7941078 < baseStart_7941078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941102 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_7941102 : Nat := 118140960795 + 7941102 * 2 ^ 59
def prefixEnd_7941102 : Nat := 4983230072969 + 3 ^ 40 * 7941102 * 2
def baseEnd_7941102 : Nat := 4077602252380294635604543

theorem tailTrace_7941102 : CollatzResearch.WordTrace tailWord_7941102 prefixEnd_7941102 4077602252380294635604543 := by
  unfold tailWord_7941102
  simp only [CollatzResearch.WordTrace]
  refine ⟨36204473059593895136443195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193090522984500774061030373 36204473059593895136443195)
  ·
    refine ⟨54306709589390842704664793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36204473059593895136443195 54306709589390842704664793)
    ·
      refine ⟨40730032192043132028498595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54306709589390842704664793 40730032192043132028498595)
      ·
        refine ⟨61095048288064698042747893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40730032192043132028498595 61095048288064698042747893)
        ·
          refine ⟨5727660777006065441507615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61095048288064698042747893 5727660777006065441507615)
          ·
            refine ⟨8591491165509098162261423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5727660777006065441507615 8591491165509098162261423)
            ·
              refine ⟨12887236748263647243392135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8591491165509098162261423 12887236748263647243392135)
              ·
                refine ⟨19330855122395470865088203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887236748263647243392135 19330855122395470865088203)
                ·
                  refine ⟨28996282683593206297632305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19330855122395470865088203 28996282683593206297632305)
                  ·
                    refine ⟨21747212012694904723224229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28996282683593206297632305 21747212012694904723224229)
                    ·
                      refine ⟨4077602252380294635604543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21747212012694904723224229 4077602252380294635604543)
                      ·
                        rfl

theorem cell23_7941102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_7941102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941102 prefixEnd_7941102 := by exact prefixLift 7941102
  have htrace : WordTrace (prefixWord ++ tailWord_7941102) baseStart_7941102 baseEnd_7941102 := by
    simpa [prefixWord, tailWord_7941102, baseEnd_7941102] using wordTrace_append hprefix tailTrace_7941102
  have hstable : (prefixWord ++ tailWord_7941102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941102).length < 2 ^ (prefixWord ++ tailWord_7941102).sum := by decide
  have hdescent : baseEnd_7941102 < baseStart_7941102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941105 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_7941105 : Nat := 118140960795 + 7941105 * 2 ^ 59
def prefixEnd_7941105 : Nat := 4983230072969 + 3 ^ 40 * 7941105 * 2
def baseEnd_7941105 : Nat := 4077603792822258123867029

theorem tailTrace_7941105 : CollatzResearch.WordTrace tailWord_7941105 prefixEnd_7941105 4077603792822258123867029 := by
  unfold tailWord_7941105
  simp only [CollatzResearch.WordTrace]
  refine ⟨289635893895740292603904769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193090595930493528402603179 289635893895740292603904769)
  ·
    refine ⟨217226920421805219452928577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289635893895740292603904769 217226920421805219452928577)
    ·
      refine ⟨162920190316353914589696433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217226920421805219452928577 162920190316353914589696433)
      ·
        refine ⟨122190142737265435942272325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162920190316353914589696433 122190142737265435942272325)
        ·
          refine ⟨22910651763237269239176061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122190142737265435942272325 22910651763237269239176061)
          ·
            refine ⟨8591494411213975964691023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22910651763237269239176061 8591494411213975964691023)
            ·
              refine ⟨12887241616820963947036535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8591494411213975964691023 12887241616820963947036535)
              ·
                refine ⟨19330862425231445920554803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887241616820963947036535 19330862425231445920554803)
                ·
                  refine ⟨28996293637847168880832205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19330862425231445920554803 28996293637847168880832205)
                  ·
                    refine ⟨10873610114192688330312077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28996293637847168880832205 10873610114192688330312077)
                    ·
                      refine ⟨4077603792822258123867029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10873610114192688330312077 4077603792822258123867029)
                      ·
                        rfl

theorem cell23_7941105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_7941105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941105 prefixEnd_7941105 := by exact prefixLift 7941105
  have htrace : WordTrace (prefixWord ++ tailWord_7941105) baseStart_7941105 baseEnd_7941105 := by
    simpa [prefixWord, tailWord_7941105, baseEnd_7941105] using wordTrace_append hprefix tailTrace_7941105
  have hstable : (prefixWord ++ tailWord_7941105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941105).length < 2 ^ (prefixWord ++ tailWord_7941105).sum := by decide
  have hdescent : baseEnd_7941105 < baseStart_7941105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941109 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7941109 : Nat := 118140960795 + 7941109 * 2 ^ 59
def prefixEnd_7941109 : Nat := 4983230072969 + 3 ^ 40 * 7941109 * 2
def baseEnd_7941109 : Nat := 4077605846744876108217011

theorem tailTrace_7941109 : CollatzResearch.WordTrace tailWord_7941109 prefixEnd_7941109 4077605846744876108217011 := by
  unfold tailWord_7941109
  simp only [CollatzResearch.WordTrace]
  refine ⟨289636039787725801287050381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193090693191817200858033587 289636039787725801287050381)
  ·
    refine ⟨108613514920397175482643893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289636039787725801287050381 108613514920397175482643893)
    ·
      refine ⟨10182517023787235201497865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108613514920397175482643893 10182517023787235201497865)
      ·
        refine ⟨7636887767840426401123399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10182517023787235201497865 7636887767840426401123399)
        ·
          refine ⟨11455331651760639601685099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7636887767840426401123399 11455331651760639601685099)
          ·
            refine ⟨17182997477640959402527649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455331651760639601685099 17182997477640959402527649)
            ·
              refine ⟨12887248108230719551895737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17182997477640959402527649 12887248108230719551895737)
              ·
                refine ⟨9665436081173039663921803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12887248108230719551895737 9665436081173039663921803)
                ·
                  refine ⟨14498154121759559495882705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665436081173039663921803 14498154121759559495882705)
                  ·
                    refine ⟨10873615591319669621912029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14498154121759559495882705 10873615591319669621912029)
                    ·
                      refine ⟨4077605846744876108217011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10873615591319669621912029 4077605846744876108217011)
                      ·
                        rfl

theorem cell23_7941109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7941109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941109 prefixEnd_7941109 := by exact prefixLift 7941109
  have htrace : WordTrace (prefixWord ++ tailWord_7941109) baseStart_7941109 baseEnd_7941109 := by
    simpa [prefixWord, tailWord_7941109, baseEnd_7941109] using wordTrace_append hprefix tailTrace_7941109
  have hstable : (prefixWord ++ tailWord_7941109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941109).length < 2 ^ (prefixWord ++ tailWord_7941109).sum := by decide
  have hdescent : baseEnd_7941109 < baseStart_7941109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941131 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5]
def baseStart_7941131 : Nat := 118140960795 + 7941131 * 2 ^ 59
def prefixEnd_7941131 : Nat := 4983230072969 + 3 ^ 40 * 7941131 * 2
def baseEnd_7941131 : Nat := 4077617143319275022141909

theorem tailTrace_7941131 : CollatzResearch.WordTrace tailWord_7941131 prefixEnd_7941131 4077617143319275022141909 := by
  unfold tailWord_7941131
  simp only [CollatzResearch.WordTrace]
  refine ⟨289636842193646099044351247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193091228129097399362900831 289636842193646099044351247)
  ·
    refine ⟨434455263290469148566526871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289636842193646099044351247 434455263290469148566526871)
    ·
      refine ⟨651682894935703722849790307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434455263290469148566526871 651682894935703722849790307)
      ·
        refine ⟨977524342403555584274685461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651682894935703722849790307 977524342403555584274685461)
        ·
          refine ⟨45821453550166668012875881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 977524342403555584274685461 45821453550166668012875881)
          ·
            refine ⟨34366090162625001009656911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45821453550166668012875881 34366090162625001009656911)
            ·
              refine ⟨51549135243937501514485367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34366090162625001009656911 51549135243937501514485367)
              ·
                refine ⟨77323702865906252271728051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51549135243937501514485367 77323702865906252271728051)
                ·
                  refine ⟨115985554298859378407592077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77323702865906252271728051 115985554298859378407592077)
                  ·
                    refine ⟨43494582862072266902847029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115985554298859378407592077 43494582862072266902847029)
                    ·
                      refine ⟨4077617143319275022141909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43494582862072266902847029 4077617143319275022141909)
                      ·
                        rfl

theorem cell23_7941131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_7941131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941131 prefixEnd_7941131 := by exact prefixLift 7941131
  have htrace : WordTrace (prefixWord ++ tailWord_7941131) baseStart_7941131 baseEnd_7941131 := by
    simpa [prefixWord, tailWord_7941131, baseEnd_7941131] using wordTrace_append hprefix tailTrace_7941131
  have hstable : (prefixWord ++ tailWord_7941131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941131).length < 2 ^ (prefixWord ++ tailWord_7941131).sum := by decide
  have hdescent : baseEnd_7941131 < baseStart_7941131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941145 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 4, 2, 2]
def baseStart_7941145 : Nat := 118140960795 + 7941145 * 2 ^ 59
def prefixEnd_7941145 : Nat := 4983230072969 + 3 ^ 40 * 7941145 * 2
def baseEnd_7941145 : Nat := 4077624332048437967366845

theorem tailTrace_7941145 : CollatzResearch.WordTrace tailWord_7941145 prefixEnd_7941145 4077624332048437967366845 := by
  unfold tailWord_7941145
  simp only [CollatzResearch.WordTrace]
  refine ⟨289637352815595379435360889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193091568543730252956907259 289637352815595379435360889)
  ·
    refine ⟨217228014611696534576520667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289637352815595379435360889 217228014611696534576520667)
    ·
      refine ⟨325842021917544801864781001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217228014611696534576520667 325842021917544801864781001)
      ·
        refine ⟨244381516438158601398585751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325842021917544801864781001 244381516438158601398585751)
        ·
          refine ⟨366572274657237902097878627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244381516438158601398585751 366572274657237902097878627)
          ·
            refine ⟨549858411985856853146817941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366572274657237902097878627 549858411985856853146817941)
            ·
              refine ⟨25774613061837039991257091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 549858411985856853146817941 25774613061837039991257091)
              ·
                refine ⟨38661919592755559986885637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25774613061837039991257091 38661919592755559986885637)
                ·
                  refine ⟨7249109923641667497541057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38661919592755559986885637 7249109923641667497541057)
                  ·
                    refine ⟨5436832442731250623155793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7249109923641667497541057 5436832442731250623155793)
                    ·
                      refine ⟨4077624332048437967366845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436832442731250623155793 4077624332048437967366845)
                      ·
                        rfl

theorem cell23_7941145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_7941145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941145 prefixEnd_7941145 := by exact prefixLift 7941145
  have htrace : WordTrace (prefixWord ++ tailWord_7941145) baseStart_7941145 baseEnd_7941145 := by
    simpa [prefixWord, tailWord_7941145, baseEnd_7941145] using wordTrace_append hprefix tailTrace_7941145
  have hstable : (prefixWord ++ tailWord_7941145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941145).length < 2 ^ (prefixWord ++ tailWord_7941145).sum := by decide
  have hdescent : baseEnd_7941145 < baseStart_7941145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941198 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_7941198 : Nat := 118140960795 + 7941198 * 2 ^ 59
def prefixEnd_7941198 : Nat := 4983230072969 + 3 ^ 40 * 7941198 * 2
def baseEnd_7941198 : Nat := 1359217182174375420001367

theorem tailTrace_7941198 : CollatzResearch.WordTrace tailWord_7941198 prefixEnd_7941198 1359217182174375420001367 := by
  unfold tailWord_7941198
  simp only [CollatzResearch.WordTrace]
  refine ⟨36204910735550421185880031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193092857256268912991360165 36204910735550421185880031)
  ·
    refine ⟨54307366103325631778820047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36204910735550421185880031 54307366103325631778820047)
    ·
      refine ⟨81461049154988447668230071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54307366103325631778820047 81461049154988447668230071)
      ·
        refine ⟨122191573732482671502345107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81461049154988447668230071 122191573732482671502345107)
        ·
          refine ⟨183287360598724007253517661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122191573732482671502345107 183287360598724007253517661)
          ·
            refine ⟨68732760224521502720069123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183287360598724007253517661 68732760224521502720069123)
            ·
              refine ⟨103099140336782254080103685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68732760224521502720069123 103099140336782254080103685)
              ·
                refine ⟨19331088813146672640019441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103099140336782254080103685 19331088813146672640019441)
                ·
                  refine ⟨14498316609860004480014581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19331088813146672640019441 14498316609860004480014581)
                  ·
                    refine ⟨1359217182174375420001367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14498316609860004480014581 1359217182174375420001367)
                    ·
                      rfl

theorem cell23_7941198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_7941198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941198 prefixEnd_7941198 := by exact prefixLift 7941198
  have htrace : WordTrace (prefixWord ++ tailWord_7941198) baseStart_7941198 baseEnd_7941198 := by
    simpa [prefixWord, tailWord_7941198, baseEnd_7941198] using wordTrace_append hprefix tailTrace_7941198
  have hstable : (prefixWord ++ tailWord_7941198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941198).length < 2 ^ (prefixWord ++ tailWord_7941198).sum := by decide
  have hdescent : baseEnd_7941198 < baseStart_7941198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941202 : List Nat := [3, 2, 2, 1, 3, 1, 4, 2, 5]
def baseStart_7941202 : Nat := 118140960795 + 7941202 * 2 ^ 59
def prefixEnd_7941202 : Nat := 4983230072969 + 3 ^ 40 * 7941202 * 2
def baseEnd_7941202 : Nat := 453072622271749360483787

theorem tailTrace_7941202 : CollatzResearch.WordTrace tailWord_7941202 prefixEnd_7941202 453072622271749360483787 := by
  unfold tailWord_7941202
  simp only [CollatzResearch.WordTrace]
  refine ⟨72409857944097219542546465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193092954517592585446790573 72409857944097219542546465)
  ·
    refine ⟨54307393458072914656909849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72409857944097219542546465 54307393458072914656909849)
    ·
      refine ⟨40730545093554685992682387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54307393458072914656909849 40730545093554685992682387)
      ·
        refine ⟨61095817640332028989023581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40730545093554685992682387 61095817640332028989023581)
        ·
          refine ⟨22910931615124510870883843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61095817640332028989023581 22910931615124510870883843)
          ·
            refine ⟨34366397422686766306325765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22910931615124510870883843 34366397422686766306325765)
            ·
              refine ⟨6443699516753768682436081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34366397422686766306325765 6443699516753768682436081)
              ·
                refine ⟨4832774637565326511827061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443699516753768682436081 4832774637565326511827061)
                ·
                  refine ⟨453072622271749360483787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832774637565326511827061 453072622271749360483787)
                  ·
                    rfl

theorem cell23_7941202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_7941202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941202 prefixEnd_7941202 := by exact prefixLift 7941202
  have htrace : WordTrace (prefixWord ++ tailWord_7941202) baseStart_7941202 baseEnd_7941202 := by
    simpa [prefixWord, tailWord_7941202, baseEnd_7941202] using wordTrace_append hprefix tailTrace_7941202
  have hstable : (prefixWord ++ tailWord_7941202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941202).length < 2 ^ (prefixWord ++ tailWord_7941202).sum := by decide
  have hdescent : baseEnd_7941202 < baseStart_7941202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941258 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 8]
def baseStart_7941258 : Nat := 118140960795 + 7941258 * 2 ^ 59
def prefixEnd_7941258 : Nat := 4983230072969 + 3 ^ 40 * 7941258 * 2
def baseEnd_7941258 : Nat := 453075817262488447250425

theorem tailTrace_7941258 : CollatzResearch.WordTrace tailWord_7941258 prefixEnd_7941258 453075817262488447250425 := by
  unfold tailWord_7941258
  simp only [CollatzResearch.WordTrace]
  refine ⟨72410368566046499933556107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193094316176123999822816285 72410368566046499933556107)
  ·
    refine ⟨108615552849069749900334161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72410368566046499933556107 108615552849069749900334161)
    ·
      refine ⟨81461664636802312425250621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108615552849069749900334161 81461664636802312425250621)
      ·
        refine ⟨30548124238800867159468983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81461664636802312425250621 30548124238800867159468983)
        ·
          refine ⟨45822186358201300739203475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30548124238800867159468983 45822186358201300739203475)
          ·
            refine ⟨68733279537301951108805213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45822186358201300739203475 68733279537301951108805213)
            ·
              refine ⟨25774979826488231665801955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68733279537301951108805213 25774979826488231665801955)
              ·
                refine ⟨38662469739732347498702933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25774979826488231665801955 38662469739732347498702933)
                ·
                  refine ⟨453075817262488447250425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38662469739732347498702933 453075817262488447250425)
                  ·
                    rfl

theorem cell23_7941258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_7941258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941258 prefixEnd_7941258 := by exact prefixLift 7941258
  have htrace : WordTrace (prefixWord ++ tailWord_7941258) baseStart_7941258 baseEnd_7941258 := by
    simpa [prefixWord, tailWord_7941258, baseEnd_7941258] using wordTrace_append hprefix tailTrace_7941258
  have hstable : (prefixWord ++ tailWord_7941258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941258).length < 2 ^ (prefixWord ++ tailWord_7941258).sum := by decide
  have hdescent : baseEnd_7941258 < baseStart_7941258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941262 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_7941262 : Nat := 118140960795 + 7941262 * 2 ^ 59
def prefixEnd_7941262 : Nat := 4983230072969 + 3 ^ 40 * 7941262 * 2
def baseEnd_7941262 : Nat := 1359228136428338003201269

theorem tailTrace_7941262 : CollatzResearch.WordTrace tailWord_7941262 prefixEnd_7941262 1359228136428338003201269 := by
  unfold tailWord_7941262
  simp only [CollatzResearch.WordTrace]
  refine ⟨36205202519521438552171255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193094413437447672278246693 36205202519521438552171255)
  ·
    refine ⟨54307803779282157828256883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36205202519521438552171255 54307803779282157828256883)
    ·
      refine ⟨81461705668923236742385325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54307803779282157828256883 81461705668923236742385325)
      ·
        refine ⟨30548139625846213778394497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81461705668923236742385325 30548139625846213778394497)
        ·
          refine ⟨22911104719384660333795873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30548139625846213778394497 22911104719384660333795873)
          ·
            refine ⟨17183328539538495250346905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22911104719384660333795873 17183328539538495250346905)
            ·
              refine ⟨12887496404653871437760179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17183328539538495250346905 12887496404653871437760179)
              ·
                refine ⟨19331244606980807156640269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887496404653871437760179 19331244606980807156640269)
                ·
                  refine ⟨7249216727617802683740101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19331244606980807156640269 7249216727617802683740101)
                  ·
                    refine ⟨1359228136428338003201269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249216727617802683740101 1359228136428338003201269)
                    ·
                      rfl

theorem cell23_7941262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_7941262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941262 prefixEnd_7941262 := by exact prefixLift 7941262
  have htrace : WordTrace (prefixWord ++ tailWord_7941262) baseStart_7941262 baseEnd_7941262 := by
    simpa [prefixWord, tailWord_7941262, baseEnd_7941262] using wordTrace_append hprefix tailTrace_7941262
  have hstable : (prefixWord ++ tailWord_7941262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941262).length < 2 ^ (prefixWord ++ tailWord_7941262).sum := by decide
  have hdescent : baseEnd_7941262 < baseStart_7941262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941295 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 1, 5, 2]
def baseStart_7941295 : Nat := 118140960795 + 7941295 * 2 ^ 59
def prefixEnd_7941295 : Nat := 4983230072969 + 3 ^ 40 * 7941295 * 2
def baseEnd_7941295 : Nat := 4077701354146612380491155

theorem tailTrace_7941295 : CollatzResearch.WordTrace tailWord_7941295 prefixEnd_7941295 4077701354146612380491155 := by
  unfold tailWord_7941295
  simp only [CollatzResearch.WordTrace]
  refine ⟨289642823765051955053321339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193095215843367970035547559 289642823765051955053321339)
  ·
    refine ⟨434464235647577932579982009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289642823765051955053321339 434464235647577932579982009)
    ·
      refine ⟨325848176735683449434986507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434464235647577932579982009 325848176735683449434986507)
      ·
        refine ⟨488772265103525174152479761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325848176735683449434986507 488772265103525174152479761)
        ·
          refine ⟨366579198827643880614359821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488772265103525174152479761 366579198827643880614359821)
          ·
            refine ⟨137467199560366455230384933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366579198827643880614359821 137467199560366455230384933)
            ·
              refine ⟨25775099917568710355697175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137467199560366455230384933 25775099917568710355697175)
              ·
                refine ⟨38662649876353065533545763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25775099917568710355697175 38662649876353065533545763)
                ·
                  refine ⟨57993974814529598300318645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38662649876353065533545763 57993974814529598300318645)
                  ·
                    refine ⟨5436935138862149840654873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57993974814529598300318645 5436935138862149840654873)
                    ·
                      refine ⟨4077701354146612380491155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5436935138862149840654873 4077701354146612380491155)
                      ·
                        rfl

theorem cell23_7941295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5, 2].length) (baseStart_7941295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941295 prefixEnd_7941295 := by exact prefixLift 7941295
  have htrace : WordTrace (prefixWord ++ tailWord_7941295) baseStart_7941295 baseEnd_7941295 := by
    simpa [prefixWord, tailWord_7941295, baseEnd_7941295] using wordTrace_append hprefix tailTrace_7941295
  have hstable : (prefixWord ++ tailWord_7941295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941295).length < 2 ^ (prefixWord ++ tailWord_7941295).sum := by decide
  have hdescent : baseEnd_7941295 < baseStart_7941295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941305 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 1, 5]
def baseStart_7941305 : Nat := 118140960795 + 7941305 * 2 ^ 59
def prefixEnd_7941305 : Nat := 4983230072969 + 3 ^ 40 * 7941305 * 2
def baseEnd_7941305 : Nat := 1359235496317719113788703

theorem tailTrace_7941305 : CollatzResearch.WordTrace tailWord_7941305 prefixEnd_7941305 1359235496317719113788703 := by
  unfold tailWord_7941305
  simp only [CollatzResearch.WordTrace]
  refine ⟨289643188495015726761185369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193095458996677151174123579 289643188495015726761185369)
  ·
    refine ⟨217232391371261795070889027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289643188495015726761185369 217232391371261795070889027)
    ·
      refine ⟨325848587056892692606333541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217232391371261795070889027 325848587056892692606333541)
      ·
        refine ⟨61096610073167379863687539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325848587056892692606333541 61096610073167379863687539)
        ·
          refine ⟨91644915109751069795531309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61096610073167379863687539 91644915109751069795531309)
          ·
            refine ⟨34366843166156651173324241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91644915109751069795531309 34366843166156651173324241)
            ·
              refine ⟨25775132374617488379993181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34366843166156651173324241 25775132374617488379993181)
              ·
                refine ⟨9665674640481558142497443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25775132374617488379993181 9665674640481558142497443)
                ·
                  refine ⟨14498511960722337213746165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665674640481558142497443 14498511960722337213746165)
                  ·
                    refine ⟨1359235496317719113788703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14498511960722337213746165 1359235496317719113788703)
                    ·
                      rfl

theorem cell23_7941305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_7941305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941305 prefixEnd_7941305 := by exact prefixLift 7941305
  have htrace : WordTrace (prefixWord ++ tailWord_7941305) baseStart_7941305 baseEnd_7941305 := by
    simpa [prefixWord, tailWord_7941305, baseEnd_7941305] using wordTrace_append hprefix tailTrace_7941305
  have hstable : (prefixWord ++ tailWord_7941305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941305).length < 2 ^ (prefixWord ++ tailWord_7941305).sum := by decide
  have hdescent : baseEnd_7941305 < baseStart_7941305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941348 : List Nat := [2, 3, 1, 1, 1, 2, 4, 9]
def baseStart_7941348 : Nat := 118140960795 + 7941348 * 2 ^ 59
def prefixEnd_7941348 : Nat := 4983230072969 + 3 ^ 40 * 7941348 * 2
def baseEnd_7941348 : Nat := 151026984023011136041793

theorem tailTrace_7941348 : CollatzResearch.WordTrace tailWord_7941348 prefixEnd_7941348 151026984023011136041793 := by
  unfold tailWord_7941348
  simp only [CollatzResearch.WordTrace]
  refine ⟨144822378416929972552500349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193096504555906630070000465 144822378416929972552500349)
  ·
    refine ⟨54308391906348739707187631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144822378416929972552500349 54308391906348739707187631)
    ·
      refine ⟨81462587859523109560781447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54308391906348739707187631 81462587859523109560781447)
      ·
        refine ⟨122193881789284664341172171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81462587859523109560781447 122193881789284664341172171)
        ·
          refine ⟨183290822683926996511758257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122193881789284664341172171 183290822683926996511758257)
          ·
            refine ⟨137468117012945247383818693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183290822683926996511758257 137468117012945247383818693)
            ·
              refine ⟨25775271939927233884466005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137468117012945247383818693 25775271939927233884466005)
              ·
                refine ⟨151026984023011136041793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25775271939927233884466005 151026984023011136041793)
                ·
                  rfl

theorem cell23_7941348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 9].length) (baseStart_7941348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941348 prefixEnd_7941348 := by exact prefixLift 7941348
  have htrace : WordTrace (prefixWord ++ tailWord_7941348) baseStart_7941348 baseEnd_7941348 := by
    simpa [prefixWord, tailWord_7941348, baseEnd_7941348] using wordTrace_append hprefix tailTrace_7941348
  have hstable : (prefixWord ++ tailWord_7941348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941348).length < 2 ^ (prefixWord ++ tailWord_7941348).sum := by decide
  have hdescent : baseEnd_7941348 < baseStart_7941348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941355 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4]
def baseStart_7941355 : Nat := 118140960795 + 7941355 * 2 ^ 59
def prefixEnd_7941355 : Nat := 4983230072969 + 3 ^ 40 * 7941355 * 2
def baseEnd_7941355 : Nat := 4077732162985882145740879

theorem tailTrace_7941355 : CollatzResearch.WordTrace tailWord_7941355 prefixEnd_7941355 4077732162985882145740879 := by
  unfold tailWord_7941355
  simp only [CollatzResearch.WordTrace]
  refine ⟨289645012144834585300505519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193096674763223056867003679 289645012144834585300505519)
  ·
    refine ⟨434467518217251877950758279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289645012144834585300505519 434467518217251877950758279)
    ·
      refine ⟨651701277325877816926137419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434467518217251877950758279 651701277325877816926137419)
      ·
        refine ⟨977551915988816725389206129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651701277325877816926137419 977551915988816725389206129)
        ·
          refine ⟨733163936991612544041904597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977551915988816725389206129 733163936991612544041904597)
          ·
            refine ⟨17183529773240919000982139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 733163936991612544041904597 17183529773240919000982139)
            ·
              refine ⟨25775294659861378501473209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17183529773240919000982139 25775294659861378501473209)
              ·
                refine ⟨19331470994896033876104907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25775294659861378501473209 19331470994896033876104907)
                ·
                  refine ⟨28997206492344050814157361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19331470994896033876104907 28997206492344050814157361)
                  ·
                    refine ⟨21747904869258038110618021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28997206492344050814157361 21747904869258038110618021)
                    ·
                      refine ⟨4077732162985882145740879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21747904869258038110618021 4077732162985882145740879)
                      ·
                        rfl

theorem cell23_7941355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4].length) (baseStart_7941355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941355 prefixEnd_7941355 := by exact prefixLift 7941355
  have htrace : WordTrace (prefixWord ++ tailWord_7941355) baseStart_7941355 baseEnd_7941355 := by
    simpa [prefixWord, tailWord_7941355, baseEnd_7941355] using wordTrace_append hprefix tailTrace_7941355
  have hstable : (prefixWord ++ tailWord_7941355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941355).length < 2 ^ (prefixWord ++ tailWord_7941355).sum := by decide
  have hdescent : baseEnd_7941355 < baseStart_7941355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941359 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 1, 1, 4]
def baseStart_7941359 : Nat := 118140960795 + 7941359 * 2 ^ 59
def prefixEnd_7941359 : Nat := 4983230072969 + 3 ^ 40 * 7941359 * 2
def baseEnd_7941359 : Nat := 4077734216908500130090861

theorem tailTrace_7941359 : CollatzResearch.WordTrace tailWord_7941359 prefixEnd_7941359 4077734216908500130090861 := by
  unfold tailWord_7941359
  simp only [CollatzResearch.WordTrace]
  refine ⟨289645158036820093983651131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193096772024546729322434087 289645158036820093983651131)
  ·
    refine ⟨434467737055230140975476697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289645158036820093983651131 434467737055230140975476697)
    ·
      refine ⟨325850802791422605731607523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434467737055230140975476697 325850802791422605731607523)
      ·
        refine ⟨488776204187133908597411285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325850802791422605731607523 488776204187133908597411285)
        ·
          refine ⟨11455692285635950982751827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 488776204187133908597411285 11455692285635950982751827)
          ·
            refine ⟨17183538428453926474127741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455692285635950982751827 17183538428453926474127741)
            ·
              refine ⟨6443826910670222427797903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17183538428453926474127741 6443826910670222427797903)
              ·
                refine ⟨9665740366005333641696855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443826910670222427797903 9665740366005333641696855)
                ·
                  refine ⟨14498610549008000462545283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665740366005333641696855 14498610549008000462545283)
                  ·
                    refine ⟨21747915823512000693817925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14498610549008000462545283 21747915823512000693817925)
                    ·
                      refine ⟨4077734216908500130090861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21747915823512000693817925 4077734216908500130090861)
                      ·
                        rfl

theorem cell23_7941359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 1, 4].length) (baseStart_7941359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941359 prefixEnd_7941359 := by exact prefixLift 7941359
  have htrace : WordTrace (prefixWord ++ tailWord_7941359) baseStart_7941359 baseEnd_7941359 := by
    simpa [prefixWord, tailWord_7941359, baseEnd_7941359] using wordTrace_append hprefix tailTrace_7941359
  have hstable : (prefixWord ++ tailWord_7941359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941359).length < 2 ^ (prefixWord ++ tailWord_7941359).sum := by decide
  have hdescent : baseEnd_7941359 < baseStart_7941359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941425 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 2, 6]
def baseStart_7941425 : Nat := 118140960795 + 7941425 * 2 ^ 59
def prefixEnd_7941425 : Nat := 4983230072969 + 3 ^ 40 * 7941425 * 2
def baseEnd_7941425 : Nat := 1359256035543898957288519

theorem tailTrace_7941425 : CollatzResearch.WordTrace tailWord_7941425 prefixEnd_7941425 1359256035543898957288519 := by
  unfold tailWord_7941425
  simp only [CollatzResearch.WordTrace]
  refine ⟨289647565254580987255553729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193098376836387324837035819 289647565254580987255553729)
  ·
    refine ⟨217235673940935740441665297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289647565254580987255553729 217235673940935740441665297)
    ·
      refine ⟨162926755455701805331248973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217235673940935740441665297 162926755455701805331248973)
      ·
        refine ⟨61097533295888176999218365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162926755455701805331248973 61097533295888176999218365)
        ·
          refine ⟨22911574985958066374706887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61097533295888176999218365 22911574985958066374706887)
          ·
            refine ⟨34367362478937099562060331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22911574985958066374706887 34367362478937099562060331)
            ·
              refine ⟨51551043718405649343090497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34367362478937099562060331 51551043718405649343090497)
              ·
                refine ⟨38663282788804237007317873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51551043718405649343090497 38663282788804237007317873)
                ·
                  refine ⟨28997462091603177755488405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38663282788804237007317873 28997462091603177755488405)
                  ·
                    refine ⟨1359256035543898957288519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28997462091603177755488405 1359256035543898957288519)
                    ·
                      rfl

theorem cell23_7941425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_7941425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941425 prefixEnd_7941425 := by exact prefixLift 7941425
  have htrace : WordTrace (prefixWord ++ tailWord_7941425) baseStart_7941425 baseEnd_7941425 := by
    simpa [prefixWord, tailWord_7941425, baseEnd_7941425] using wordTrace_append hprefix tailTrace_7941425
  have hstable : (prefixWord ++ tailWord_7941425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941425).length < 2 ^ (prefixWord ++ tailWord_7941425).sum := by decide
  have hdescent : baseEnd_7941425 < baseStart_7941425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941426 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_7941426 : Nat := 118140960795 + 7941426 * 2 ^ 59
def prefixEnd_7941426 : Nat := 4983230072969 + 3 ^ 40 * 7941426 * 2
def baseEnd_7941426 : Nat := 4077768620112351367953053

theorem tailTrace_7941426 : CollatzResearch.WordTrace tailWord_7941426 prefixEnd_7941426 4077768620112351367953053 := by
  unfold tailWord_7941426
  simp only [CollatzResearch.WordTrace]
  refine ⟨72411900431894341106585033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193098401151718242950893421 72411900431894341106585033)
  ·
    refine ⟨54308925323920755829938775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72411900431894341106585033 54308925323920755829938775)
    ·
      refine ⟨81463387985881133744908163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54308925323920755829938775 81463387985881133744908163)
      ·
        refine ⟨122195081978821700617362245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81463387985881133744908163 122195081978821700617362245)
        ·
          refine ⟨22911577871029068865755421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122195081978821700617362245 22911577871029068865755421)
          ·
            refine ⟨8591841701635900824658283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22911577871029068865755421 8591841701635900824658283)
            ·
              refine ⟨12887762552453851236987425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8591841701635900824658283 12887762552453851236987425)
              ·
                refine ⟨9665821914340388427740569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12887762552453851236987425 9665821914340388427740569)
                ·
                  refine ⟨7249366435755291320805427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9665821914340388427740569 7249366435755291320805427)
                  ·
                    refine ⟨10874049653632936981208141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7249366435755291320805427 10874049653632936981208141)
                    ·
                      refine ⟨4077768620112351367953053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10874049653632936981208141 4077768620112351367953053)
                      ·
                        rfl

theorem cell23_7941426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_7941426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941426 prefixEnd_7941426 := by exact prefixLift 7941426
  have htrace : WordTrace (prefixWord ++ tailWord_7941426) baseStart_7941426 baseEnd_7941426 := by
    simpa [prefixWord, tailWord_7941426, baseEnd_7941426] using wordTrace_append hprefix tailTrace_7941426
  have hstable : (prefixWord ++ tailWord_7941426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941426).length < 2 ^ (prefixWord ++ tailWord_7941426).sum := by decide
  have hdescent : baseEnd_7941426 < baseStart_7941426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941449 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 2, 2, 2]
def baseStart_7941449 : Nat := 118140960795 + 7941449 * 2 ^ 59
def prefixEnd_7941449 : Nat := 4983230072969 + 3 ^ 40 * 7941449 * 2
def baseEnd_7941449 : Nat := 4077780430167404777965447

theorem tailTrace_7941449 : CollatzResearch.WordTrace tailWord_7941449 prefixEnd_7941449 4077780430167404777965447 := by
  unfold tailWord_7941449
  simp only [CollatzResearch.WordTrace]
  refine ⟨289648440606494039354427401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193098960404329359569618267 289648440606494039354427401)
  ·
    refine ⟨217236330454870529515820551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289648440606494039354427401 217236330454870529515820551)
    ·
      refine ⟨325854495682305794273730827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217236330454870529515820551 325854495682305794273730827)
      ·
        refine ⟨488781743523458691410596241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325854495682305794273730827 488781743523458691410596241)
        ·
          refine ⟨366586307642594018557947181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488781743523458691410596241 366586307642594018557947181)
          ·
            refine ⟨137469865365972756959230193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366586307642594018557947181 137469865365972756959230193)
            ·
              refine ⟨103102399024479567719422645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137469865365972756959230193 103102399024479567719422645)
              ·
                refine ⟨9665849908544959473695873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103102399024479567719422645 9665849908544959473695873)
                ·
                  refine ⟨7249387431408719605271905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9665849908544959473695873 7249387431408719605271905)
                  ·
                    refine ⟨5437040573556539703953929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7249387431408719605271905 5437040573556539703953929)
                    ·
                      refine ⟨4077780430167404777965447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437040573556539703953929 4077780430167404777965447)
                      ·
                        rfl

theorem cell23_7941449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 2, 2].length) (baseStart_7941449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941449 prefixEnd_7941449 := by exact prefixLift 7941449
  have htrace : WordTrace (prefixWord ++ tailWord_7941449) baseStart_7941449 baseEnd_7941449 := by
    simpa [prefixWord, tailWord_7941449, baseEnd_7941449] using wordTrace_append hprefix tailTrace_7941449
  have hstable : (prefixWord ++ tailWord_7941449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941449).length < 2 ^ (prefixWord ++ tailWord_7941449).sum := by decide
  have hdescent : baseEnd_7941449 < baseStart_7941449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941465 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 3]
def baseStart_7941465 : Nat := 118140960795 + 7941465 * 2 ^ 59
def prefixEnd_7941465 : Nat := 4983230072969 + 3 ^ 40 * 7941465 * 2
def baseEnd_7941465 : Nat := 4077788645857876715365373

theorem tailTrace_7941465 : CollatzResearch.WordTrace tailWord_7941465 prefixEnd_7941465 4077788645857876715365373 := by
  unfold tailWord_7941465
  simp only [CollatzResearch.WordTrace]
  refine ⟨289649024174436074087009849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193099349449624049391339899 289649024174436074087009849)
  ·
    refine ⟨217236768130827055565257387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289649024174436074087009849 217236768130827055565257387)
    ·
      refine ⟨325855152196240583347886081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217236768130827055565257387 325855152196240583347886081)
      ·
        refine ⟨244391364147180437510914561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325855152196240583347886081 244391364147180437510914561)
        ·
          refine ⟨183293523110385328133185921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244391364147180437510914561 183293523110385328133185921)
          ·
            refine ⟨137470142332788996099889441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183293523110385328133185921 137470142332788996099889441)
            ·
              refine ⟨103102606749591747074917081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137470142332788996099889441 103102606749591747074917081)
              ·
                refine ⟨77326955062193810306187811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103102606749591747074917081 77326955062193810306187811)
                ·
                  refine ⟨115990432593290715459281717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77326955062193810306187811 115990432593290715459281717)
                  ·
                    refine ⟨10874103055621004574307661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115990432593290715459281717 10874103055621004574307661)
                    ·
                      refine ⟨4077788645857876715365373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10874103055621004574307661 4077788645857876715365373)
                      ·
                        rfl

theorem cell23_7941465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_7941465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941465 prefixEnd_7941465 := by exact prefixLift 7941465
  have htrace : WordTrace (prefixWord ++ tailWord_7941465) baseStart_7941465 baseEnd_7941465 := by
    simpa [prefixWord, tailWord_7941465, baseEnd_7941465] using wordTrace_append hprefix tailTrace_7941465
  have hstable : (prefixWord ++ tailWord_7941465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941465).length < 2 ^ (prefixWord ++ tailWord_7941465).sum := by decide
  have hdescent : baseEnd_7941465 < baseStart_7941465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941495 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_7941495 : Nat := 118140960795 + 7941495 * 2 ^ 59
def prefixEnd_7941495 : Nat := 4983230072969 + 3 ^ 40 * 7941495 * 2
def baseEnd_7941495 : Nat := 4077804050277511597990235

theorem tailTrace_7941495 : CollatzResearch.WordTrace tailWord_7941495 prefixEnd_7941495 4077804050277511597990235 := by
  unfold tailWord_7941495
  simp only [CollatzResearch.WordTrace]
  refine ⟨289650118364327389210601939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193100078909551592807067959 289650118364327389210601939)
  ·
    refine ⟨434475177546491083815902909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289650118364327389210601939 434475177546491083815902909)
    ·
      refine ⟨162928191579934156430963591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434475177546491083815902909 162928191579934156430963591)
      ·
        refine ⟨244392287369901234646445387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162928191579934156430963591 244392287369901234646445387)
        ·
          refine ⟨366588431054851851969668081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244392287369901234646445387 366588431054851851969668081)
          ·
            refine ⟨274941323291138888977251061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366588431054851851969668081 274941323291138888977251061)
            ·
              refine ⟨25775749058544270841617287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274941323291138888977251061 25775749058544270841617287)
              ·
                refine ⟨38663623587816406262425931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25775749058544270841617287 38663623587816406262425931)
                ·
                  refine ⟨57995435381724609393638897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38663623587816406262425931 57995435381724609393638897)
                  ·
                    refine ⟨43496576536293457045229173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57995435381724609393638897 43496576536293457045229173)
                    ·
                      refine ⟨4077804050277511597990235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43496576536293457045229173 4077804050277511597990235)
                      ·
                        rfl

theorem cell23_7941495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_7941495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941495 prefixEnd_7941495 := by exact prefixLift 7941495
  have htrace : WordTrace (prefixWord ++ tailWord_7941495) baseStart_7941495 baseEnd_7941495 := by
    simpa [prefixWord, tailWord_7941495, baseEnd_7941495] using wordTrace_append hprefix tailTrace_7941495
  have hstable : (prefixWord ++ tailWord_7941495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941495).length < 2 ^ (prefixWord ++ tailWord_7941495).sum := by decide
  have hdescent : baseEnd_7941495 < baseStart_7941495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941585 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_7941585 : Nat := 118140960795 + 7941585 * 2 ^ 59
def prefixEnd_7941585 : Nat := 4983230072969 + 3 ^ 40 * 7941585 * 2
def baseEnd_7941585 : Nat := 4077850263536416245864821

theorem tailTrace_7941585 : CollatzResearch.WordTrace tailWord_7941585 prefixEnd_7941585 4077850263536416245864821 := by
  unfold tailWord_7941585
  simp only [CollatzResearch.WordTrace]
  refine ⟨289653400934001334581378209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193102267289334223054252139 289653400934001334581378209)
  ·
    refine ⟨217240050700501000936033657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289653400934001334581378209 217240050700501000936033657)
    ·
      refine ⟨162930038025375750702025243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217240050700501000936033657 162930038025375750702025243)
      ·
        refine ⟨244395057038063626053037865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162930038025375750702025243 244395057038063626053037865)
        ·
          refine ⟨183296292778547719539778399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244395057038063626053037865 183296292778547719539778399)
          ·
            refine ⟨274944439167821579309667599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183296292778547719539778399 274944439167821579309667599)
            ·
              refine ⟨412416658751732368964501399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274944439167821579309667599 412416658751732368964501399)
              ·
                refine ⟨618624988127598553446752099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412416658751732368964501399 618624988127598553446752099)
                ·
                  refine ⟨927937482191397830170128149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618624988127598553446752099 927937482191397830170128149)
                  ·
                    refine ⟨43497069477721773289224757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 927937482191397830170128149 43497069477721773289224757)
                    ·
                      refine ⟨4077850263536416245864821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43497069477721773289224757 4077850263536416245864821)
                      ·
                        rfl

theorem cell23_7941585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_7941585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941585 prefixEnd_7941585 := by exact prefixLift 7941585
  have htrace : WordTrace (prefixWord ++ tailWord_7941585) baseStart_7941585 baseEnd_7941585 := by
    simpa [prefixWord, tailWord_7941585, baseEnd_7941585] using wordTrace_append hprefix tailTrace_7941585
  have hstable : (prefixWord ++ tailWord_7941585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941585).length < 2 ^ (prefixWord ++ tailWord_7941585).sum := by decide
  have hdescent : baseEnd_7941585 < baseStart_7941585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941589 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7941589 : Nat := 118140960795 + 7941589 * 2 ^ 59
def prefixEnd_7941589 : Nat := 4983230072969 + 3 ^ 40 * 7941589 * 2
def baseEnd_7941589 : Nat := 4077852317459034230214803

theorem tailTrace_7941589 : CollatzResearch.WordTrace tailWord_7941589 prefixEnd_7941589 4077852317459034230214803 := by
  unfold tailWord_7941589
  simp only [CollatzResearch.WordTrace]
  refine ⟨289653546825986843264523821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193102364550657895509682547 289653546825986843264523821)
  ·
    refine ⟨108620080059745066224196433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289653546825986843264523821 108620080059745066224196433)
    ·
      refine ⟨81465060044808799668147325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108620080059745066224196433 81465060044808799668147325)
      ·
        refine ⟨30549397516803299875555247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81465060044808799668147325 30549397516803299875555247)
        ·
          refine ⟨45824096275204949813332871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30549397516803299875555247 45824096275204949813332871)
          ·
            refine ⟨68736144412807424719999307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45824096275204949813332871 68736144412807424719999307)
            ·
              refine ⟨103104216619211137079998961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68736144412807424719999307 103104216619211137079998961)
              ·
                refine ⟨77328162464408352809999221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103104216619211137079998961 77328162464408352809999221)
                ·
                  refine ⟨7249515231038283075937427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77328162464408352809999221 7249515231038283075937427)
                  ·
                    refine ⟨10874272846557424613906141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7249515231038283075937427 10874272846557424613906141)
                    ·
                      refine ⟨4077852317459034230214803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10874272846557424613906141 4077852317459034230214803)
                      ·
                        rfl

theorem cell23_7941589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7941589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941589 prefixEnd_7941589 := by exact prefixLift 7941589
  have htrace : WordTrace (prefixWord ++ tailWord_7941589) baseStart_7941589 baseEnd_7941589 := by
    simpa [prefixWord, tailWord_7941589, baseEnd_7941589] using wordTrace_append hprefix tailTrace_7941589
  have hstable : (prefixWord ++ tailWord_7941589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941589).length < 2 ^ (prefixWord ++ tailWord_7941589).sum := by decide
  have hdescent : baseEnd_7941589 < baseStart_7941589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941599 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 4, 3, 2]
def baseStart_7941599 : Nat := 118140960795 + 7941599 * 2 ^ 59
def prefixEnd_7941599 : Nat := 4983230072969 + 3 ^ 40 * 7941599 * 2
def baseEnd_7941599 : Nat := 4077857452265579191089757

theorem tailTrace_7941599 : CollatzResearch.WordTrace tailWord_7941599 prefixEnd_7941599 4077857452265579191089757 := by
  unfold tailWord_7941599
  simp only [CollatzResearch.WordTrace]
  refine ⟨289653911555950614972387851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193102607703967076648258567 289653911555950614972387851)
  ·
    refine ⟨434480867333925922458581777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289653911555950614972387851 434480867333925922458581777)
    ·
      refine ⟨325860650500444441843936333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434480867333925922458581777 325860650500444441843936333)
      ·
        refine ⟨122197743937666665691476125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325860650500444441843936333 122197743937666665691476125)
        ·
          refine ⟨45824153976624999634303547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122197743937666665691476125 45824153976624999634303547)
          ·
            refine ⟨68736230964937499451455321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45824153976624999634303547 68736230964937499451455321)
            ·
              refine ⟨51552173223703124588591491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68736230964937499451455321 51552173223703124588591491)
              ·
                refine ⟨77328259835554686882887237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51552173223703124588591491 77328259835554686882887237)
                ·
                  refine ⟨14499048719166503790541357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77328259835554686882887237 14499048719166503790541357)
                  ·
                    refine ⟨5437143269687438921453009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14499048719166503790541357 5437143269687438921453009)
                    ·
                      refine ⟨4077857452265579191089757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437143269687438921453009 4077857452265579191089757)
                      ·
                        rfl

theorem cell23_7941599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_7941599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941599 prefixEnd_7941599 := by exact prefixLift 7941599
  have htrace : WordTrace (prefixWord ++ tailWord_7941599) baseStart_7941599 baseEnd_7941599 := by
    simpa [prefixWord, tailWord_7941599, baseEnd_7941599] using wordTrace_append hprefix tailTrace_7941599
  have hstable : (prefixWord ++ tailWord_7941599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941599).length < 2 ^ (prefixWord ++ tailWord_7941599).sum := by decide
  have hdescent : baseEnd_7941599 < baseStart_7941599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941612 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_7941612 : Nat := 118140960795 + 7941612 * 2 ^ 59
def prefixEnd_7941612 : Nat := 4983230072969 + 3 ^ 40 * 7941612 * 2
def baseEnd_7941612 : Nat := 4077864127514087640227197

theorem tailTrace_7941612 : CollatzResearch.WordTrace tailWord_7941612 prefixEnd_7941612 4077864127514087640227197 := by
  unfold tailWord_7941612
  simp only [CollatzResearch.WordTrace]
  refine ⟨144827192852451759096305545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193102923803269012128407393 144827192852451759096305545)
  ·
    refine ⟨108620394639338819322229159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144827192852451759096305545 108620394639338819322229159)
    ·
      refine ⟨162930591959008228983343739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108620394639338819322229159 162930591959008228983343739)
      ·
        refine ⟨244395887938512343475015609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162930591959008228983343739 244395887938512343475015609)
        ·
          refine ⟨183296915953884257606261707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244395887938512343475015609 183296915953884257606261707)
          ·
            refine ⟨274945373930826386409392561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183296915953884257606261707 274945373930826386409392561)
            ·
              refine ⟨206209030448119789807044421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274945373930826386409392561 206209030448119789807044421)
              ·
                refine ⟨38664193209022460588820829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206209030448119789807044421 38664193209022460588820829)
                ·
                  refine ⟨14499072453383422720807811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38664193209022460588820829 14499072453383422720807811)
                  ·
                    refine ⟨21748608680075134081211717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14499072453383422720807811 21748608680075134081211717)
                    ·
                      refine ⟨4077864127514087640227197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21748608680075134081211717 4077864127514087640227197)
                      ·
                        rfl

theorem cell23_7941612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_7941612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941612 prefixEnd_7941612 := by exact prefixLift 7941612
  have htrace : WordTrace (prefixWord ++ tailWord_7941612) baseStart_7941612 baseEnd_7941612 := by
    simpa [prefixWord, tailWord_7941612, baseEnd_7941612] using wordTrace_append hprefix tailTrace_7941612
  have hstable : (prefixWord ++ tailWord_7941612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941612).length < 2 ^ (prefixWord ++ tailWord_7941612).sum := by decide
  have hdescent : baseEnd_7941612 < baseStart_7941612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941629 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_7941629 : Nat := 118140960795 + 7941629 * 2 ^ 59
def prefixEnd_7941629 : Nat := 4983230072969 + 3 ^ 40 * 7941629 * 2
def baseEnd_7941629 : Nat := 4077872856685214073714619

theorem tailTrace_7941629 : CollatzResearch.WordTrace tailWord_7941629 prefixEnd_7941629 4077872856685214073714619 := by
  unfold tailWord_7941629
  simp only [CollatzResearch.WordTrace]
  refine ⟨289655005745841930095979941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193103337163894620063986627 289655005745841930095979941)
  ·
    refine ⟨54310313577345361892996239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289655005745841930095979941 54310313577345361892996239)
    ·
      refine ⟨81465470366018042839494359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54310313577345361892996239 81465470366018042839494359)
      ·
        refine ⟨122198205549027064259241539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81465470366018042839494359 122198205549027064259241539)
        ·
          refine ⟨183297308323540596388862309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122198205549027064259241539 183297308323540596388862309)
          ·
            refine ⟨34368245310663861822911683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183297308323540596388862309 34368245310663861822911683)
            ·
              refine ⟨51552367965995792734367525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34368245310663861822911683 51552367965995792734367525)
              ·
                refine ⟨9666068993624211137693911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51552367965995792734367525 9666068993624211137693911)
                ·
                  refine ⟨14499103490436316706540867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9666068993624211137693911 14499103490436316706540867)
                  ·
                    refine ⟨21748655235654475059811301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14499103490436316706540867 21748655235654475059811301)
                    ·
                      refine ⟨4077872856685214073714619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21748655235654475059811301 4077872856685214073714619)
                      ·
                        rfl

theorem cell23_7941629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_7941629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941629 prefixEnd_7941629 := by exact prefixLift 7941629
  have htrace : WordTrace (prefixWord ++ tailWord_7941629) baseStart_7941629 baseEnd_7941629 := by
    simpa [prefixWord, tailWord_7941629, baseEnd_7941629] using wordTrace_append hprefix tailTrace_7941629
  have hstable : (prefixWord ++ tailWord_7941629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941629).length < 2 ^ (prefixWord ++ tailWord_7941629).sum := by decide
  have hdescent : baseEnd_7941629 < baseStart_7941629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941639 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 4, 4]
def baseStart_7941639 : Nat := 118140960795 + 7941639 * 2 ^ 59
def prefixEnd_7941639 : Nat := 4983230072969 + 3 ^ 40 * 7941639 * 2
def baseEnd_7941639 : Nat := 1359292663830586344863191

theorem tailTrace_7941639 : CollatzResearch.WordTrace tailWord_7941639 prefixEnd_7941639 1359292663830586344863191 := by
  unfold tailWord_7941639
  simp only [CollatzResearch.WordTrace]
  refine ⟨289655370475805701803843971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193103580317203801202562647 289655370475805701803843971)
  ·
    refine ⟨434483055713708552705765957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289655370475805701803843971 434483055713708552705765957)
    ·
      refine ⟨81465572946320353632331117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434483055713708552705765957 81465572946320353632331117)
      ·
        refine ⟨30549589854870132612124169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81465572946320353632331117 30549589854870132612124169)
        ·
          refine ⟨22912192391152599459093127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30549589854870132612124169 22912192391152599459093127)
          ·
            refine ⟨34368288586728899188639691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22912192391152599459093127 34368288586728899188639691)
            ·
              refine ⟨51552432880093348782959537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34368288586728899188639691 51552432880093348782959537)
              ·
                refine ⟨38664324660070011587219653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51552432880093348782959537 38664324660070011587219653)
                ·
                  refine ⟨7249560873763127172603685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38664324660070011587219653 7249560873763127172603685)
                  ·
                    refine ⟨1359292663830586344863191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249560873763127172603685 1359292663830586344863191)
                    ·
                      rfl

theorem cell23_7941639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_7941639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941639 prefixEnd_7941639 := by exact prefixLift 7941639
  have htrace : WordTrace (prefixWord ++ tailWord_7941639) baseStart_7941639 baseEnd_7941639 := by
    simpa [prefixWord, tailWord_7941639, baseEnd_7941639] using wordTrace_append hprefix tailTrace_7941639
  have hstable : (prefixWord ++ tailWord_7941639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941639).length < 2 ^ (prefixWord ++ tailWord_7941639).sum := by decide
  have hdescent : baseEnd_7941639 < baseStart_7941639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941649 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_7941649 : Nat := 118140960795 + 7941649 * 2 ^ 59
def prefixEnd_7941649 : Nat := 4983230072969 + 3 ^ 40 * 7941649 * 2
def baseEnd_7941649 : Nat := 4077883126298303995464527

theorem tailTrace_7941649 : CollatzResearch.WordTrace tailWord_7941649 prefixEnd_7941649 4077883126298303995464527 := by
  unfold tailWord_7941649
  simp only [CollatzResearch.WordTrace]
  refine ⟨289655735205769473511708001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193103823470512982341138667 289655735205769473511708001)
  ·
    refine ⟨217241801404327105133781001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289655735205769473511708001 217241801404327105133781001)
    ·
      refine ⟨162931351053245328850335751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217241801404327105133781001 162931351053245328850335751)
      ·
        refine ⟨244397026579867993275503627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162931351053245328850335751 244397026579867993275503627)
        ·
          refine ⟨366595539869801989913255441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244397026579867993275503627 366595539869801989913255441)
          ·
            refine ⟨274946654902351492434941581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366595539869801989913255441 274946654902351492434941581)
            ·
              refine ⟨103104995588381809663103093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274946654902351492434941581 103104995588381809663103093)
              ·
                refine ⟨9666093336410794655915915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103104995588381809663103093 9666093336410794655915915)
                ·
                  refine ⟨14499140004616191983873873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9666093336410794655915915 14499140004616191983873873)
                  ·
                    refine ⟨10874355003462143987905405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14499140004616191983873873 10874355003462143987905405)
                    ·
                      refine ⟨4077883126298303995464527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10874355003462143987905405 4077883126298303995464527)
                      ·
                        rfl

theorem cell23_7941649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_7941649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941649 prefixEnd_7941649 := by exact prefixLift 7941649
  have htrace : WordTrace (prefixWord ++ tailWord_7941649) baseStart_7941649 baseEnd_7941649 := by
    simpa [prefixWord, tailWord_7941649, baseEnd_7941649] using wordTrace_append hprefix tailTrace_7941649
  have hstable : (prefixWord ++ tailWord_7941649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941649).length < 2 ^ (prefixWord ++ tailWord_7941649).sum := by decide
  have hdescent : baseEnd_7941649 < baseStart_7941649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941663 : List Nat := [1, 1, 2, 4, 1, 1, 2, 6, 1, 2, 2]
def baseStart_7941663 : Nat := 118140960795 + 7941663 * 2 ^ 59
def prefixEnd_7941663 : Nat := 4983230072969 + 3 ^ 40 * 7941663 * 2
def baseEnd_7941663 : Nat := 4077890315027466940689463

theorem tailTrace_7941663 : CollatzResearch.WordTrace tailWord_7941663 prefixEnd_7941663 4077890315027466940689463 := by
  unfold tailWord_7941663
  simp only [CollatzResearch.WordTrace]
  refine ⟨289656245827718753902717643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193104163885145835935145095 289656245827718753902717643)
  ·
    refine ⟨434484368741578130854076465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289656245827718753902717643 434484368741578130854076465)
    ·
      refine ⟨325863276556183598140557349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434484368741578130854076465 325863276556183598140557349)
      ·
        refine ⟨61099364354284424651354503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325863276556183598140557349 61099364354284424651354503)
        ·
          refine ⟨91649046531426636977031755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61099364354284424651354503 91649046531426636977031755)
          ·
            refine ⟨137473569797139955465547633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91649046531426636977031755 137473569797139955465547633)
            ·
              refine ⟨103105177347854966599160725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137473569797139955465547633 103105177347854966599160725)
              ·
                refine ⟨4833055188180701559335659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103105177347854966599160725 4833055188180701559335659)
                ·
                  refine ⟨7249582782271052339003489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833055188180701559335659 7249582782271052339003489)
                  ·
                    refine ⟨5437187086703289254252617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7249582782271052339003489 5437187086703289254252617)
                    ·
                      refine ⟨4077890315027466940689463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437187086703289254252617 4077890315027466940689463)
                      ·
                        rfl

theorem cell23_7941663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_7941663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941663 prefixEnd_7941663 := by exact prefixLift 7941663
  have htrace : WordTrace (prefixWord ++ tailWord_7941663) baseStart_7941663 baseEnd_7941663 := by
    simpa [prefixWord, tailWord_7941663, baseEnd_7941663] using wordTrace_append hprefix tailTrace_7941663
  have hstable : (prefixWord ++ tailWord_7941663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941663).length < 2 ^ (prefixWord ++ tailWord_7941663).sum := by decide
  have hdescent : baseEnd_7941663 < baseStart_7941663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941712 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 2, 6]
def baseStart_7941712 : Nat := 118140960795 + 7941712 * 2 ^ 59
def prefixEnd_7941712 : Nat := 4983230072969 + 3 ^ 40 * 7941712 * 2
def baseEnd_7941712 : Nat := 1359305158526512416325579

theorem tailTrace_7941712 : CollatzResearch.WordTrace tailWord_7941712 prefixEnd_7941712 1359305158526512416325579 := by
  unfold tailWord_7941712
  simp only [CollatzResearch.WordTrace]
  refine ⟨144829016502270617635625695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193105355336360823514167593 144829016502270617635625695)
  ·
    refine ⟨217243524753405926453438543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144829016502270617635625695 217243524753405926453438543)
    ·
      refine ⟨325865287130108889680157815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217243524753405926453438543 325865287130108889680157815)
      ·
        refine ⟨488797930695163334520236723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325865287130108889680157815 488797930695163334520236723)
        ·
          refine ⟨733196896042745001780355085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488797930695163334520236723 733196896042745001780355085)
          ·
            refine ⟨274948836016029375667633157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733196896042745001780355085 274948836016029375667633157)
            ·
              refine ⟨51552906753005507937681217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274948836016029375667633157 51552906753005507937681217)
              ·
                refine ⟨38664680064754130953260913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51552906753005507937681217 38664680064754130953260913)
                ·
                  refine ⟨28998510048565598214945685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38664680064754130953260913 28998510048565598214945685)
                  ·
                    refine ⟨1359305158526512416325579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28998510048565598214945685 1359305158526512416325579)
                    ·
                      rfl

theorem cell23_7941712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_7941712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941712 prefixEnd_7941712 := by exact prefixLift 7941712
  have htrace : WordTrace (prefixWord ++ tailWord_7941712) baseStart_7941712 baseEnd_7941712 := by
    simpa [prefixWord, tailWord_7941712, baseEnd_7941712] using wordTrace_append hprefix tailTrace_7941712
  have hstable : (prefixWord ++ tailWord_7941712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941712).length < 2 ^ (prefixWord ++ tailWord_7941712).sum := by decide
  have hdescent : baseEnd_7941712 < baseStart_7941712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941722 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_7941722 : Nat := 118140960795 + 7941722 * 2 ^ 59
def prefixEnd_7941722 : Nat := 4983230072969 + 3 ^ 40 * 7941722 * 2
def baseEnd_7941722 : Nat := 4077920610386082209851691

theorem tailTrace_7941722 : CollatzResearch.WordTrace tailWord_7941722 prefixEnd_7941722 4077920610386082209851691 := by
  unfold tailWord_7941722
  simp only [CollatzResearch.WordTrace]
  refine ⟨72414599433626251744778855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193105598489670004652743613 72414599433626251744778855)
  ·
    refine ⟨108621899150439377617168283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72414599433626251744778855 108621899150439377617168283)
    ·
      refine ⟨162932848725659066425752425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108621899150439377617168283 162932848725659066425752425)
      ·
        refine ⟨122199636544244299819314319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162932848725659066425752425 122199636544244299819314319)
        ·
          refine ⟨183299454816366449728971479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122199636544244299819314319 183299454816366449728971479)
          ·
            refine ⟨274949182224549674593457219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183299454816366449728971479 274949182224549674593457219)
            ·
              refine ⟨412423773336824511890185829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274949182224549674593457219 412423773336824511890185829)
              ·
                refine ⟨77329457500654595979409843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412423773336824511890185829 77329457500654595979409843)
                ·
                  refine ⟨115994186250981893969114765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77329457500654595979409843 115994186250981893969114765)
                  ·
                    refine ⟨43497819844118210238418037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115994186250981893969114765 43497819844118210238418037)
                    ·
                      refine ⟨4077920610386082209851691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43497819844118210238418037 4077920610386082209851691)
                      ·
                        rfl

theorem cell23_7941722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_7941722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941722 prefixEnd_7941722 := by exact prefixLift 7941722
  have htrace : WordTrace (prefixWord ++ tailWord_7941722) baseStart_7941722 baseEnd_7941722 := by
    simpa [prefixWord, tailWord_7941722, baseEnd_7941722] using wordTrace_append hprefix tailTrace_7941722
  have hstable : (prefixWord ++ tailWord_7941722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941722).length < 2 ^ (prefixWord ++ tailWord_7941722).sum := by decide
  have hdescent : baseEnd_7941722 < baseStart_7941722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941769 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 3]
def baseStart_7941769 : Nat := 118140960795 + 7941769 * 2 ^ 59
def prefixEnd_7941769 : Nat := 4983230072969 + 3 ^ 40 * 7941769 * 2
def baseEnd_7941769 : Nat := 4077944743976843525963975

theorem tailTrace_7941769 : CollatzResearch.WordTrace tailWord_7941769 prefixEnd_7941769 4077944743976843525963975 := by
  unfold tailWord_7941769
  simp only [CollatzResearch.WordTrace]
  refine ⟨289660111965334734006076361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193106741310223156004050907 289660111965334734006076361)
  ·
    refine ⟨217245083974001050504557271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289660111965334734006076361 217245083974001050504557271)
    ·
      refine ⟨325867625961001575756835907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217245083974001050504557271 325867625961001575756835907)
      ·
        refine ⟨488801438941502363635253861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325867625961001575756835907 488801438941502363635253861)
        ·
          refine ⟨91650269801531693181610099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488801438941502363635253861 91650269801531693181610099)
          ·
            refine ⟨137475404702297539772415149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91650269801531693181610099 137475404702297539772415149)
            ·
              refine ⟨51553276763361577414655681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137475404702297539772415149 51553276763361577414655681)
              ·
                refine ⟨38664957572521183060991761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51553276763361577414655681 38664957572521183060991761)
                ·
                  refine ⟨28998718179390887295743821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38664957572521183060991761 28998718179390887295743821)
                  ·
                    refine ⟨10874519317271582735903933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28998718179390887295743821 10874519317271582735903933)
                    ·
                      refine ⟨4077944743976843525963975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10874519317271582735903933 4077944743976843525963975)
                      ·
                        rfl

theorem cell23_7941769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_7941769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941769 prefixEnd_7941769 := by exact prefixLift 7941769
  have htrace : WordTrace (prefixWord ++ tailWord_7941769) baseStart_7941769 baseEnd_7941769 := by
    simpa [prefixWord, tailWord_7941769, baseEnd_7941769] using wordTrace_append hprefix tailTrace_7941769
  have hstable : (prefixWord ++ tailWord_7941769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941769).length < 2 ^ (prefixWord ++ tailWord_7941769).sum := by decide
  have hdescent : baseEnd_7941769 < baseStart_7941769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941770 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_7941770 : Nat := 118140960795 + 7941770 * 2 ^ 59
def prefixEnd_7941770 : Nat := 4983230072969 + 3 ^ 40 * 7941770 * 2
def baseEnd_7941770 : Nat := 4077945257457498022051471

theorem tailTrace_7941770 : CollatzResearch.WordTrace tailWord_7941770 prefixEnd_7941770 4077945257457498022051471 := by
  unfold tailWord_7941770
  simp only [CollatzResearch.WordTrace]
  refine ⟨72415037109582777794215691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193106765625554074117908509 72415037109582777794215691)
  ·
    refine ⟨108622555664374166691323537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72415037109582777794215691 108622555664374166691323537)
    ·
      refine ⟨81466916748280625018492653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108622555664374166691323537 81466916748280625018492653)
      ·
        refine ⟨30550093780605234381934745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81466916748280625018492653 30550093780605234381934745)
        ·
          refine ⟨22912570335453925786451059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30550093780605234381934745 22912570335453925786451059)
          ·
            refine ⟨34368855503180888679676589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22912570335453925786451059 34368855503180888679676589)
            ·
              refine ⟨12888320813692833254878721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34368855503180888679676589 12888320813692833254878721)
              ·
                refine ⟨9666240610269624941159041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12888320813692833254878721 9666240610269624941159041)
                ·
                  refine ⟨7249680457702218705869281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9666240610269624941159041 7249680457702218705869281)
                  ·
                    refine ⟨5437260343276664029401961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7249680457702218705869281 5437260343276664029401961)
                    ·
                      refine ⟨4077945257457498022051471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437260343276664029401961 4077945257457498022051471)
                      ·
                        rfl

theorem cell23_7941770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_7941770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941770 prefixEnd_7941770 := by exact prefixLift 7941770
  have htrace : WordTrace (prefixWord ++ tailWord_7941770) baseStart_7941770 baseEnd_7941770 := by
    simpa [prefixWord, tailWord_7941770, baseEnd_7941770] using wordTrace_append hprefix tailTrace_7941770
  have hstable : (prefixWord ++ tailWord_7941770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941770).length < 2 ^ (prefixWord ++ tailWord_7941770).sum := by decide
  have hdescent : baseEnd_7941770 < baseStart_7941770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941819 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 5, 4]
def baseStart_7941819 : Nat := 118140960795 + 7941819 * 2 ^ 59
def prefixEnd_7941819 : Nat := 4983230072969 + 3 ^ 40 * 7941819 * 2
def baseEnd_7941819 : Nat := 1359323472669856110112915

theorem tailTrace_7941819 : CollatzResearch.WordTrace tailWord_7941819 prefixEnd_7941819 1359323472669856110112915 := by
  unfold tailWord_7941819
  simp only [CollatzResearch.WordTrace]
  refine ⟨289661935615153592545396511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193107957076769061696931007 289661935615153592545396511)
  ·
    refine ⟨434492903422730388818094767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289661935615153592545396511 434492903422730388818094767)
    ·
      refine ⟨651739355134095583227142151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434492903422730388818094767 651739355134095583227142151)
      ·
        refine ⟨977609032701143374840713227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651739355134095583227142151 977609032701143374840713227)
        ·
          refine ⟨1466413549051715062261069841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977609032701143374840713227 1466413549051715062261069841)
          ·
            refine ⟨1099810161788786296695802381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466413549051715062261069841 1099810161788786296695802381)
            ·
              refine ⟨412428810670794861260925893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1099810161788786296695802381 412428810670794861260925893)
              ·
                refine ⟨77330402000774036486423605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412428810670794861260925893 77330402000774036486423605)
                ·
                  refine ⟨7249725187572565920602213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77330402000774036486423605 7249725187572565920602213)
                  ·
                    refine ⟨1359323472669856110112915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249725187572565920602213 1359323472669856110112915)
                    ·
                      rfl

theorem cell23_7941819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 4].length) (baseStart_7941819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941819 prefixEnd_7941819 := by exact prefixLift 7941819
  have htrace : WordTrace (prefixWord ++ tailWord_7941819) baseStart_7941819 baseEnd_7941819 := by
    simpa [prefixWord, tailWord_7941819, baseEnd_7941819] using wordTrace_append hprefix tailTrace_7941819
  have hstable : (prefixWord ++ tailWord_7941819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941819).length < 2 ^ (prefixWord ++ tailWord_7941819).sum := by decide
  have hdescent : baseEnd_7941819 < baseStart_7941819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941916 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7941916 : Nat := 118140960795 + 7941916 * 2 ^ 59
def prefixEnd_7941916 : Nat := 4983230072969 + 3 ^ 40 * 7941916 * 2
def baseEnd_7941916 : Nat := 4078020225633054450825799

theorem tailTrace_7941916 : CollatzResearch.WordTrace tailWord_7941916 prefixEnd_7941916 4078020225633054450825799 := by
  unfold tailWord_7941916
  simp only [CollatzResearch.WordTrace]
  refine ⟨144832736747901089055838801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193110315663868118741118401 144832736747901089055838801)
  ·
    refine ⟨108624552560925816791879101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144832736747901089055838801 108624552560925816791879101)
    ·
      refine ⟨40734207210347181296954663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108624552560925816791879101 40734207210347181296954663)
      ·
        refine ⟨61101310815520771945431995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40734207210347181296954663 61101310815520771945431995)
        ·
          refine ⟨91651966223281157918147993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61101310815520771945431995 91651966223281157918147993)
          ·
            refine ⟨68738974667460868438610995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91651966223281157918147993 68738974667460868438610995)
            ·
              refine ⟨103108462001191302657916493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68738974667460868438610995 103108462001191302657916493)
              ·
                refine ⟨38665673250446738496718685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103108462001191302657916493 38665673250446738496718685)
                ·
                  refine ⟨14499627468917526936269507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38665673250446738496718685 14499627468917526936269507)
                  ·
                    refine ⟨21749441203376290404404261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14499627468917526936269507 21749441203376290404404261)
                    ·
                      refine ⟨4078020225633054450825799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21749441203376290404404261 4078020225633054450825799)
                      ·
                        rfl

theorem cell23_7941916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7941916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941916 prefixEnd_7941916 := by exact prefixLift 7941916
  have htrace : WordTrace (prefixWord ++ tailWord_7941916) baseStart_7941916 baseEnd_7941916 := by
    simpa [prefixWord, tailWord_7941916, baseEnd_7941916] using wordTrace_append hprefix tailTrace_7941916
  have hstable : (prefixWord ++ tailWord_7941916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941916).length < 2 ^ (prefixWord ++ tailWord_7941916).sum := by decide
  have hdescent : baseEnd_7941916 < baseStart_7941916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941960 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 2, 4]
def baseStart_7941960 : Nat := 118140960795 + 7941960 * 2 ^ 59
def prefixEnd_7941960 : Nat := 4983230072969 + 3 ^ 40 * 7941960 * 2
def baseEnd_7941960 : Nat := 1359347606260617426225199

theorem tailTrace_7941960 : CollatzResearch.WordTrace tailWord_7941960 prefixEnd_7941960 1359347606260617426225199 := by
  unfold tailWord_7941960
  simp only [CollatzResearch.WordTrace]
  refine ⟨144833539153821386813139667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193111385538428515750852889 144833539153821386813139667)
  ·
    refine ⟨217250308730732080219709501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144833539153821386813139667 217250308730732080219709501)
    ·
      refine ⟨81468865774024530082391063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217250308730732080219709501 81468865774024530082391063)
      ·
        refine ⟨122203298661036795123586595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81468865774024530082391063 122203298661036795123586595)
        ·
          refine ⟨183304947991555192685379893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122203298661036795123586595 183304947991555192685379893)
          ·
            refine ⟨17184838874208299314254365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183304947991555192685379893 17184838874208299314254365)
            ·
              refine ⟨6444314577828112242845387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17184838874208299314254365 6444314577828112242845387)
              ·
                refine ⟨9666471866742168364268081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444314577828112242845387 9666471866742168364268081)
                ·
                  refine ⟨7249853900056626273201061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9666471866742168364268081 7249853900056626273201061)
                  ·
                    refine ⟨1359347606260617426225199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249853900056626273201061 1359347606260617426225199)
                    ·
                      rfl

theorem cell23_7941960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_7941960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941960 prefixEnd_7941960 := by exact prefixLift 7941960
  have htrace : WordTrace (prefixWord ++ tailWord_7941960) baseStart_7941960 baseEnd_7941960 := by
    simpa [prefixWord, tailWord_7941960, baseEnd_7941960] using wordTrace_append hprefix tailTrace_7941960
  have hstable : (prefixWord ++ tailWord_7941960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941960).length < 2 ^ (prefixWord ++ tailWord_7941960).sum := by decide
  have hdescent : baseEnd_7941960 < baseStart_7941960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941970 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_7941970 : Nat := 118140960795 + 7941970 * 2 ^ 59
def prefixEnd_7941970 : Nat := 4983230072969 + 3 ^ 40 * 7941970 * 2
def baseEnd_7941970 : Nat := 4078047953588397239550551

theorem tailTrace_7941970 : CollatzResearch.WordTrace tailWord_7941970 prefixEnd_7941970 4078047953588397239550551 := by
  unfold tailWord_7941970
  simp only [CollatzResearch.WordTrace]
  refine ⟨72416860759401636333535841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193111628691737696889428909 72416860759401636333535841)
  ·
    refine ⟨54312645569551227250151881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72416860759401636333535841 54312645569551227250151881)
    ·
      refine ⟨40734484177163420437613911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54312645569551227250151881 40734484177163420437613911)
      ·
        refine ⟨61101726265745130656420867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40734484177163420437613911 61101726265745130656420867)
        ·
          refine ⟨91652589398617695984631301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61101726265745130656420867 91652589398617695984631301)
          ·
            refine ⟨17184860512240817997118369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91652589398617695984631301 17184860512240817997118369)
            ·
              refine ⟨12888645384180613497838777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17184860512240817997118369 12888645384180613497838777)
              ·
                refine ⟨9666484038135460123379083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12888645384180613497838777 9666484038135460123379083)
                ·
                  refine ⟨14499726057203190185068625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9666484038135460123379083 14499726057203190185068625)
                  ·
                    refine ⟨10874794542902392638801469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14499726057203190185068625 10874794542902392638801469)
                    ·
                      refine ⟨4078047953588397239550551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10874794542902392638801469 4078047953588397239550551)
                      ·
                        rfl

theorem cell23_7941970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_7941970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941970 prefixEnd_7941970 := by exact prefixLift 7941970
  have htrace : WordTrace (prefixWord ++ tailWord_7941970) baseStart_7941970 baseEnd_7941970 := by
    simpa [prefixWord, tailWord_7941970, baseEnd_7941970] using wordTrace_append hprefix tailTrace_7941970
  have hstable : (prefixWord ++ tailWord_7941970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941970).length < 2 ^ (prefixWord ++ tailWord_7941970).sum := by decide
  have hdescent : baseEnd_7941970 < baseStart_7941970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941973 : List Nat := [1, 3, 2, 2, 2, 4, 2, 7]
def baseStart_7941973 : Nat := 118140960795 + 7941973 * 2 ^ 59
def prefixEnd_7941973 : Nat := 4983230072969 + 3 ^ 40 * 7941973 * 2
def baseEnd_7941973 : Nat := 151038870149272619548631

theorem tailTrace_7941973 : CollatzResearch.WordTrace tailWord_7941973 prefixEnd_7941973 151038870149272619548631 := by
  unfold tailWord_7941973
  simp only [CollatzResearch.WordTrace]
  refine ⟨289667552456595676846502573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193111701637730451231001715 289667552456595676846502573)
  ·
    refine ⟨108625332171223378817438465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289667552456595676846502573 108625332171223378817438465)
    ·
      refine ⟨81468999128417534113078849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108625332171223378817438465 81468999128417534113078849)
      ·
        refine ⟨61101749346313150584809137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81468999128417534113078849 61101749346313150584809137)
        ·
          refine ⟨45826312009734862938606853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61101749346313150584809137 45826312009734862938606853)
          ·
            refine ⟨8592433501825286800988785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45826312009734862938606853 8592433501825286800988785)
            ·
              refine ⟨6444325126368965100741589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8592433501825286800988785 6444325126368965100741589)
              ·
                refine ⟨151038870149272619548631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6444325126368965100741589 151038870149272619548631)
                ·
                  rfl

theorem cell23_7941973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 7].length) (baseStart_7941973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941973 prefixEnd_7941973 := by exact prefixLift 7941973
  have htrace : WordTrace (prefixWord ++ tailWord_7941973) baseStart_7941973 baseEnd_7941973 := by
    simpa [prefixWord, tailWord_7941973, baseEnd_7941973] using wordTrace_append hprefix tailTrace_7941973
  have hstable : (prefixWord ++ tailWord_7941973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941973).length < 2 ^ (prefixWord ++ tailWord_7941973).sum := by decide
  have hdescent : baseEnd_7941973 < baseStart_7941973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941983 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 3]
def baseStart_7941983 : Nat := 118140960795 + 7941983 * 2 ^ 59
def prefixEnd_7941983 : Nat := 4983230072969 + 3 ^ 40 * 7941983 * 2
def baseEnd_7941983 : Nat := 4078054628836905688687991

theorem tailTrace_7941983 : CollatzResearch.WordTrace tailWord_7941983 prefixEnd_7941983 4078054628836905688687991 := by
  unfold tailWord_7941983
  simp only [CollatzResearch.WordTrace]
  refine ⟨289667917186559448554366603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193111944791039632369577735 289667917186559448554366603)
  ·
    refine ⟨434501875779839172831549905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289667917186559448554366603 434501875779839172831549905)
    ·
      refine ⟨325876406834879379623662429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434501875779839172831549905 325876406834879379623662429)
      ·
        refine ⟨122203652563079767358873411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325876406834879379623662429 122203652563079767358873411)
        ·
          refine ⟨183305478844619651038310117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122203652563079767358873411 183305478844619651038310117)
          ·
            refine ⟨34369777283366184569683147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183305478844619651038310117 34369777283366184569683147)
            ·
              refine ⟨51554665925049276854524721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34369777283366184569683147 51554665925049276854524721)
              ·
                refine ⟨38665999443786957640893541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51554665925049276854524721 38665999443786957640893541)
                ·
                  refine ⟨7249874895710054557667539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38665999443786957640893541 7249874895710054557667539)
                  ·
                    refine ⟨10874812343565081836501309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7249874895710054557667539 10874812343565081836501309)
                    ·
                      refine ⟨4078054628836905688687991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10874812343565081836501309 4078054628836905688687991)
                      ·
                        rfl

theorem cell23_7941983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_7941983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941983 prefixEnd_7941983 := by exact prefixLift 7941983
  have htrace : WordTrace (prefixWord ++ tailWord_7941983) baseStart_7941983 baseEnd_7941983 := by
    simpa [prefixWord, tailWord_7941983, baseEnd_7941983] using wordTrace_append hprefix tailTrace_7941983
  have hstable : (prefixWord ++ tailWord_7941983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941983).length < 2 ^ (prefixWord ++ tailWord_7941983).sum := by decide
  have hdescent : baseEnd_7941983 < baseStart_7941983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7941984 : List Nat := [2, 1, 1, 3, 3, 4, 1, 3, 1, 2, 2]
def baseStart_7941984 : Nat := 118140960795 + 7941984 * 2 ^ 59
def prefixEnd_7941984 : Nat := 4983230072969 + 3 ^ 40 * 7941984 * 2
def baseEnd_7941984 : Nat := 4078055142317560184775487

theorem tailTrace_7941984 : CollatzResearch.WordTrace tailWord_7941984 prefixEnd_7941984 4078055142317560184775487 := by
  unfold tailWord_7941984
  simp only [CollatzResearch.WordTrace]
  refine ⟨144833976829777912862576503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193111969106370550483435337 144833976829777912862576503)
  ·
    refine ⟨217250965244666869293864755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144833976829777912862576503 217250965244666869293864755)
    ·
      refine ⟨325876447867000303940797133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217250965244666869293864755 325876447867000303940797133)
      ·
        refine ⟨122203667950125113977798925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325876447867000303940797133 122203667950125113977798925)
        ·
          refine ⟨45826375481296917741674597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122203667950125113977798925 45826375481296917741674597)
          ·
            refine ⟨8592445402743172076563987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45826375481296917741674597 8592445402743172076563987)
            ·
              refine ⟨12888668104114758114845981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8592445402743172076563987 12888668104114758114845981)
              ·
                refine ⟨4833250539043034293067243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12888668104114758114845981 4833250539043034293067243)
                ·
                  refine ⟨7249875808564551439600865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833250539043034293067243 7249875808564551439600865)
                  ·
                    refine ⟨5437406856423413579700649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7249875808564551439600865 5437406856423413579700649)
                    ·
                      refine ⟨4078055142317560184775487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437406856423413579700649 4078055142317560184775487)
                      ·
                        rfl

theorem cell23_7941984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_7941984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7941984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7941984 prefixEnd_7941984 := by exact prefixLift 7941984
  have htrace : WordTrace (prefixWord ++ tailWord_7941984) baseStart_7941984 baseEnd_7941984 := by
    simpa [prefixWord, tailWord_7941984, baseEnd_7941984] using wordTrace_append hprefix tailTrace_7941984
  have hstable : (prefixWord ++ tailWord_7941984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7941984).length < 2 ^ (prefixWord ++ tailWord_7941984).sum := by decide
  have hdescent : baseEnd_7941984 < baseStart_7941984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7941984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942044 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7942044 : Nat := 118140960795 + 7942044 * 2 ^ 59
def prefixEnd_7942044 : Nat := 4983230072969 + 3 ^ 40 * 7942044 * 2
def baseEnd_7942044 : Nat := 4078085951156829950025211

theorem tailTrace_7942044 : CollatzResearch.WordTrace tailWord_7942044 prefixEnd_7942044 4078085951156829950025211 := by
  unfold tailWord_7942044
  simp only [CollatzResearch.WordTrace]
  refine ⟨144835071019669227986168593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193113428026225637314891457 144835071019669227986168593)
  ·
    refine ⟨108626303264751920989626445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144835071019669227986168593 108626303264751920989626445)
    ·
      refine ⟨40734863724281970371109917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108626303264751920989626445 40734863724281970371109917)
      ·
        refine ⟨15275573896605738889166219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40734863724281970371109917 15275573896605738889166219)
        ·
          refine ⟨22913360844908608333749329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15275573896605738889166219 22913360844908608333749329)
          ·
            refine ⟨17185020633681456250311997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22913360844908608333749329 17185020633681456250311997)
            ·
              refine ⟨6444382737630546093866999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17185020633681456250311997 6444382737630546093866999)
              ·
                refine ⟨9666574106445819140800499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444382737630546093866999 9666574106445819140800499)
                ·
                  refine ⟨14499861159668728711200749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9666574106445819140800499 14499861159668728711200749)
                  ·
                    refine ⟨5437447934875773266700281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14499861159668728711200749 5437447934875773266700281)
                    ·
                      refine ⟨4078085951156829950025211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5437447934875773266700281 4078085951156829950025211)
                      ·
                        rfl

theorem cell23_7942044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7942044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942044 prefixEnd_7942044 := by exact prefixLift 7942044
  have htrace : WordTrace (prefixWord ++ tailWord_7942044) baseStart_7942044 baseEnd_7942044 := by
    simpa [prefixWord, tailWord_7942044, baseEnd_7942044] using wordTrace_append hprefix tailTrace_7942044
  have hstable : (prefixWord ++ tailWord_7942044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942044).length < 2 ^ (prefixWord ++ tailWord_7942044).sum := by decide
  have hdescent : baseEnd_7942044 < baseStart_7942044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942063 : List Nat := [1, 1, 2, 1, 2, 2, 5, 4, 5]
def baseStart_7942063 : Nat := 118140960795 + 7942063 * 2 ^ 59
def prefixEnd_7942063 : Nat := 4983230072969 + 3 ^ 40 * 7942063 * 2
def baseEnd_7942063 : Nat := 453121745254362819520847

theorem tailTrace_7942063 : CollatzResearch.WordTrace tailWord_7942063 prefixEnd_7942063 453121745254362819520847 := by
  unfold tailWord_7942063
  simp only [CollatzResearch.WordTrace]
  refine ⟨289670835026269622217278843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193113890017513081478185895 289670835026269622217278843)
  ·
    refine ⟨434506252539404433325918265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289670835026269622217278843 434506252539404433325918265)
    ·
      refine ⟨325879689404553324994438699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434506252539404433325918265 325879689404553324994438699)
      ·
        refine ⟨488819534106829987491658049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325879689404553324994438699 488819534106829987491658049)
        ·
          refine ⟨366614650580122490618743537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488819534106829987491658049 366614650580122490618743537)
          ·
            refine ⟨274960987935091867964057653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366614650580122490618743537 274960987935091867964057653)
            ·
              refine ⟨25777592618914862621630405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274960987935091867964057653 25777592618914862621630405)
              ·
                refine ⟨4833298616046536741555701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25777592618914862621630405 4833298616046536741555701)
                ·
                  refine ⟨453121745254362819520847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4833298616046536741555701 453121745254362819520847)
                  ·
                    rfl

theorem cell23_7942063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 5].length) (baseStart_7942063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942063 prefixEnd_7942063 := by exact prefixLift 7942063
  have htrace : WordTrace (prefixWord ++ tailWord_7942063) baseStart_7942063 baseEnd_7942063 := by
    simpa [prefixWord, tailWord_7942063, baseEnd_7942063] using wordTrace_append hprefix tailTrace_7942063
  have hstable : (prefixWord ++ tailWord_7942063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942063).length < 2 ^ (prefixWord ++ tailWord_7942063).sum := by decide
  have hdescent : baseEnd_7942063 < baseStart_7942063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942073 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 3]
def baseStart_7942073 : Nat := 118140960795 + 7942073 * 2 ^ 59
def prefixEnd_7942073 : Nat := 4983230072969 + 3 ^ 40 * 7942073 * 2
def baseEnd_7942073 : Nat := 4078100842095810336562577

theorem tailTrace_7942073 : CollatzResearch.WordTrace tailWord_7942073 prefixEnd_7942073 4078100842095810336562577 := by
  unfold tailWord_7942073
  simp only [CollatzResearch.WordTrace]
  refine ⟨289671199756233393925142873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193114133170822262616761915 289671199756233393925142873)
  ·
    refine ⟨217253399817175045443857155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289671199756233393925142873 217253399817175045443857155)
    ·
      refine ⟨325880099725762568165785733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217253399817175045443857155 325880099725762568165785733)
      ·
        refine ⟨61102518698580481531084825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325880099725762568165785733 61102518698580481531084825)
        ·
          refine ⟨45826889023935361148313619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61102518698580481531084825 45826889023935361148313619)
          ·
            refine ⟨68740333535903041722470429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45826889023935361148313619 68740333535903041722470429)
            ·
              refine ⟨25777625075963640645926411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68740333535903041722470429 25777625075963640645926411)
              ·
                refine ⟨38666437613945460968889617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25777625075963640645926411 38666437613945460968889617)
                ·
                  refine ⟨28999828210459095726667213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38666437613945460968889617 28999828210459095726667213)
                  ·
                    refine ⟨10874935578922160897500205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28999828210459095726667213 10874935578922160897500205)
                    ·
                      refine ⟨4078100842095810336562577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10874935578922160897500205 4078100842095810336562577)
                      ·
                        rfl

theorem cell23_7942073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_7942073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942073 prefixEnd_7942073 := by exact prefixLift 7942073
  have htrace : WordTrace (prefixWord ++ tailWord_7942073) baseStart_7942073 baseEnd_7942073 := by
    simpa [prefixWord, tailWord_7942073, baseEnd_7942073] using wordTrace_append hprefix tailTrace_7942073
  have hstable : (prefixWord ++ tailWord_7942073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942073).length < 2 ^ (prefixWord ++ tailWord_7942073).sum := by decide
  have hdescent : baseEnd_7942073 < baseStart_7942073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942113 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7942113 : Nat := 118140960795 + 7942113 * 2 ^ 59
def prefixEnd_7942113 : Nat := 4983230072969 + 3 ^ 40 * 7942113 * 2
def baseEnd_7942113 : Nat := 4078121381321990180062393

theorem tailTrace_7942113 : CollatzResearch.WordTrace tailWord_7942113 prefixEnd_7942113 4078121381321990180062393 := by
  unfold tailWord_7942113
  simp only [CollatzResearch.WordTrace]
  refine ⟨289672658676088480756598993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193115105784058987171065995 289672658676088480756598993)
  ·
    refine ⟨217254494007066360567449245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289672658676088480756598993 217254494007066360567449245)
    ·
      refine ⟨81470435252649885212793467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217254494007066360567449245 81470435252649885212793467)
      ·
        refine ⟨122205652878974827819190201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81470435252649885212793467 122205652878974827819190201)
        ·
          refine ⟨91654239659231120864392651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122205652878974827819190201 91654239659231120864392651)
          ·
            refine ⟨137481359488846681296588977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91654239659231120864392651 137481359488846681296588977)
            ·
              refine ⟨103111019616635010972441733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137481359488846681296588977 103111019616635010972441733)
              ·
                refine ⟨19333316178119064557332825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103111019616635010972441733 19333316178119064557332825)
                ·
                  refine ⟨14499987133589298417999619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19333316178119064557332825 14499987133589298417999619)
                  ·
                    refine ⟨21749980700383947626999429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14499987133589298417999619 21749980700383947626999429)
                    ·
                      refine ⟨4078121381321990180062393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21749980700383947626999429 4078121381321990180062393)
                      ·
                        rfl

theorem cell23_7942113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7942113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942113 prefixEnd_7942113 := by exact prefixLift 7942113
  have htrace : WordTrace (prefixWord ++ tailWord_7942113) baseStart_7942113 baseEnd_7942113 := by
    simpa [prefixWord, tailWord_7942113, baseEnd_7942113] using wordTrace_append hprefix tailTrace_7942113
  have hstable : (prefixWord ++ tailWord_7942113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942113).length < 2 ^ (prefixWord ++ tailWord_7942113).sum := by decide
  have hdescent : baseEnd_7942113 < baseStart_7942113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942164 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7942164 : Nat := 118140960795 + 7942164 * 2 ^ 59
def prefixEnd_7942164 : Nat := 4983230072969 + 3 ^ 40 * 7942164 * 2
def baseEnd_7942164 : Nat := 4078147568835369480524659

theorem tailTrace_7942164 : CollatzResearch.WordTrace tailWord_7942164 prefixEnd_7942164 4078147568835369480524659 := by
  unfold tailWord_7942164
  simp only [CollatzResearch.WordTrace]
  refine ⟨144837259399451858233352773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193116345865935810977803697 144837259399451858233352773)
  ·
    refine ⟨27156986137397223418753645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144837259399451858233352773 27156986137397223418753645)
    ·
      refine ⟨10183869801523958782032617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27156986137397223418753645 10183869801523958782032617)
      ·
        refine ⟨7637902351142969086524463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10183869801523958782032617 7637902351142969086524463)
        ·
          refine ⟨11456853526714453629786695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7637902351142969086524463 11456853526714453629786695)
          ·
            refine ⟨17185280290071680444680043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11456853526714453629786695 17185280290071680444680043)
            ·
              refine ⟨25777920435107520667020065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17185280290071680444680043 25777920435107520667020065)
              ·
                refine ⟨19333440326330640500265049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25777920435107520667020065 19333440326330640500265049)
                ·
                  refine ⟨14500080244747980375198787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19333440326330640500265049 14500080244747980375198787)
                  ·
                    refine ⟨21750120367121970562798181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14500080244747980375198787 21750120367121970562798181)
                    ·
                      refine ⟨4078147568835369480524659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21750120367121970562798181 4078147568835369480524659)
                      ·
                        rfl

theorem cell23_7942164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7942164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942164 prefixEnd_7942164 := by exact prefixLift 7942164
  have htrace : WordTrace (prefixWord ++ tailWord_7942164) baseStart_7942164 baseEnd_7942164 := by
    simpa [prefixWord, tailWord_7942164, baseEnd_7942164] using wordTrace_append hprefix tailTrace_7942164
  have hstable : (prefixWord ++ tailWord_7942164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942164).length < 2 ^ (prefixWord ++ tailWord_7942164).sum := by decide
  have hdescent : baseEnd_7942164 < baseStart_7942164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7942167 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7942167 : Nat := 118140960795 + 7942167 * 2 ^ 59
def prefixEnd_7942167 : Nat := 4983230072969 + 3 ^ 40 * 7942167 * 2
def baseEnd_7942167 : Nat := 4078149109277332968787145

theorem tailTrace_7942167 : CollatzResearch.WordTrace tailWord_7942167 prefixEnd_7942167 4078149109277332968787145 := by
  unfold tailWord_7942167
  simp only [CollatzResearch.WordTrace]
  refine ⟨289674628217892847979064755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193116418811928565319376503 289674628217892847979064755)
  ·
    refine ⟨434511942326839271968597133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289674628217892847979064755 434511942326839271968597133)
    ·
      refine ⟨162941978372564726988223925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434511942326839271968597133 162941978372564726988223925)
      ·
        refine ⟨15275810472427943155145993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162941978372564726988223925 15275810472427943155145993)
        ·
          refine ⟨11456857854320957366359495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15275810472427943155145993 11456857854320957366359495)
          ·
            refine ⟨17185286781481436049539243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11456857854320957366359495 17185286781481436049539243)
            ·
              refine ⟨25777930172222154074308865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17185286781481436049539243 25777930172222154074308865)
              ·
                refine ⟨19333447629166615555731649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25777930172222154074308865 19333447629166615555731649)
                ·
                  refine ⟨14500085721874961666798737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19333447629166615555731649 14500085721874961666798737)
                  ·
                    refine ⟨10875064291406221250099053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14500085721874961666798737 10875064291406221250099053)
                    ·
                      refine ⟨4078149109277332968787145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10875064291406221250099053 4078149109277332968787145)
                      ·
                        rfl

theorem cell23_7942167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7942167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7942167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7942167 prefixEnd_7942167 := by exact prefixLift 7942167
  have htrace : WordTrace (prefixWord ++ tailWord_7942167) baseStart_7942167 baseEnd_7942167 := by
    simpa [prefixWord, tailWord_7942167, baseEnd_7942167] using wordTrace_append hprefix tailTrace_7942167
  have hstable : (prefixWord ++ tailWord_7942167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7942167).length < 2 ^ (prefixWord ++ tailWord_7942167).sum := by decide
  have hdescent : baseEnd_7942167 < baseStart_7942167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7942167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
