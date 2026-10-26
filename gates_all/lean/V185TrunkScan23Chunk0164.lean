import V185TrunkScan23Chunk0163

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_970165 : List Nat := [1, 3, 3, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_970165 : Nat := 118140960795 + 970165 * 2 ^ 59
def prefixEnd_970165 : Nat := 4983230072969 + 3 ^ 40 * 970165 * 2
def baseEnd_970165 : Nat := 498160959169301958675799

theorem tailTrace_970165 : CollatzResearch.WordTrace tailWord_970165 prefixEnd_970165 498160959169301958675799 := by
  unfold tailWord_970165
  simp only [CollatzResearch.WordTrace]
  refine ⟨35384824530265370835775949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23589883020176913890517299 35384824530265370835775949)
  ·
    refine ⟨13269309198849514063415981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35384824530265370835775949 13269309198849514063415981)
    ·
      refine ⟨4975990949568567773780993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13269309198849514063415981 4975990949568567773780993)
      ·
        refine ⟨3731993212176425830335745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4975990949568567773780993 3731993212176425830335745)
        ·
          refine ⟨2798994909132319372751809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3731993212176425830335745 2798994909132319372751809)
          ·
            refine ⟨2099246181849239529563857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2798994909132319372751809 2099246181849239529563857)
            ·
              refine ⟨1574434636386929647172893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2099246181849239529563857 1574434636386929647172893)
              ·
                refine ⟨590412988645098617689835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1574434636386929647172893 590412988645098617689835)
                ·
                  refine ⟨885619482967647926534753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590412988645098617689835 885619482967647926534753)
                  ·
                    refine ⟨664214612225735944901065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 885619482967647926534753 664214612225735944901065)
                    ·
                      refine ⟨498160959169301958675799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664214612225735944901065 498160959169301958675799)
                      ·
                        rfl

theorem cell23_970165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_970165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970165 prefixEnd_970165 := by exact prefixLift 970165
  have htrace : WordTrace (prefixWord ++ tailWord_970165) baseStart_970165 baseEnd_970165 := by
    simpa [prefixWord, tailWord_970165, baseEnd_970165] using wordTrace_append hprefix tailTrace_970165
  have hstable : (prefixWord ++ tailWord_970165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970165).length < 2 ^ (prefixWord ++ tailWord_970165).sum := by decide
  have hdescent : baseEnd_970165 < baseStart_970165 := by decide
  rcases family_descends (prefixWord ++ tailWord_970165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970197 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_970197 : Nat := 118140960795 + 970197 * 2 ^ 59
def prefixEnd_970197 : Nat := 4983230072969 + 3 ^ 40 * 970197 * 2
def baseEnd_970197 : Nat := 166059130183415277825217

theorem tailTrace_970197 : CollatzResearch.WordTrace tailWord_970197 prefixEnd_970197 166059130183415277825217 := by
  unfold tailWord_970197
  simp only [CollatzResearch.WordTrace]
  refine ⟨35385991666149440300940845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23590661110766293533960563 35385991666149440300940845)
  ·
    refine ⟨13269746874806040112852817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35385991666149440300940845 13269746874806040112852817)
    ·
      refine ⟨9952310156104530084639613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13269746874806040112852817 9952310156104530084639613)
      ·
        refine ⟨3732116308539198781739855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9952310156104530084639613 3732116308539198781739855)
        ·
          refine ⟨5598174462808798172609783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732116308539198781739855 5598174462808798172609783)
          ·
            refine ⟨8397261694213197258914675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598174462808798172609783 8397261694213197258914675)
            ·
              refine ⟨12595892541319795888372013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397261694213197258914675 12595892541319795888372013)
              ·
                refine ⟨4723459702994923458139505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12595892541319795888372013 4723459702994923458139505)
                ·
                  refine ⟨3542594777246192593604629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723459702994923458139505 3542594777246192593604629)
                  ·
                    refine ⟨166059130183415277825217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3542594777246192593604629 166059130183415277825217)
                    ·
                      rfl

theorem cell23_970197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_970197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970197 prefixEnd_970197 := by exact prefixLift 970197
  have htrace : WordTrace (prefixWord ++ tailWord_970197) baseStart_970197 baseEnd_970197 := by
    simpa [prefixWord, tailWord_970197, baseEnd_970197] using wordTrace_append hprefix tailTrace_970197
  have hstable : (prefixWord ++ tailWord_970197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970197).length < 2 ^ (prefixWord ++ tailWord_970197).sum := by decide
  have hdescent : baseEnd_970197 < baseStart_970197 := by decide
  rcases family_descends (prefixWord ++ tailWord_970197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970198 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_970198 : Nat := 118140960795 + 970198 * 2 ^ 59
def prefixEnd_970198 : Nat := 4983230072969 + 3 ^ 40 * 970198 * 2
def baseEnd_970198 : Nat := 498177904030900329563147

theorem tailTrace_970198 : CollatzResearch.WordTrace tailWord_970198 prefixEnd_970198 498177904030900329563147 := by
  unfold tailWord_970198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211626758696613591982953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23590685426097211647818165 2211626758696613591982953)
  ·
    refine ⟨1658720069022460193987215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2211626758696613591982953 1658720069022460193987215)
    ·
      refine ⟨2488080103533690290980823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658720069022460193987215 2488080103533690290980823)
      ·
        refine ⟨3732120155300535436471235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488080103533690290980823 3732120155300535436471235)
        ·
          refine ⟨5598180232950803154706853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732120155300535436471235 5598180232950803154706853)
          ·
            refine ⟨1049658793678275591507535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5598180232950803154706853 1049658793678275591507535)
            ·
              refine ⟨1574488190517413387261303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049658793678275591507535 1574488190517413387261303)
              ·
                refine ⟨2361732285776120080891955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574488190517413387261303 2361732285776120080891955)
                ·
                  refine ⟨3542598428664180121337933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361732285776120080891955 3542598428664180121337933)
                  ·
                    refine ⟨1328474410749067545501725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3542598428664180121337933 1328474410749067545501725)
                    ·
                      refine ⟨498177904030900329563147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1328474410749067545501725 498177904030900329563147)
                      ·
                        rfl

theorem cell23_970198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_970198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970198 prefixEnd_970198 := by exact prefixLift 970198
  have htrace : WordTrace (prefixWord ++ tailWord_970198) baseStart_970198 baseEnd_970198 := by
    simpa [prefixWord, tailWord_970198, baseEnd_970198] using wordTrace_append hprefix tailTrace_970198
  have hstable : (prefixWord ++ tailWord_970198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970198).length < 2 ^ (prefixWord ++ tailWord_970198).sum := by decide
  have hdescent : baseEnd_970198 < baseStart_970198 := by decide
  rcases family_descends (prefixWord ++ tailWord_970198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970207 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_970207 : Nat := 118140960795 + 970207 * 2 ^ 59
def prefixEnd_970207 : Nat := 4983230072969 + 3 ^ 40 * 970207 * 2
def baseEnd_970207 : Nat := 498182525356790794350605

theorem tailTrace_970207 : CollatzResearch.WordTrace tailWord_970207 prefixEnd_970207 498182525356790794350605 := by
  unfold tailWord_970207
  simp only [CollatzResearch.WordTrace]
  refine ⟨35386356396113212008804875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23590904264075474672536583 35386356396113212008804875)
  ·
    refine ⟨53079534594169818013207313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35386356396113212008804875 53079534594169818013207313)
    ·
      refine ⟨39809650945627363509905485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53079534594169818013207313 39809650945627363509905485)
      ·
        refine ⟨14928619104610261316214557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39809650945627363509905485 14928619104610261316214557)
        ·
          refine ⟨5598232164228847993580459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14928619104610261316214557 5598232164228847993580459)
          ·
            refine ⟨8397348246343271990370689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598232164228847993580459 8397348246343271990370689)
            ·
              refine ⟨6298011184757453992778017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8397348246343271990370689 6298011184757453992778017)
              ·
                refine ⟨4723508388568090494583513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298011184757453992778017 4723508388568090494583513)
                ·
                  refine ⟨3542631291426067870937635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723508388568090494583513 3542631291426067870937635)
                  ·
                    refine ⟨5313946937139101806406453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542631291426067870937635 5313946937139101806406453)
                    ·
                      refine ⟨498182525356790794350605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5313946937139101806406453 498182525356790794350605)
                      ·
                        rfl

theorem cell23_970207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_970207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970207 prefixEnd_970207 := by exact prefixLift 970207
  have htrace : WordTrace (prefixWord ++ tailWord_970207) baseStart_970207 baseEnd_970207 := by
    simpa [prefixWord, tailWord_970207, baseEnd_970207] using wordTrace_append hprefix tailTrace_970207
  have hstable : (prefixWord ++ tailWord_970207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970207).length < 2 ^ (prefixWord ++ tailWord_970207).sum := by decide
  have hdescent : baseEnd_970207 < baseStart_970207 := by decide
  rcases family_descends (prefixWord ++ tailWord_970207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970257 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 4, 5]
def baseStart_970257 : Nat := 118140960795 + 970257 * 2 ^ 59
def prefixEnd_970257 : Nat := 4983230072969 + 3 ^ 40 * 970257 * 2
def baseEnd_970257 : Nat := 166069399796505199575125

theorem tailTrace_970257 : CollatzResearch.WordTrace tailWord_970257 prefixEnd_970257 166069399796505199575125 := by
  unfold tailWord_970257
  simp only [CollatzResearch.WordTrace]
  refine ⟨35388180045932070548125025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23592120030621380365416683 35388180045932070548125025)
  ·
    refine ⟨26541135034449052911093769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35388180045932070548125025 26541135034449052911093769)
    ·
      refine ⟨19905851275836789683320327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26541135034449052911093769 19905851275836789683320327)
      ·
        refine ⟨29858776913755184524980491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19905851275836789683320327 29858776913755184524980491)
        ·
          refine ⟨44788165370632776787470737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29858776913755184524980491 44788165370632776787470737)
          ·
            refine ⟨33591124027974582590603053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44788165370632776787470737 33591124027974582590603053)
            ·
              refine ⟨12596671510490468471476145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33591124027974582590603053 12596671510490468471476145)
              ·
                refine ⟨9447503632867851353607109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12596671510490468471476145 9447503632867851353607109)
                ·
                  refine ⟨1771406931162722128801333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9447503632867851353607109 1771406931162722128801333)
                  ·
                    refine ⟨166069399796505199575125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1771406931162722128801333 166069399796505199575125)
                    ·
                      rfl

theorem cell23_970257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_970257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970257 prefixEnd_970257 := by exact prefixLift 970257
  have htrace : WordTrace (prefixWord ++ tailWord_970257) baseStart_970257 baseEnd_970257 := by
    simpa [prefixWord, tailWord_970257, baseEnd_970257] using wordTrace_append hprefix tailTrace_970257
  have hstable : (prefixWord ++ tailWord_970257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970257).length < 2 ^ (prefixWord ++ tailWord_970257).sum := by decide
  have hdescent : baseEnd_970257 < baseStart_970257 := by decide
  rcases family_descends (prefixWord ++ tailWord_970257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970274 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_970274 : Nat := 118140960795 + 970274 * 2 ^ 59
def prefixEnd_970274 : Nat := 4983230072969 + 3 ^ 40 * 970274 * 2
def baseEnd_970274 : Nat := 166072309520214010737599

theorem tailTrace_970274 : CollatzResearch.WordTrace tailWord_970274 prefixEnd_970274 166072309520214010737599 := by
  unfold tailWord_970274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847200021717620612873469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23592533391246988300995917 8847200021717620612873469)
  ·
    refine ⟨3317700008144107729827551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8847200021717620612873469 3317700008144107729827551)
    ·
      refine ⟨4976550012216161594741327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3317700008144107729827551 4976550012216161594741327)
      ·
        refine ⟨7464825018324242392111991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976550012216161594741327 7464825018324242392111991)
        ·
          refine ⟨11197237527486363588167987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464825018324242392111991 11197237527486363588167987)
          ·
            refine ⟨16795856291229545382251981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197237527486363588167987 16795856291229545382251981)
            ·
              refine ⟨6298446109211079518344493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16795856291229545382251981 6298446109211079518344493)
              ·
                refine ⟨2361917290954154819379185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298446109211079518344493 2361917290954154819379185)
                ·
                  refine ⟨1771437968215616114534389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2361917290954154819379185 1771437968215616114534389)
                  ·
                    refine ⟨166072309520214010737599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1771437968215616114534389 166072309520214010737599)
                    ·
                      rfl

theorem cell23_970274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_970274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970274 prefixEnd_970274 := by exact prefixLift 970274
  have htrace : WordTrace (prefixWord ++ tailWord_970274) baseStart_970274 baseEnd_970274 := by
    simpa [prefixWord, tailWord_970274, baseEnd_970274] using wordTrace_append hprefix tailTrace_970274
  have hstable : (prefixWord ++ tailWord_970274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970274).length < 2 ^ (prefixWord ++ tailWord_970274).sum := by decide
  have hdescent : baseEnd_970274 < baseStart_970274 := by decide
  rcases family_descends (prefixWord ++ tailWord_970274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970304 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 3, 4]
def baseStart_970304 : Nat := 118140960795 + 970304 * 2 ^ 59
def prefixEnd_970304 : Nat := 4983230072969 + 3 ^ 40 * 970304 * 2
def baseEnd_970304 : Nat := 166077444326758971612553

theorem tailTrace_970304 : CollatzResearch.WordTrace tailWord_970304 prefixEnd_970304 166077444326758971612553 := by
  unfold tailWord_970304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694947138380898787542983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23593262851174531716723977 17694947138380898787542983)
  ·
    refine ⟨26542420707571348181314475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17694947138380898787542983 26542420707571348181314475)
    ·
      refine ⟨39813631061357022271971713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26542420707571348181314475 39813631061357022271971713)
      ·
        refine ⟨29860223296017766703978785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39813631061357022271971713 29860223296017766703978785)
        ·
          refine ⟨22395167472013325027984089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29860223296017766703978785 22395167472013325027984089)
          ·
            refine ⟨16796375604009993770988067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22395167472013325027984089 16796375604009993770988067)
            ·
              refine ⟨25194563406014990656482101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16796375604009993770988067 25194563406014990656482101)
              ·
                refine ⟨2361990319313905374045197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25194563406014990656482101 2361990319313905374045197)
                ·
                  refine ⟨885746369742714515266949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2361990319313905374045197 885746369742714515266949)
                  ·
                    refine ⟨166077444326758971612553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885746369742714515266949 166077444326758971612553)
                    ·
                      rfl

theorem cell23_970304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_970304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970304 prefixEnd_970304 := by exact prefixLift 970304
  have htrace : WordTrace (prefixWord ++ tailWord_970304) baseStart_970304 baseEnd_970304 := by
    simpa [prefixWord, tailWord_970304, baseEnd_970304] using wordTrace_append hprefix tailTrace_970304
  have hstable : (prefixWord ++ tailWord_970304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970304).length < 2 ^ (prefixWord ++ tailWord_970304).sum := by decide
  have hdescent : baseEnd_970304 < baseStart_970304 := by decide
  rcases family_descends (prefixWord ++ tailWord_970304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970307 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4]
def baseStart_970307 : Nat := 118140960795 + 970307 * 2 ^ 59
def prefixEnd_970307 : Nat := 4983230072969 + 3 ^ 40 * 970307 * 2
def baseEnd_970307 : Nat := 498233873422240403100145

theorem tailTrace_970307 : CollatzResearch.WordTrace tailWord_970307 prefixEnd_970307 498233873422240403100145 := by
  unfold tailWord_970307
  simp only [CollatzResearch.WordTrace]
  refine ⟨35390003695750929087445175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23593335797167286058296783 35390003695750929087445175)
  ·
    refine ⟨53085005543626393631167763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35390003695750929087445175 53085005543626393631167763)
    ·
      refine ⟨79627508315439590446751645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53085005543626393631167763 79627508315439590446751645)
      ·
        refine ⟨29860315618289846417531867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79627508315439590446751645 29860315618289846417531867)
        ·
          refine ⟨44790473427434769626297801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29860315618289846417531867 44790473427434769626297801)
          ·
            refine ⟨33592855070576077219723351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44790473427434769626297801 33592855070576077219723351)
            ·
              refine ⟨50389282605864115829585027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33592855070576077219723351 50389282605864115829585027)
              ·
                refine ⟨75583923908796173744377541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50389282605864115829585027 75583923908796173744377541)
                ·
                  refine ⟨14171985732899282577070789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75583923908796173744377541 14171985732899282577070789)
                  ·
                    refine ⟨2657247324918615483200773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14171985732899282577070789 2657247324918615483200773)
                    ·
                      refine ⟨498233873422240403100145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2657247324918615483200773 498233873422240403100145)
                      ·
                        rfl

theorem cell23_970307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_970307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970307 prefixEnd_970307 := by exact prefixLift 970307
  have htrace : WordTrace (prefixWord ++ tailWord_970307) baseStart_970307 baseEnd_970307 := by
    simpa [prefixWord, tailWord_970307, baseEnd_970307] using wordTrace_append hprefix tailTrace_970307
  have hstable : (prefixWord ++ tailWord_970307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970307).length < 2 ^ (prefixWord ++ tailWord_970307).sum := by decide
  have hdescent : baseEnd_970307 < baseStart_970307 := by decide
  rcases family_descends (prefixWord ++ tailWord_970307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970314 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_970314 : Nat := 118140960795 + 970314 * 2 ^ 59
def prefixEnd_970314 : Nat := 4983230072969 + 3 ^ 40 * 970314 * 2
def baseEnd_970314 : Nat := 498237467786821875712613

theorem tailTrace_970314 : CollatzResearch.WordTrace tailWord_970314 prefixEnd_970314 498237467786821875712613 := by
  unfold tailWord_970314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847564751681392320737499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23593506004483712855299997 8847564751681392320737499)
  ·
    refine ⟨13271347127522088481106249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8847564751681392320737499 13271347127522088481106249)
    ·
      refine ⟨9953510345641566360829687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13271347127522088481106249 9953510345641566360829687)
      ·
        refine ⟨14930265518462349541244531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9953510345641566360829687 14930265518462349541244531)
        ·
          refine ⟨22395398277693524311866797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14930265518462349541244531 22395398277693524311866797)
          ·
            refine ⟨8398274354135071616950049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22395398277693524311866797 8398274354135071616950049)
            ·
              refine ⟨6298705765601303712712537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398274354135071616950049 6298705765601303712712537)
              ·
                refine ⟨4724029324200977784534403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298705765601303712712537 4724029324200977784534403)
                ·
                  refine ⟨7086043986301466676801605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724029324200977784534403 7086043986301466676801605)
                  ·
                    refine ⟨1328633247431525001900301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7086043986301466676801605 1328633247431525001900301)
                    ·
                      refine ⟨498237467786821875712613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1328633247431525001900301 498237467786821875712613)
                      ·
                        rfl

theorem cell23_970314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_970314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970314 prefixEnd_970314 := by exact prefixLift 970314
  have htrace : WordTrace (prefixWord ++ tailWord_970314) baseStart_970314 baseEnd_970314 := by
    simpa [prefixWord, tailWord_970314, baseEnd_970314] using wordTrace_append hprefix tailTrace_970314
  have hstable : (prefixWord ++ tailWord_970314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970314).length < 2 ^ (prefixWord ++ tailWord_970314).sum := by decide
  have hdescent : baseEnd_970314 < baseStart_970314 := by decide
  rcases family_descends (prefixWord ++ tailWord_970314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970354 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_970354 : Nat := 118140960795 + 970354 * 2 ^ 59
def prefixEnd_970354 : Nat := 4983230072969 + 3 ^ 40 * 970354 * 2
def baseEnd_970354 : Nat := 498258007013001719212429

theorem tailTrace_970354 : CollatzResearch.WordTrace tailWord_970354 prefixEnd_970354 498258007013001719212429 := by
  unfold tailWord_970354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847929481645164028601529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23594478617720437409604077 8847929481645164028601529)
  ·
    refine ⟨6635947111233873021451147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8847929481645164028601529 6635947111233873021451147)
    ·
      refine ⟨9953920666850809532176721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6635947111233873021451147 9953920666850809532176721)
      ·
        refine ⟨7465440500138107149132541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9953920666850809532176721 7465440500138107149132541)
        ·
          refine ⟨2799540187551790180924703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7465440500138107149132541 2799540187551790180924703)
          ·
            refine ⟨4199310281327685271387055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799540187551790180924703 4199310281327685271387055)
            ·
              refine ⟨6298965421991527907080583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199310281327685271387055 6298965421991527907080583)
              ·
                refine ⟨9448448132987291860620875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298965421991527907080583 9448448132987291860620875)
                ·
                  refine ⟨14172672199480937790931313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9448448132987291860620875 14172672199480937790931313)
                  ·
                    refine ⟨10629504149610703343198485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14172672199480937790931313 10629504149610703343198485)
                    ·
                      refine ⟨498258007013001719212429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10629504149610703343198485 498258007013001719212429)
                      ·
                        rfl

theorem cell23_970354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_970354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970354 prefixEnd_970354 := by exact prefixLift 970354
  have htrace : WordTrace (prefixWord ++ tailWord_970354) baseStart_970354 baseEnd_970354 := by
    simpa [prefixWord, tailWord_970354, baseEnd_970354] using wordTrace_append hprefix tailTrace_970354
  have hstable : (prefixWord ++ tailWord_970354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970354).length < 2 ^ (prefixWord ++ tailWord_970354).sum := by decide
  have hdescent : baseEnd_970354 < baseStart_970354 := by decide
  rcases family_descends (prefixWord ++ tailWord_970354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970378 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_970378 : Nat := 118140960795 + 970378 * 2 ^ 59
def prefixEnd_970378 : Nat := 4983230072969 + 3 ^ 40 * 970378 * 2
def baseEnd_970378 : Nat := 498270330548709625312319

theorem tailTrace_970378 : CollatzResearch.WordTrace tailWord_970378 prefixEnd_970378 498270330548709625312319 := by
  unfold tailWord_970378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8848148319623427053319947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23595062185662472142186525 8848148319623427053319947)
  ·
    refine ⟨13272222479435140579979921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8848148319623427053319947 13272222479435140579979921)
    ·
      refine ⟨9954166859576355434984941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13272222479435140579979921 9954166859576355434984941)
      ·
        refine ⟨3732812572341133288119353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9954166859576355434984941 3732812572341133288119353)
        ·
          refine ⟨2799609429255849966089515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3732812572341133288119353 2799609429255849966089515)
          ·
            refine ⟨4199414143883774949134273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799609429255849966089515 4199414143883774949134273)
            ·
              refine ⟨3149560607912831211850705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4199414143883774949134273 3149560607912831211850705)
              ·
                refine ⟨2362170455934623408888029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149560607912831211850705 2362170455934623408888029)
                ·
                  refine ⟨885813920975483778333011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2362170455934623408888029 885813920975483778333011)
                  ·
                    refine ⟨1328720881463225667499517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 885813920975483778333011 1328720881463225667499517)
                    ·
                      refine ⟨498270330548709625312319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1328720881463225667499517 498270330548709625312319)
                      ·
                        rfl

theorem cell23_970378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_970378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970378 prefixEnd_970378 := by exact prefixLift 970378
  have htrace : WordTrace (prefixWord ++ tailWord_970378) baseStart_970378 baseEnd_970378 := by
    simpa [prefixWord, tailWord_970378, baseEnd_970378] using wordTrace_append hprefix tailTrace_970378
  have hstable : (prefixWord ++ tailWord_970378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970378).length < 2 ^ (prefixWord ++ tailWord_970378).sum := by decide
  have hdescent : baseEnd_970378 < baseStart_970378 := by decide
  rcases family_descends (prefixWord ++ tailWord_970378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970384 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_970384 : Nat := 118140960795 + 970384 * 2 ^ 59
def prefixEnd_970384 : Nat := 4983230072969 + 3 ^ 40 * 970384 * 2
def baseEnd_970384 : Nat := 498273411432636601837291

theorem tailTrace_970384 : CollatzResearch.WordTrace tailWord_970384 prefixEnd_970384 498273411432636601837291 := by
  unfold tailWord_970384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17696406058235985618999103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23595208077647980825332137 17696406058235985618999103)
  ·
    refine ⟨26544609087353978428498655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17696406058235985618999103 26544609087353978428498655)
    ·
      refine ⟨39816913631030967642747983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26544609087353978428498655 39816913631030967642747983)
      ·
        refine ⟨59725370446546451464121975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39816913631030967642747983 59725370446546451464121975)
        ·
          refine ⟨89588055669819677196182963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59725370446546451464121975 89588055669819677196182963)
          ·
            refine ⟨134382083504729515794274445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89588055669819677196182963 134382083504729515794274445)
            ·
              refine ⟨50393281314273568422852917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134382083504729515794274445 50393281314273568422852917)
              ·
                refine ⟨4724370123213147039642461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50393281314273568422852917 4724370123213147039642461)
                ·
                  refine ⟨1771638796204930139865923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4724370123213147039642461 1771638796204930139865923)
                  ·
                    refine ⟨2657458194307395209798885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1771638796204930139865923 2657458194307395209798885)
                    ·
                      refine ⟨498273411432636601837291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2657458194307395209798885 498273411432636601837291)
                      ·
                        rfl

theorem cell23_970384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_970384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970384 prefixEnd_970384 := by exact prefixLift 970384
  have htrace : WordTrace (prefixWord ++ tailWord_970384) baseStart_970384 baseEnd_970384 := by
    simpa [prefixWord, tailWord_970384, baseEnd_970384] using wordTrace_append hprefix tailTrace_970384
  have hstable : (prefixWord ++ tailWord_970384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970384).length < 2 ^ (prefixWord ++ tailWord_970384).sum := by decide
  have hdescent : baseEnd_970384 < baseStart_970384 := by decide
  rcases family_descends (prefixWord ++ tailWord_970384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970398 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_970398 : Nat := 118140960795 + 970398 * 2 ^ 59
def prefixEnd_970398 : Nat := 4983230072969 + 3 ^ 40 * 970398 * 2
def baseEnd_970398 : Nat := 166093533387266515687409

theorem tailTrace_970398 : CollatzResearch.WordTrace tailWord_970398 prefixEnd_970398 166093533387266515687409 := by
  unfold tailWord_970398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424165342302656453625981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23595548492280834419338565 4424165342302656453625981)
  ·
    refine ⟨1659062003363496170109743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4424165342302656453625981 1659062003363496170109743)
    ·
      refine ⟨2488593005045244255164615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659062003363496170109743 2488593005045244255164615)
      ·
        refine ⟨3732889507567866382746923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488593005045244255164615 3732889507567866382746923)
        ·
          refine ⟨5599334261351799574120385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732889507567866382746923 5599334261351799574120385)
          ·
            refine ⟨4199500696013849680590289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5599334261351799574120385 4199500696013849680590289)
            ·
              refine ⟨3149625522010387260442717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4199500696013849680590289 3149625522010387260442717)
              ·
                refine ⟨1181109570753895222666019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3149625522010387260442717 1181109570753895222666019)
                ·
                  refine ⟨1771664356130842833999029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181109570753895222666019 1771664356130842833999029)
                  ·
                    refine ⟨166093533387266515687409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1771664356130842833999029 166093533387266515687409)
                    ·
                      rfl

theorem cell23_970398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_970398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970398 prefixEnd_970398 := by exact prefixLift 970398
  have htrace : WordTrace (prefixWord ++ tailWord_970398) baseStart_970398 baseEnd_970398 := by
    simpa [prefixWord, tailWord_970398, baseEnd_970398] using wordTrace_append hprefix tailTrace_970398
  have hstable : (prefixWord ++ tailWord_970398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970398).length < 2 ^ (prefixWord ++ tailWord_970398).sum := by decide
  have hdescent : baseEnd_970398 < baseStart_970398 := by decide
  rcases family_descends (prefixWord ++ tailWord_970398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970428 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_970428 : Nat := 118140960795 + 970428 * 2 ^ 59
def prefixEnd_970428 : Nat := 4983230072969 + 3 ^ 40 * 970428 * 2
def baseEnd_970428 : Nat := 166098668193811476562363

theorem tailTrace_970428 : CollatzResearch.WordTrace tailWord_970428 prefixEnd_970428 166098668193811476562363 := by
  unfold tailWord_970428
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697208464156283376299969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23596277952208377835066625 17697208464156283376299969)
  ·
    refine ⟨13272906348117212532224977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17697208464156283376299969 13272906348117212532224977)
    ·
      refine ⟨9954679761087909399168733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13272906348117212532224977 9954679761087909399168733)
      ·
        refine ⟨3733004910407966024688275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9954679761087909399168733 3733004910407966024688275)
        ·
          refine ⟨5599507365611949037032413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733004910407966024688275 5599507365611949037032413)
          ·
            refine ⟨2099815262104480888887155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5599507365611949037032413 2099815262104480888887155)
            ·
              refine ⟨3149722893156721333330733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099815262104480888887155 3149722893156721333330733)
              ·
                refine ⟨1181146084933770499999025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3149722893156721333330733 1181146084933770499999025)
                ·
                  refine ⟨885859563700327874999269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1181146084933770499999025 885859563700327874999269)
                  ·
                    refine ⟨166098668193811476562363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885859563700327874999269 166098668193811476562363)
                    ·
                      rfl

theorem cell23_970428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_970428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970428 prefixEnd_970428 := by exact prefixLift 970428
  have htrace : WordTrace (prefixWord ++ tailWord_970428) baseStart_970428 baseEnd_970428 := by
    simpa [prefixWord, tailWord_970428, baseEnd_970428] using wordTrace_append hprefix tailTrace_970428
  have hstable : (prefixWord ++ tailWord_970428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970428).length < 2 ^ (prefixWord ++ tailWord_970428).sum := by decide
  have hdescent : baseEnd_970428 < baseStart_970428 := by decide
  rcases family_descends (prefixWord ++ tailWord_970428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970464 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_970464 : Nat := 118140960795 + 970464 * 2 ^ 59
def prefixEnd_970464 : Nat := 4983230072969 + 3 ^ 40 * 970464 * 2
def baseEnd_970464 : Nat := 498314489884996288836923

theorem tailTrace_970464 : CollatzResearch.WordTrace tailWord_970464 prefixEnd_970464 498314489884996288836923 := by
  unfold tailWord_970464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697864978091072450455223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23597153304121429933940297 17697864978091072450455223)
  ·
    refine ⟨26546797467136608675682835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17697864978091072450455223 26546797467136608675682835)
    ·
      refine ⟨39820196200704913013524253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26546797467136608675682835 39820196200704913013524253)
      ·
        refine ⟨14932573575264342380071595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39820196200704913013524253 14932573575264342380071595)
        ·
          refine ⟨22398860362896513570107393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14932573575264342380071595 22398860362896513570107393)
          ·
            refine ⟨16799145272172385177580545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22398860362896513570107393 16799145272172385177580545)
            ·
              refine ⟨12599358954129288883185409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16799145272172385177580545 12599358954129288883185409)
              ·
                refine ⟨9449519215596966662389057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12599358954129288883185409 9449519215596966662389057)
                ·
                  refine ⟨7087139411697724996791793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9449519215596966662389057 7087139411697724996791793)
                  ·
                    refine ⟨5315354558773293747593845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7087139411697724996791793 5315354558773293747593845)
                    ·
                      refine ⟨498314489884996288836923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5315354558773293747593845 498314489884996288836923)
                      ·
                        rfl

theorem cell23_970464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_970464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970464 prefixEnd_970464 := by exact prefixLift 970464
  have htrace : WordTrace (prefixWord ++ tailWord_970464) baseStart_970464 baseEnd_970464 := by
    simpa [prefixWord, tailWord_970464, baseEnd_970464] using wordTrace_append hprefix tailTrace_970464
  have hstable : (prefixWord ++ tailWord_970464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970464).length < 2 ^ (prefixWord ++ tailWord_970464).sum := by decide
  have hdescent : baseEnd_970464 < baseStart_970464 := by decide
  rcases family_descends (prefixWord ++ tailWord_970464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970478 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_970478 : Nat := 118140960795 + 970478 * 2 ^ 59
def prefixEnd_970478 : Nat := 4983230072969 + 3 ^ 40 * 970478 * 2
def baseEnd_970478 : Nat := 498321678614159234061859

theorem tailTrace_970478 : CollatzResearch.WordTrace tailWord_970478 prefixEnd_970478 498321678614159234061859 := by
  unfold tailWord_970478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424530072266428161490011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23597493718754283527946725 4424530072266428161490011)
  ·
    refine ⟨6636795108399642242235017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424530072266428161490011 6636795108399642242235017)
    ·
      refine ⟨4977596331299731681676263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6636795108399642242235017 4977596331299731681676263)
      ·
        refine ⟨7466394496949597522514395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977596331299731681676263 7466394496949597522514395)
        ·
          refine ⟨11199591745424396283771593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466394496949597522514395 11199591745424396283771593)
          ·
            refine ⟨8399693809068297212828695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11199591745424396283771593 8399693809068297212828695)
            ·
              refine ⟨12599540713602445819243043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8399693809068297212828695 12599540713602445819243043)
              ·
                refine ⟨18899311070403668728864565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12599540713602445819243043 18899311070403668728864565)
                ·
                  refine ⟨1771810412850343943331053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18899311070403668728864565 1771810412850343943331053)
                  ·
                    refine ⟨664428904818878978749145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771810412850343943331053 664428904818878978749145)
                    ·
                      refine ⟨498321678614159234061859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664428904818878978749145 498321678614159234061859)
                      ·
                        rfl

theorem cell23_970478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_970478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970478 prefixEnd_970478 := by exact prefixLift 970478
  have htrace : WordTrace (prefixWord ++ tailWord_970478) baseStart_970478 baseEnd_970478 := by
    simpa [prefixWord, tailWord_970478, baseEnd_970478] using wordTrace_append hprefix tailTrace_970478
  have hstable : (prefixWord ++ tailWord_970478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970478).length < 2 ^ (prefixWord ++ tailWord_970478).sum := by decide
  have hdescent : baseEnd_970478 < baseStart_970478 := by decide
  rcases family_descends (prefixWord ++ tailWord_970478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970508 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 1, 4, 2]
def baseStart_970508 : Nat := 118140960795 + 970508 * 2 ^ 59
def prefixEnd_970508 : Nat := 4983230072969 + 3 ^ 40 * 970508 * 2
def baseEnd_970508 : Nat := 498337083033794116686721

theorem tailTrace_970508 : CollatzResearch.WordTrace tailWord_970508 prefixEnd_970508 498337083033794116686721 := by
  unfold tailWord_970508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17698667384011370207756089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23598223178681826943674785 17698667384011370207756089)
  ·
    refine ⟨13274000538008527655817067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17698667384011370207756089 13274000538008527655817067)
    ·
      refine ⟨19911000807012791483725601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13274000538008527655817067 19911000807012791483725601)
      ·
        refine ⟨14933250605259593612794201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19911000807012791483725601 14933250605259593612794201)
        ·
          refine ⟨11199937953944695209595651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14933250605259593612794201 11199937953944695209595651)
          ·
            refine ⟨16799906930917042814393477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199937953944695209595651 16799906930917042814393477)
            ·
              refine ⟨3149982549546945527698777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16799906930917042814393477 3149982549546945527698777)
              ·
                refine ⟨2362486912160209145774083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149982549546945527698777 2362486912160209145774083)
                ·
                  refine ⟨3543730368240313718661125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362486912160209145774083 3543730368240313718661125)
                  ·
                    refine ⟨664449444045058822248961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3543730368240313718661125 664449444045058822248961)
                    ·
                      refine ⟨498337083033794116686721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664449444045058822248961 498337083033794116686721)
                      ·
                        rfl

theorem cell23_970508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_970508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970508 prefixEnd_970508 := by exact prefixLift 970508
  have htrace : WordTrace (prefixWord ++ tailWord_970508) baseStart_970508 baseEnd_970508 := by
    simpa [prefixWord, tailWord_970508, baseEnd_970508] using wordTrace_append hprefix tailTrace_970508
  have hstable : (prefixWord ++ tailWord_970508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970508).length < 2 ^ (prefixWord ++ tailWord_970508).sum := by decide
  have hdescent : baseEnd_970508 < baseStart_970508 := by decide
  rcases family_descends (prefixWord ++ tailWord_970508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970548 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 7]
def baseStart_970548 : Nat := 118140960795 + 970548 * 2 ^ 59
def prefixEnd_970548 : Nat := 4983230072969 + 3 ^ 40 * 970548 * 2
def baseEnd_970548 : Nat := 55373069139997106687393

theorem tailTrace_970548 : CollatzResearch.WordTrace tailWord_970548 prefixEnd_970548 55373069139997106687393 := by
  unfold tailWord_970548
  simp only [CollatzResearch.WordTrace]
  refine ⟨17699396843938913623484149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23599195791918551497978865 17699396843938913623484149)
  ·
    refine ⟨1659318454119273152201639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17699396843938913623484149 1659318454119273152201639)
    ·
      refine ⟨2488977681178909728302459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659318454119273152201639 2488977681178909728302459)
      ·
        refine ⟨3733466521768364592453689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488977681178909728302459 3733466521768364592453689)
        ·
          refine ⟨2800099891326273444340267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3733466521768364592453689 2800099891326273444340267)
          ·
            refine ⟨4200149836989410166510401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800099891326273444340267 4200149836989410166510401)
            ·
              refine ⟨3150112377742057624882801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4200149836989410166510401 3150112377742057624882801)
              ·
                refine ⟨2362584283306543218662101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150112377742057624882801 2362584283306543218662101)
                ·
                  refine ⟨55373069139997106687393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2362584283306543218662101 55373069139997106687393)
                  ·
                    rfl

theorem cell23_970548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_970548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970548 prefixEnd_970548 := by exact prefixLift 970548
  have htrace : WordTrace (prefixWord ++ tailWord_970548) baseStart_970548 baseEnd_970548 := by
    simpa [prefixWord, tailWord_970548, baseEnd_970548] using wordTrace_append hprefix tailTrace_970548
  have hstable : (prefixWord ++ tailWord_970548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970548).length < 2 ^ (prefixWord ++ tailWord_970548).sum := by decide
  have hdescent : baseEnd_970548 < baseStart_970548 := by decide
  rcases family_descends (prefixWord ++ tailWord_970548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970578 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_970578 : Nat := 118140960795 + 970578 * 2 ^ 59
def prefixEnd_970578 : Nat := 4983230072969 + 3 ^ 40 * 970578 * 2
def baseEnd_970578 : Nat := 166124342226536280937133

theorem tailTrace_970578 : CollatzResearch.WordTrace tailWord_970578 prefixEnd_970578 166124342226536280937133 := by
  unfold tailWord_970578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8849971969442285592640097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23599925251846094913706925 8849971969442285592640097)
  ·
    refine ⟨6637478977081714194480073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8849971969442285592640097 6637478977081714194480073)
    ·
      refine ⟨4978109232811285645860055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6637478977081714194480073 4978109232811285645860055)
      ·
        refine ⟨7467163849216928468790083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978109232811285645860055 7467163849216928468790083)
        ·
          refine ⟨11200745773825392703185125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467163849216928468790083 11200745773825392703185125)
          ·
            refine ⟨2100139832592261131847211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11200745773825392703185125 2100139832592261131847211)
            ·
              refine ⟨3150209748888391697770817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100139832592261131847211 3150209748888391697770817)
              ·
                refine ⟨2362657311666293773328113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150209748888391697770817 2362657311666293773328113)
                ·
                  refine ⟨1771992983749720329996085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2362657311666293773328113 1771992983749720329996085)
                  ·
                    refine ⟨166124342226536280937133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1771992983749720329996085 166124342226536280937133)
                    ·
                      rfl

theorem cell23_970578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_970578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970578 prefixEnd_970578 := by exact prefixLift 970578
  have htrace : WordTrace (prefixWord ++ tailWord_970578) baseStart_970578 baseEnd_970578 := by
    simpa [prefixWord, tailWord_970578, baseEnd_970578] using wordTrace_append hprefix tailTrace_970578
  have hstable : (prefixWord ++ tailWord_970578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970578).length < 2 ^ (prefixWord ++ tailWord_970578).sum := by decide
  have hdescent : baseEnd_970578 < baseStart_970578 := by decide
  rcases family_descends (prefixWord ++ tailWord_970578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970601 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 3]
def baseStart_970601 : Nat := 118140960795 + 970601 * 2 ^ 59
def prefixEnd_970601 : Nat := 4983230072969 + 3 ^ 40 * 970601 * 2
def baseEnd_970601 : Nat := 498384836734662252823793

theorem tailTrace_970601 : CollatzResearch.WordTrace tailWord_970601 prefixEnd_970601 498384836734662252823793 := by
  unfold tailWord_970601
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400726756685817298647657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23600484504457211532431771 35400726756685817298647657)
  ·
    refine ⟨26550545067514362973985743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35400726756685817298647657 26550545067514362973985743)
    ·
      refine ⟨39825817601271544460978615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26550545067514362973985743 39825817601271544460978615)
      ·
        refine ⟨59738726401907316691467923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39825817601271544460978615 59738726401907316691467923)
        ·
          refine ⟨89608089602860975037201885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59738726401907316691467923 89608089602860975037201885)
          ·
            refine ⟨33603033601072865638950707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89608089602860975037201885 33603033601072865638950707)
            ·
              refine ⟨50404550401609298458426061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33603033601072865638950707 50404550401609298458426061)
              ·
                refine ⟨18901706400603486921909773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50404550401609298458426061 18901706400603486921909773)
                ·
                  refine ⟨7088139900226307595716165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18901706400603486921909773 7088139900226307595716165)
                  ·
                    refine ⟨1329026231292432674196781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7088139900226307595716165 1329026231292432674196781)
                    ·
                      refine ⟨498384836734662252823793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329026231292432674196781 498384836734662252823793)
                      ·
                        rfl

theorem cell23_970601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_970601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970601 prefixEnd_970601 := by exact prefixLift 970601
  have htrace : WordTrace (prefixWord ++ tailWord_970601) baseStart_970601 baseEnd_970601 := by
    simpa [prefixWord, tailWord_970601, baseEnd_970601] using wordTrace_append hprefix tailTrace_970601
  have hstable : (prefixWord ++ tailWord_970601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970601).length < 2 ^ (prefixWord ++ tailWord_970601).sum := by decide
  have hdescent : baseEnd_970601 < baseStart_970601 := by decide
  rcases family_descends (prefixWord ++ tailWord_970601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970618 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_970618 : Nat := 118140960795 + 970618 * 2 ^ 59
def prefixEnd_970618 : Nat := 4983230072969 + 3 ^ 40 * 970618 * 2
def baseEnd_970618 : Nat := 498393565905788686311215

theorem tailTrace_970618 : CollatzResearch.WordTrace tailWord_970618 prefixEnd_970618 498393565905788686311215 := by
  unfold tailWord_970618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850336699406057300504127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23600897865082819468011005 8850336699406057300504127)
  ·
    refine ⟨13275505049109085950756191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8850336699406057300504127 13275505049109085950756191)
    ·
      refine ⟨19913257573663628926134287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13275505049109085950756191 19913257573663628926134287)
      ·
        refine ⟨29869886360495443389201431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19913257573663628926134287 29869886360495443389201431)
        ·
          refine ⟨44804829540743165083802147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29869886360495443389201431 44804829540743165083802147)
          ·
            refine ⟨67207244311114747625703221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44804829540743165083802147 67207244311114747625703221)
            ·
              refine ⟨6300679154167007589909677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67207244311114747625703221 6300679154167007589909677)
              ·
                refine ⟨2362754682812627846216129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6300679154167007589909677 2362754682812627846216129)
                ·
                  refine ⟨1772066012109470884662097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2362754682812627846216129 1772066012109470884662097)
                  ·
                    refine ⟨1329049509082103163496573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1772066012109470884662097 1329049509082103163496573)
                    ·
                      refine ⟨498393565905788686311215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329049509082103163496573 498393565905788686311215)
                      ·
                        rfl

theorem cell23_970618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_970618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970618 prefixEnd_970618 := by exact prefixLift 970618
  have htrace : WordTrace (prefixWord ++ tailWord_970618) baseStart_970618 baseEnd_970618 := by
    simpa [prefixWord, tailWord_970618, baseEnd_970618] using wordTrace_append hprefix tailTrace_970618
  have hstable : (prefixWord ++ tailWord_970618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970618).length < 2 ^ (prefixWord ++ tailWord_970618).sum := by decide
  have hdescent : baseEnd_970618 < baseStart_970618 := by decide
  rcases family_descends (prefixWord ++ tailWord_970618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970676 : List Nat := [2, 5, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_970676 : Nat := 118140960795 + 970676 * 2 ^ 59
def prefixEnd_970676 : Nat := 4983230072969 + 3 ^ 40 * 970676 * 2
def baseEnd_970676 : Nat := 166141115927916486461983

theorem tailTrace_970676 : CollatzResearch.WordTrace tailWord_970676 prefixEnd_970676 166141115927916486461983 := by
  unfold tailWord_970676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17701731115707052553813941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23602308154276070071751921 17701731115707052553813941)
  ·
    refine ⟨1659537292097536176920057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17701731115707052553813941 1659537292097536176920057)
    ·
      refine ⟨1244652969073152132690043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1659537292097536176920057 1244652969073152132690043)
      ·
        refine ⟨1866979453609728199035065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244652969073152132690043 1866979453609728199035065)
        ·
          refine ⟨1400234590207296149276299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1866979453609728199035065 1400234590207296149276299)
          ·
            refine ⟨2100351885310944223914449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400234590207296149276299 2100351885310944223914449)
            ·
              refine ⟨1575263913983208167935837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100351885310944223914449 1575263913983208167935837)
              ·
                refine ⟨590723967743703062975939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575263913983208167935837 590723967743703062975939)
                ·
                  refine ⟨886085951615554594463909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590723967743703062975939 886085951615554594463909)
                  ·
                    refine ⟨166141115927916486461983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 886085951615554594463909 166141115927916486461983)
                    ·
                      rfl

theorem cell23_970676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_970676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970676 prefixEnd_970676 := by exact prefixLift 970676
  have htrace : WordTrace (prefixWord ++ tailWord_970676) baseStart_970676 baseEnd_970676 := by
    simpa [prefixWord, tailWord_970676, baseEnd_970676] using wordTrace_append hprefix tailTrace_970676
  have hstable : (prefixWord ++ tailWord_970676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970676).length < 2 ^ (prefixWord ++ tailWord_970676).sum := by decide
  have hdescent : baseEnd_970676 < baseStart_970676 := by decide
  rcases family_descends (prefixWord ++ tailWord_970676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970685 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_970685 : Nat := 118140960795 + 970685 * 2 ^ 59
def prefixEnd_970685 : Nat := 4983230072969 + 3 ^ 40 * 970685 * 2
def baseEnd_970685 : Nat := 166142656369879974724469

theorem tailTrace_970685 : CollatzResearch.WordTrace tailWord_970685 prefixEnd_970685 166142656369879974724469 := by
  unfold tailWord_970685
  simp only [CollatzResearch.WordTrace]
  refine ⟨35403790488381499644705509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23602526992254333096470339 35403790488381499644705509)
  ·
    refine ⟨6638210716571531183382283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35403790488381499644705509 6638210716571531183382283)
    ·
      refine ⟨9957316074857296775073425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6638210716571531183382283 9957316074857296775073425)
      ·
        refine ⟨7467987056142972581305069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9957316074857296775073425 7467987056142972581305069)
        ·
          refine ⟨2800495146053614717989401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7467987056142972581305069 2800495146053614717989401)
          ·
            refine ⟨2100371359540211038492051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800495146053614717989401 2100371359540211038492051)
            ·
              refine ⟨3150557039310316557738077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100371359540211038492051 3150557039310316557738077)
              ·
                refine ⟨1181458889741368709151779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3150557039310316557738077 1181458889741368709151779)
                ·
                  refine ⟨1772188334612053063727669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181458889741368709151779 1772188334612053063727669)
                  ·
                    refine ⟨166142656369879974724469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1772188334612053063727669 166142656369879974724469)
                    ·
                      rfl

theorem cell23_970685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_970685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970685 prefixEnd_970685 := by exact prefixLift 970685
  have htrace : WordTrace (prefixWord ++ tailWord_970685) baseStart_970685 baseEnd_970685 := by
    simpa [prefixWord, tailWord_970685, baseEnd_970685] using wordTrace_append hprefix tailTrace_970685
  have hstable : (prefixWord ++ tailWord_970685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970685).length < 2 ^ (prefixWord ++ tailWord_970685).sum := by decide
  have hdescent : baseEnd_970685 < baseStart_970685 := by decide
  rcases family_descends (prefixWord ++ tailWord_970685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970711 : List Nat := [1, 1, 3, 2, 1, 1, 4, 10]
def baseStart_970711 : Nat := 118140960795 + 970711 * 2 ^ 59
def prefixEnd_970711 : Nat := 4983230072969 + 3 ^ 40 * 970711 * 2
def baseEnd_970711 : Nat := 18460789615061363794381

theorem tailTrace_970711 : CollatzResearch.WordTrace tailWord_970711 prefixEnd_970711 18460789615061363794381 := by
  unfold tailWord_970711
  simp only [CollatzResearch.WordTrace]
  refine ⟨35404738786287306085151987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23603159190858204056767991 35404738786287306085151987)
  ·
    refine ⟨53107108179430959127727981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35404738786287306085151987 53107108179430959127727981)
    ·
      refine ⟨19915165567286609672897993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53107108179430959127727981 19915165567286609672897993)
      ·
        refine ⟨14936374175464957254673495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19915165567286609672897993 14936374175464957254673495)
        ·
          refine ⟨22404561263197435882010243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14936374175464957254673495 22404561263197435882010243)
          ·
            refine ⟨33606841894796153823015365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22404561263197435882010243 33606841894796153823015365)
            ·
              refine ⟨6301282855274278841815381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33606841894796153823015365 6301282855274278841815381)
              ·
                refine ⟨18460789615061363794381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6301282855274278841815381 18460789615061363794381)
                ·
                  rfl

theorem cell23_970711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 10].length) (baseStart_970711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970711 prefixEnd_970711 := by exact prefixLift 970711
  have htrace : WordTrace (prefixWord ++ tailWord_970711) baseStart_970711 baseEnd_970711 := by
    simpa [prefixWord, tailWord_970711, baseEnd_970711] using wordTrace_append hprefix tailTrace_970711
  have hstable : (prefixWord ++ tailWord_970711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970711).length < 2 ^ (prefixWord ++ tailWord_970711).sum := by decide
  have hdescent : baseEnd_970711 < baseStart_970711 := by decide
  rcases family_descends (prefixWord ++ tailWord_970711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970731 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6]
def baseStart_970731 : Nat := 118140960795 + 970731 * 2 ^ 59
def prefixEnd_970731 : Nat := 4983230072969 + 3 ^ 40 * 970731 * 2
def baseEnd_970731 : Nat := 498451589219746744198195

theorem tailTrace_970731 : CollatzResearch.WordTrace tailWord_970731 prefixEnd_970731 498451589219746744198195 := by
  unfold tailWord_970731
  simp only [CollatzResearch.WordTrace]
  refine ⟨35405468246214849500880047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23603645497476566333920031 35405468246214849500880047)
  ·
    refine ⟨53108202369322274251320071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35405468246214849500880047 53108202369322274251320071)
    ·
      refine ⟨79662303553983411376980107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53108202369322274251320071 79662303553983411376980107)
      ·
        refine ⟨119493455330975117065470161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79662303553983411376980107 119493455330975117065470161)
        ·
          refine ⟨89620091498231337799102621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119493455330975117065470161 89620091498231337799102621)
          ·
            refine ⟨33607534311836751674663483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89620091498231337799102621 33607534311836751674663483)
            ·
              refine ⟨50411301467755127511995225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33607534311836751674663483 50411301467755127511995225)
              ·
                refine ⟨37808476100816345633996419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50411301467755127511995225 37808476100816345633996419)
                ·
                  refine ⟨56712714151224518450994629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37808476100816345633996419 56712714151224518450994629)
                  ·
                    refine ⟨10633633903354597209561493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56712714151224518450994629 10633633903354597209561493)
                    ·
                      refine ⟨498451589219746744198195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10633633903354597209561493 498451589219746744198195)
                      ·
                        rfl

theorem cell23_970731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_970731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970731 prefixEnd_970731 := by exact prefixLift 970731
  have htrace : WordTrace (prefixWord ++ tailWord_970731) baseStart_970731 baseEnd_970731 := by
    simpa [prefixWord, tailWord_970731, baseEnd_970731] using wordTrace_append hprefix tailTrace_970731
  have hstable : (prefixWord ++ tailWord_970731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970731).length < 2 ^ (prefixWord ++ tailWord_970731).sum := by decide
  have hdescent : baseEnd_970731 < baseStart_970731 := by decide
  rcases family_descends (prefixWord ++ tailWord_970731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970733 : List Nat := [1, 5, 1, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_970733 : Nat := 118140960795 + 970733 * 2 ^ 59
def prefixEnd_970733 : Nat := 4983230072969 + 3 ^ 40 * 970733 * 2
def baseEnd_970733 : Nat := 498452616181055736373187

theorem tailTrace_970733 : CollatzResearch.WordTrace tailWord_970733 prefixEnd_970733 498452616181055736373187 := by
  unfold tailWord_970733
  simp only [CollatzResearch.WordTrace]
  refine ⟨35405541192207603842452853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23603694128138402561635235 35405541192207603842452853)
  ·
    refine ⟨3319269486769462860229955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35405541192207603842452853 3319269486769462860229955)
    ·
      refine ⟨4978904230154194290344933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319269486769462860229955 4978904230154194290344933)
      ·
        refine ⟨933544543153911429439675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4978904230154194290344933 933544543153911429439675)
        ·
          refine ⟨1400316814730867144159513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933544543153911429439675 1400316814730867144159513)
          ·
            refine ⟨1050237611048150358119635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400316814730867144159513 1050237611048150358119635)
            ·
              refine ⟨1575356416572225537179453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050237611048150358119635 1575356416572225537179453)
              ·
                refine ⟨590758656214584576442295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575356416572225537179453 590758656214584576442295)
                ·
                  refine ⟨886137984321876864663443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590758656214584576442295 886137984321876864663443)
                  ·
                    refine ⟨1329206976482815296995165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 886137984321876864663443 1329206976482815296995165)
                    ·
                      refine ⟨498452616181055736373187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329206976482815296995165 498452616181055736373187)
                      ·
                        rfl

theorem cell23_970733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_970733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970733 prefixEnd_970733 := by exact prefixLift 970733
  have htrace : WordTrace (prefixWord ++ tailWord_970733) baseStart_970733 baseEnd_970733 := by
    simpa [prefixWord, tailWord_970733, baseEnd_970733] using wordTrace_append hprefix tailTrace_970733
  have hstable : (prefixWord ++ tailWord_970733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970733).length < 2 ^ (prefixWord ++ tailWord_970733).sum := by decide
  have hdescent : baseEnd_970733 < baseStart_970733 := by decide
  rcases family_descends (prefixWord ++ tailWord_970733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970742 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_970742 : Nat := 118140960795 + 970742 * 2 ^ 59
def prefixEnd_970742 : Nat := 4983230072969 + 3 ^ 40 * 970742 * 2
def baseEnd_970742 : Nat := 498457237506946201160645

theorem tailTrace_970742 : CollatzResearch.WordTrace tailWord_970742 prefixEnd_970742 498457237506946201160645 := by
  unfold tailWord_970742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212866840573437398720655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23603912966116665586353653 2212866840573437398720655)
  ·
    refine ⟨3319300260860156098080983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212866840573437398720655 3319300260860156098080983)
    ·
      refine ⟨4978950391290234147121475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319300260860156098080983 4978950391290234147121475)
      ·
        refine ⟨7468425586935351220682213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978950391290234147121475 7468425586935351220682213)
        ·
          refine ⟨1400329797550378353877915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7468425586935351220682213 1400329797550378353877915)
          ·
            refine ⟨2100494696325567530816873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400329797550378353877915 2100494696325567530816873)
            ·
              refine ⟨1575371022244175648112655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100494696325567530816873 1575371022244175648112655)
              ·
                refine ⟨2363056533366263472168983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575371022244175648112655 2363056533366263472168983)
                ·
                  refine ⟨3544584800049395208253475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363056533366263472168983 3544584800049395208253475)
                  ·
                    refine ⟨5316877200074092812380213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3544584800049395208253475 5316877200074092812380213)
                    ·
                      refine ⟨498457237506946201160645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5316877200074092812380213 498457237506946201160645)
                      ·
                        rfl

theorem cell23_970742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_970742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970742 prefixEnd_970742 := by exact prefixLift 970742
  have htrace : WordTrace (prefixWord ++ tailWord_970742) baseStart_970742 baseEnd_970742 := by
    simpa [prefixWord, tailWord_970742, baseEnd_970742] using wordTrace_append hprefix tailTrace_970742
  have hstable : (prefixWord ++ tailWord_970742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970742).length < 2 ^ (prefixWord ++ tailWord_970742).sum := by decide
  have hdescent : baseEnd_970742 < baseStart_970742 := by decide
  rcases family_descends (prefixWord ++ tailWord_970742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970822 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_970822 : Nat := 118140960795 + 970822 * 2 ^ 59
def prefixEnd_970822 : Nat := 4983230072969 + 3 ^ 40 * 970822 * 2
def baseEnd_970822 : Nat := 166166105319768629386759

theorem tailTrace_970822 : CollatzResearch.WordTrace tailWord_970822 prefixEnd_970822 166166105319768629386759 := by
  unfold tailWord_970822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106524602777661626326335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23605858192590114694961813 1106524602777661626326335)
  ·
    refine ⟨1659786904166492439489503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1106524602777661626326335 1659786904166492439489503)
    ·
      refine ⟨2489680356249738659234255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659786904166492439489503 2489680356249738659234255)
      ·
        refine ⟨3734520534374607988851383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489680356249738659234255 3734520534374607988851383)
        ·
          refine ⟨5601780801561911983277075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734520534374607988851383 5601780801561911983277075)
          ·
            refine ⟨8402671202342867974915613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601780801561911983277075 8402671202342867974915613)
            ·
              refine ⟨3151001700878575490593355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8402671202342867974915613 3151001700878575490593355)
              ·
                refine ⟨4726502551317863235890033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151001700878575490593355 4726502551317863235890033)
                ·
                  refine ⟨3544876913488397426917525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4726502551317863235890033 3544876913488397426917525)
                  ·
                    refine ⟨166166105319768629386759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3544876913488397426917525 166166105319768629386759)
                    ·
                      rfl

theorem cell23_970822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_970822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970822 prefixEnd_970822 := by exact prefixLift 970822
  have htrace : WordTrace (prefixWord ++ tailWord_970822) baseStart_970822 baseEnd_970822 := by
    simpa [prefixWord, tailWord_970822, baseEnd_970822] using wordTrace_append hprefix tailTrace_970822
  have hstable : (prefixWord ++ tailWord_970822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970822).length < 2 ^ (prefixWord ++ tailWord_970822).sum := by decide
  have hdescent : baseEnd_970822 < baseStart_970822 := by decide
  rcases family_descends (prefixWord ++ tailWord_970822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970829 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_970829 : Nat := 118140960795 + 970829 * 2 ^ 59
def prefixEnd_970829 : Nat := 4983230072969 + 3 ^ 40 * 970829 * 2
def baseEnd_970829 : Nat := 498501910323887360772745

theorem tailTrace_970829 : CollatzResearch.WordTrace tailWord_970829 prefixEnd_970829 498501910323887360772745 := by
  unfold tailWord_970829
  simp only [CollatzResearch.WordTrace]
  refine ⟨35409042599859812237947541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23606028399906541491965027 35409042599859812237947541)
  ·
    refine ⟨1659798871868428698653791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35409042599859812237947541 1659798871868428698653791)
    ·
      refine ⟨2489698307802643047980687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659798871868428698653791 2489698307802643047980687)
      ·
        refine ⟨3734547461703964571971031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489698307802643047980687 3734547461703964571971031)
        ·
          refine ⟨5601821192555946857956547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734547461703964571971031 5601821192555946857956547)
          ·
            refine ⟨8402731788833920286934821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601821192555946857956547 8402731788833920286934821)
            ·
              refine ⟨1575512210406360053800279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8402731788833920286934821 1575512210406360053800279)
              ·
                refine ⟨2363268315609540080700419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575512210406360053800279 2363268315609540080700419)
                ·
                  refine ⟨3544902473414310121050629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363268315609540080700419 3544902473414310121050629)
                  ·
                    refine ⟨664669213765183147696993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544902473414310121050629 664669213765183147696993)
                    ·
                      refine ⟨498501910323887360772745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664669213765183147696993 498501910323887360772745)
                      ·
                        rfl

theorem cell23_970829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_970829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970829 prefixEnd_970829 := by exact prefixLift 970829
  have htrace : WordTrace (prefixWord ++ tailWord_970829) baseStart_970829 baseEnd_970829 := by
    simpa [prefixWord, tailWord_970829, baseEnd_970829] using wordTrace_append hprefix tailTrace_970829
  have hstable : (prefixWord ++ tailWord_970829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970829).length < 2 ^ (prefixWord ++ tailWord_970829).sum := by decide
  have hdescent : baseEnd_970829 < baseStart_970829 := by decide
  rcases family_descends (prefixWord ++ tailWord_970829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970850 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_970850 : Nat := 118140960795 + 970850 * 2 ^ 59
def prefixEnd_970850 : Nat := 4983230072969 + 3 ^ 40 * 970850 * 2
def baseEnd_970850 : Nat := 498512693417631778610149

theorem tailTrace_970850 : CollatzResearch.WordTrace tailWord_970850 prefixEnd_970850 498512693417631778610149 := by
  unfold tailWord_970850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852452133195933206115501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23606539021855821882974669 8852452133195933206115501)
  ·
    refine ⟨3319669549948474952293313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8852452133195933206115501 3319669549948474952293313)
    ·
      refine ⟨2489752162461356214219985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3319669549948474952293313 2489752162461356214219985)
      ·
        refine ⟨1867314121846017160664989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2489752162461356214219985 1867314121846017160664989)
        ·
          refine ⟨700242795692256435249371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1867314121846017160664989 700242795692256435249371)
          ·
            refine ⟨1050364193538384652874057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700242795692256435249371 1050364193538384652874057)
            ·
              refine ⟨787773145153788489655543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050364193538384652874057 787773145153788489655543)
              ·
                refine ⟨1181659717730682734483315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787773145153788489655543 1181659717730682734483315)
                ·
                  refine ⟨1772489576596024101724973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181659717730682734483315 1772489576596024101724973)
                  ·
                    refine ⟨664683591223509038146865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772489576596024101724973 664683591223509038146865)
                    ·
                      refine ⟨498512693417631778610149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664683591223509038146865 498512693417631778610149)
                      ·
                        rfl

theorem cell23_970850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_970850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970850 prefixEnd_970850 := by exact prefixLift 970850
  have htrace : WordTrace (prefixWord ++ tailWord_970850) baseStart_970850 baseEnd_970850 := by
    simpa [prefixWord, tailWord_970850, baseEnd_970850] using wordTrace_append hprefix tailTrace_970850
  have hstable : (prefixWord ++ tailWord_970850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970850).length < 2 ^ (prefixWord ++ tailWord_970850).sum := by decide
  have hdescent : baseEnd_970850 < baseStart_970850 := by decide
  rcases family_descends (prefixWord ++ tailWord_970850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970885 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_970885 : Nat := 118140960795 + 970885 * 2 ^ 59
def prefixEnd_970885 : Nat := 4983230072969 + 3 ^ 40 * 970885 * 2
def baseEnd_970885 : Nat := 498530665240539141672487

theorem tailTrace_970885 : CollatzResearch.WordTrace tailWord_970885 prefixEnd_970885 498530665240539141672487 := by
  unfold tailWord_970885
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411085087656933801986109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23607390058437955867990739 35411085087656933801986109)
  ·
    refine ⟨13279156907871350175744791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35411085087656933801986109 13279156907871350175744791)
    ·
      refine ⟨19918735361807025263617187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13279156907871350175744791 19918735361807025263617187)
      ·
        refine ⟨29878103042710537895425781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19918735361807025263617187 29878103042710537895425781)
        ·
          refine ⟨2801072160254112927696167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29878103042710537895425781 2801072160254112927696167)
          ·
            refine ⟨4201608240381169391544251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801072160254112927696167 4201608240381169391544251)
            ·
              refine ⟨6302412360571754087316377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201608240381169391544251 6302412360571754087316377)
              ·
                refine ⟨4726809270428815565487283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302412360571754087316377 4726809270428815565487283)
                ·
                  refine ⟨7090213905643223348230925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726809270428815565487283 7090213905643223348230925)
                  ·
                    refine ⟨2658830214616208755586597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7090213905643223348230925 2658830214616208755586597)
                    ·
                      refine ⟨498530665240539141672487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2658830214616208755586597 498530665240539141672487)
                      ·
                        rfl

theorem cell23_970885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_970885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970885 prefixEnd_970885 := by exact prefixLift 970885
  have htrace : WordTrace (prefixWord ++ tailWord_970885) baseStart_970885 baseEnd_970885 := by
    simpa [prefixWord, tailWord_970885, baseEnd_970885] using wordTrace_append hprefix tailTrace_970885
  have hstable : (prefixWord ++ tailWord_970885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970885).length < 2 ^ (prefixWord ++ tailWord_970885).sum := by decide
  have hdescent : baseEnd_970885 < baseStart_970885 := by decide
  rcases family_descends (prefixWord ++ tailWord_970885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970905 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 3]
def baseStart_970905 : Nat := 118140960795 + 970905 * 2 ^ 59
def prefixEnd_970905 : Nat := 4983230072969 + 3 ^ 40 * 970905 * 2
def baseEnd_970905 : Nat := 498540934853629063422395

theorem tailTrace_970905 : CollatzResearch.WordTrace tailWord_970905 prefixEnd_970905 498540934853629063422395 := by
  unfold tailWord_970905
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411814547584477217714169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23607876365056318145142779 35411814547584477217714169)
  ·
    refine ⟨26558860910688357913285627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35411814547584477217714169 26558860910688357913285627)
    ·
      refine ⟨39838291366032536869928441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26558860910688357913285627 39838291366032536869928441)
      ·
        refine ⟨29878718524524402652446331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39838291366032536869928441 29878718524524402652446331)
        ·
          refine ⟨44818077786786603978669497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29878718524524402652446331 44818077786786603978669497)
          ·
            refine ⟨33613558340089952984002123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44818077786786603978669497 33613558340089952984002123)
            ·
              refine ⟨50420337510134929476003185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33613558340089952984002123 50420337510134929476003185)
              ·
                refine ⟨37815253132601197107002389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50420337510134929476003185 37815253132601197107002389)
                ·
                  refine ⟨1772589990590681114390737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37815253132601197107002389 1772589990590681114390737)
                  ·
                    refine ⟨1329442492943010835793053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1772589990590681114390737 1329442492943010835793053)
                    ·
                      refine ⟨498540934853629063422395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329442492943010835793053 498540934853629063422395)
                      ·
                        rfl

theorem cell23_970905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_970905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970905 prefixEnd_970905 := by exact prefixLift 970905
  have htrace : WordTrace (prefixWord ++ tailWord_970905) baseStart_970905 baseEnd_970905 := by
    simpa [prefixWord, tailWord_970905, baseEnd_970905] using wordTrace_append hprefix tailTrace_970905
  have hstable : (prefixWord ++ tailWord_970905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970905).length < 2 ^ (prefixWord ++ tailWord_970905).sum := by decide
  have hdescent : baseEnd_970905 < baseStart_970905 := by decide
  rcases family_descends (prefixWord ++ tailWord_970905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970919 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_970919 : Nat := 118140960795 + 970919 * 2 ^ 59
def prefixEnd_970919 : Nat := 4983230072969 + 3 ^ 40 * 970919 * 2
def baseEnd_970919 : Nat := 498548123582792008647331

theorem tailTrace_970919 : CollatzResearch.WordTrace tailWord_970919 prefixEnd_970919 498548123582792008647331 := by
  unfold tailWord_970919
  simp only [CollatzResearch.WordTrace]
  refine ⟨35412325169533757608723811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23608216779689171739149207 35412325169533757608723811)
  ·
    refine ⟨53118487754300636413085717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35412325169533757608723811 53118487754300636413085717)
    ·
      refine ⟨2489929113482842331863393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53118487754300636413085717 2489929113482842331863393)
      ·
        refine ⟨1867446835112131748897545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2489929113482842331863393 1867446835112131748897545)
        ·
          refine ⟨1400585126334098811673159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867446835112131748897545 1400585126334098811673159)
          ·
            refine ⟨2100877689501148217509739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400585126334098811673159 2100877689501148217509739)
            ·
              refine ⟨3151316534251722326264609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100877689501148217509739 3151316534251722326264609)
              ·
                refine ⟨2363487400688791744698457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151316534251722326264609 2363487400688791744698457)
                ·
                  refine ⟨1772615550516593808523843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363487400688791744698457 1772615550516593808523843)
                  ·
                    refine ⟨2658923325774890712785765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1772615550516593808523843 2658923325774890712785765)
                    ·
                      refine ⟨498548123582792008647331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2658923325774890712785765 498548123582792008647331)
                      ·
                        rfl

theorem cell23_970919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_970919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970919 prefixEnd_970919 := by exact prefixLift 970919
  have htrace : WordTrace (prefixWord ++ tailWord_970919) baseStart_970919 baseEnd_970919 := by
    simpa [prefixWord, tailWord_970919, baseEnd_970919] using wordTrace_append hprefix tailTrace_970919
  have hstable : (prefixWord ++ tailWord_970919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970919).length < 2 ^ (prefixWord ++ tailWord_970919).sum := by decide
  have hdescent : baseEnd_970919 < baseStart_970919 := by decide
  rcases family_descends (prefixWord ++ tailWord_970919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970952 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_970952 : Nat := 118140960795 + 970952 * 2 ^ 59
def prefixEnd_970952 : Nat := 4983230072969 + 3 ^ 40 * 970952 * 2
def baseEnd_970952 : Nat := 498565068444390379534679

theorem tailTrace_970952 : CollatzResearch.WordTrace tailWord_970952 prefixEnd_970952 498565068444390379534679 := by
  unfold tailWord_970952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17706764389207102122337555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23609019185609469496450073 17706764389207102122337555)
  ·
    refine ⟨26560146583810653183506333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17706764389207102122337555 26560146583810653183506333)
    ·
      refine ⟨9960054968928994943814875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26560146583810653183506333 9960054968928994943814875)
      ·
        refine ⟨14940082453393492415722313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960054968928994943814875 14940082453393492415722313)
        ·
          refine ⟨11205061840045119311791735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14940082453393492415722313 11205061840045119311791735)
          ·
            refine ⟨16807592760067678967687603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205061840045119311791735 16807592760067678967687603)
            ·
              refine ⟨25211389140101518451531405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16807592760067678967687603 25211389140101518451531405)
              ·
                refine ⟨9454270927538069419324277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25211389140101518451531405 9454270927538069419324277)
                ·
                  refine ⟨886337899456694008061651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9454270927538069419324277 886337899456694008061651)
                  ·
                    refine ⟨1329506849185041012092477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 886337899456694008061651 1329506849185041012092477)
                    ·
                      refine ⟨498565068444390379534679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329506849185041012092477 498565068444390379534679)
                      ·
                        rfl

theorem cell23_970952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_970952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970952 prefixEnd_970952 := by exact prefixLift 970952
  have htrace : WordTrace (prefixWord ++ tailWord_970952) baseStart_970952 baseEnd_970952 := by
    simpa [prefixWord, tailWord_970952, baseEnd_970952] using wordTrace_append hprefix tailTrace_970952
  have hstable : (prefixWord ++ tailWord_970952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970952).length < 2 ^ (prefixWord ++ tailWord_970952).sum := by decide
  have hdescent : baseEnd_970952 < baseStart_970952 := by decide
  rcases family_descends (prefixWord ++ tailWord_970952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970955 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 3, 5]
def baseStart_970955 : Nat := 118140960795 + 970955 * 2 ^ 59
def prefixEnd_970955 : Nat := 4983230072969 + 3 ^ 40 * 970955 * 2
def baseEnd_970955 : Nat := 166188869628784622599055

theorem tailTrace_970955 : CollatzResearch.WordTrace tailWord_970955 prefixEnd_970955 166188869628784622599055 := by
  unfold tailWord_970955
  simp only [CollatzResearch.WordTrace]
  refine ⟨35413638197403335757034319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23609092131602223838022879 35413638197403335757034319)
  ·
    refine ⟨53120457296105003635551479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35413638197403335757034319 53120457296105003635551479)
    ·
      refine ⟨79680685944157505453327219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53120457296105003635551479 79680685944157505453327219)
      ·
        refine ⟨119521028916236258179990829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79680685944157505453327219 119521028916236258179990829)
        ·
          refine ⟨44820385843588596817496561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119521028916236258179990829 44820385843588596817496561)
          ·
            refine ⟨33615289382691447613122421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44820385843588596817496561 33615289382691447613122421)
            ·
              refine ⟨3151433379627323213730227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33615289382691447613122421 3151433379627323213730227)
              ·
                refine ⟨4727150069440984820595341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151433379627323213730227 4727150069440984820595341)
                ·
                  refine ⟨1772681276040369307723253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4727150069440984820595341 1772681276040369307723253)
                  ·
                    refine ⟨166188869628784622599055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1772681276040369307723253 166188869628784622599055)
                    ·
                      rfl

theorem cell23_970955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 5].length) (baseStart_970955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970955 prefixEnd_970955 := by exact prefixLift 970955
  have htrace : WordTrace (prefixWord ++ tailWord_970955) baseStart_970955 baseEnd_970955 := by
    simpa [prefixWord, tailWord_970955, baseEnd_970955] using wordTrace_append hprefix tailTrace_970955
  have hstable : (prefixWord ++ tailWord_970955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970955).length < 2 ^ (prefixWord ++ tailWord_970955).sum := by decide
  have hdescent : baseEnd_970955 < baseStart_970955 := by decide
  rcases family_descends (prefixWord ++ tailWord_970955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970956 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_970956 : Nat := 118140960795 + 970956 * 2 ^ 59
def prefixEnd_970956 : Nat := 4983230072969 + 3 ^ 40 * 970956 * 2
def baseEnd_970956 : Nat := 498567122367008363884661

theorem tailTrace_970956 : CollatzResearch.WordTrace tailWord_970956 prefixEnd_970956 498567122367008363884661 := by
  unfold tailWord_970956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17706837335199856463910361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23609116446933141951880481 17706837335199856463910361)
  ·
    refine ⟨13280128001399892347932771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17706837335199856463910361 13280128001399892347932771)
    ·
      refine ⟨19920192002099838521899157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13280128001399892347932771 19920192002099838521899157)
      ·
        refine ⟨933759000098429930714023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19920192002099838521899157 933759000098429930714023)
        ·
          refine ⟨1400638500147644896071035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933759000098429930714023 1400638500147644896071035)
          ·
            refine ⟨2100957750221467344106553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400638500147644896071035 2100957750221467344106553)
            ·
              refine ⟨1575718312666100508079915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100957750221467344106553 1575718312666100508079915)
              ·
                refine ⟨2363577468999150762119873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575718312666100508079915 2363577468999150762119873)
                ·
                  refine ⟨1772683101749363071589905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363577468999150762119873 1772683101749363071589905)
                  ·
                    refine ⟨1329512326312022303692429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1772683101749363071589905 1329512326312022303692429)
                    ·
                      refine ⟨498567122367008363884661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329512326312022303692429 498567122367008363884661)
                      ·
                        rfl

theorem cell23_970956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_970956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970956 prefixEnd_970956 := by exact prefixLift 970956
  have htrace : WordTrace (prefixWord ++ tailWord_970956) baseStart_970956 baseEnd_970956 := by
    simpa [prefixWord, tailWord_970956, baseEnd_970956] using wordTrace_append hprefix tailTrace_970956
  have hstable : (prefixWord ++ tailWord_970956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970956).length < 2 ^ (prefixWord ++ tailWord_970956).sum := by decide
  have hdescent : baseEnd_970956 < baseStart_970956 := by decide
  rcases family_descends (prefixWord ++ tailWord_970956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970986 : List Nat := [3, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_970986 : Nat := 118140960795 + 970986 * 2 ^ 59
def prefixEnd_970986 : Nat := 4983230072969 + 3 ^ 40 * 970986 * 2
def baseEnd_970986 : Nat := 498582526786643246509523

theorem tailTrace_970986 : CollatzResearch.WordTrace tailWord_970986 prefixEnd_970986 498582526786643246509523 := by
  unfold tailWord_970986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8853692215072757012853203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23609845906860685367608541 8853692215072757012853203)
  ·
    refine ⟨13280538322609135519279805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8853692215072757012853203 13280538322609135519279805)
    ·
      refine ⟨4980201870978425819729927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13280538322609135519279805 4980201870978425819729927)
      ·
        refine ⟨7470302806467638729594891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980201870978425819729927 7470302806467638729594891)
        ·
          refine ⟨11205454209701458094392337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470302806467638729594891 11205454209701458094392337)
          ·
            refine ⟨8404090657276093570794253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11205454209701458094392337 8404090657276093570794253)
            ·
              refine ⟨3151533996478535089047845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8404090657276093570794253 3151533996478535089047845)
              ·
                refine ⟨590912624339725329196471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3151533996478535089047845 590912624339725329196471)
                ·
                  refine ⟨886368936509587993794707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590912624339725329196471 886368936509587993794707)
                  ·
                    refine ⟨1329553404764381990692061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 886368936509587993794707 1329553404764381990692061)
                    ·
                      refine ⟨498582526786643246509523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329553404764381990692061 498582526786643246509523)
                      ·
                        rfl

theorem cell23_970986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_970986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970986 prefixEnd_970986 := by exact prefixLift 970986
  have htrace : WordTrace (prefixWord ++ tailWord_970986) baseStart_970986 baseEnd_970986 := by
    simpa [prefixWord, tailWord_970986, baseEnd_970986] using wordTrace_append hprefix tailTrace_970986
  have hstable : (prefixWord ++ tailWord_970986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970986).length < 2 ^ (prefixWord ++ tailWord_970986).sum := by decide
  have hdescent : baseEnd_970986 < baseStart_970986 := by decide
  rcases family_descends (prefixWord ++ tailWord_970986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970995 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5]
def baseStart_970995 : Nat := 118140960795 + 970995 * 2 ^ 59
def prefixEnd_970995 : Nat := 4983230072969 + 3 ^ 40 * 970995 * 2
def baseEnd_970995 : Nat := 498587148112533711296981

theorem tailTrace_970995 : CollatzResearch.WordTrace tailWord_970995 prefixEnd_970995 498587148112533711296981 := by
  unfold tailWord_970995
  simp only [CollatzResearch.WordTrace]
  refine ⟨35415097117258422588490439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23610064744838948392326959 35415097117258422588490439)
  ·
    refine ⟨53122645675887633882735659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35415097117258422588490439 53122645675887633882735659)
    ·
      refine ⟨79683968513831450824103489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53122645675887633882735659 79683968513831450824103489)
      ·
        refine ⟨59762976385373588118077617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79683968513831450824103489 59762976385373588118077617)
        ·
          refine ⟨44822232289030191088558213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59762976385373588118077617 44822232289030191088558213)
          ·
            refine ⟨8404168554193160829104665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44822232289030191088558213 8404168554193160829104665)
            ·
              refine ⟨6303126415644870621828499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8404168554193160829104665 6303126415644870621828499)
              ·
                refine ⟨9454689623467305932742749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6303126415644870621828499 9454689623467305932742749)
                ·
                  refine ⟨3545508608800239724778531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9454689623467305932742749 3545508608800239724778531)
                  ·
                    refine ⟨5318262913200359587167797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3545508608800239724778531 5318262913200359587167797)
                    ·
                      refine ⟨498587148112533711296981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5318262913200359587167797 498587148112533711296981)
                      ·
                        rfl

theorem cell23_970995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_970995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970995 prefixEnd_970995 := by exact prefixLift 970995
  have htrace : WordTrace (prefixWord ++ tailWord_970995) baseStart_970995 baseEnd_970995 := by
    simpa [prefixWord, tailWord_970995, baseEnd_970995] using wordTrace_append hprefix tailTrace_970995
  have hstable : (prefixWord ++ tailWord_970995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970995).length < 2 ^ (prefixWord ++ tailWord_970995).sum := by decide
  have hdescent : baseEnd_970995 < baseStart_970995 := by decide
  rcases family_descends (prefixWord ++ tailWord_970995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971002 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_971002 : Nat := 118140960795 + 971002 * 2 ^ 59
def prefixEnd_971002 : Nat := 4983230072969 + 3 ^ 40 * 971002 * 2
def baseEnd_971002 : Nat := 166196914159038394636483

theorem tailTrace_971002 : CollatzResearch.WordTrace tailWord_971002 prefixEnd_971002 166196914159038394636483 := by
  unfold tailWord_971002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8853838107058265695998815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23610234952155375189330173 8853838107058265695998815)
  ·
    refine ⟨13280757160587398543998223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8853838107058265695998815 13280757160587398543998223)
    ·
      refine ⟨19921135740881097815997335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13280757160587398543998223 19921135740881097815997335)
      ·
        refine ⟨29881703611321646723996003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19921135740881097815997335 29881703611321646723996003)
        ·
          refine ⟨44822555416982470085994005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29881703611321646723996003 44822555416982470085994005)
          ·
            refine ⟨2101057285171053285280969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44822555416982470085994005 2101057285171053285280969)
            ·
              refine ⟨1575792963878289963960727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101057285171053285280969 1575792963878289963960727)
              ·
                refine ⟨2363689445817434945941091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575792963878289963960727 2363689445817434945941091)
                ·
                  refine ⟨3545534168726152418911637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363689445817434945941091 3545534168726152418911637)
                  ·
                    refine ⟨166196914159038394636483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3545534168726152418911637 166196914159038394636483)
                    ·
                      rfl

theorem cell23_971002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_971002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971002 prefixEnd_971002 := by exact prefixLift 971002
  have htrace : WordTrace (prefixWord ++ tailWord_971002) baseStart_971002 baseEnd_971002 := by
    simpa [prefixWord, tailWord_971002, baseEnd_971002] using wordTrace_append hprefix tailTrace_971002
  have hstable : (prefixWord ++ tailWord_971002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971002).length < 2 ^ (prefixWord ++ tailWord_971002).sum := by decide
  have hdescent : baseEnd_971002 < baseStart_971002 := by decide
  rcases family_descends (prefixWord ++ tailWord_971002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971005 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_971005 : Nat := 118140960795 + 971005 * 2 ^ 59
def prefixEnd_971005 : Nat := 4983230072969 + 3 ^ 40 * 971005 * 2
def baseEnd_971005 : Nat := 498592282919078672171935

theorem tailTrace_971005 : CollatzResearch.WordTrace tailWord_971005 prefixEnd_971005 498592282919078672171935 := by
  unfold tailWord_971005
  simp only [CollatzResearch.WordTrace]
  refine ⟨35415461847222194296354469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23610307898148129530902979 35415461847222194296354469)
  ·
    refine ⟨6640399096354161430566463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35415461847222194296354469 6640399096354161430566463)
    ·
      refine ⟨9960598644531242145849695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6640399096354161430566463 9960598644531242145849695)
      ·
        refine ⟨14940897966796863218774543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960598644531242145849695 14940897966796863218774543)
        ·
          refine ⟨22411346950195294828161815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14940897966796863218774543 22411346950195294828161815)
          ·
            refine ⟨33617020425292942242242723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22411346950195294828161815 33617020425292942242242723)
            ·
              refine ⟨50425530637939413363364085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33617020425292942242242723 50425530637939413363364085)
              ·
                refine ⟨4727393497306820002815383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50425530637939413363364085 4727393497306820002815383)
                ·
                  refine ⟨7091090245960230004223075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727393497306820002815383 7091090245960230004223075)
                  ·
                    refine ⟨10636635368940345006334613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7091090245960230004223075 10636635368940345006334613)
                    ·
                      refine ⟨498592282919078672171935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10636635368940345006334613 498592282919078672171935)
                      ·
                        rfl

theorem cell23_971005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_971005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971005 prefixEnd_971005 := by exact prefixLift 971005
  have htrace : WordTrace (prefixWord ++ tailWord_971005) baseStart_971005 baseEnd_971005 := by
    simpa [prefixWord, tailWord_971005, baseEnd_971005] using wordTrace_append hprefix tailTrace_971005
  have hstable : (prefixWord ++ tailWord_971005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971005).length < 2 ^ (prefixWord ++ tailWord_971005).sum := by decide
  have hdescent : baseEnd_971005 < baseStart_971005 := by decide
  rcases family_descends (prefixWord ++ tailWord_971005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971022 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_971022 : Nat := 118140960795 + 971022 * 2 ^ 59
def prefixEnd_971022 : Nat := 4983230072969 + 3 ^ 40 * 971022 * 2
def baseEnd_971022 : Nat := 498601012090205105659357

theorem tailTrace_971022 : CollatzResearch.WordTrace tailWord_971022 prefixEnd_971022 498601012090205105659357 := by
  unfold tailWord_971022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427010236020075774965415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23610721258773737466482213 4427010236020075774965415)
  ·
    refine ⟨6640515354030113662448123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4427010236020075774965415 6640515354030113662448123)
    ·
      refine ⟨9960773031045170493672185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6640515354030113662448123 9960773031045170493672185)
      ·
        refine ⟨7470579773283877870254139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9960773031045170493672185 7470579773283877870254139)
        ·
          refine ⟨11205869659925816805381209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470579773283877870254139 11205869659925816805381209)
          ·
            refine ⟨8404402244944362604035907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11205869659925816805381209 8404402244944362604035907)
            ·
              refine ⟨12606603367416543906053861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8404402244944362604035907 12606603367416543906053861)
              ·
                refine ⟨2363738131390601982385099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12606603367416543906053861 2363738131390601982385099)
                ·
                  refine ⟨3545607197085902973577649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363738131390601982385099 3545607197085902973577649)
                  ·
                    refine ⟨2659205397814427230183237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3545607197085902973577649 2659205397814427230183237)
                    ·
                      refine ⟨498601012090205105659357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2659205397814427230183237 498601012090205105659357)
                      ·
                        rfl

theorem cell23_971022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_971022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971022 prefixEnd_971022 := by exact prefixLift 971022
  have htrace : WordTrace (prefixWord ++ tailWord_971022) baseStart_971022 baseEnd_971022 := by
    simpa [prefixWord, tailWord_971022, baseEnd_971022] using wordTrace_append hprefix tailTrace_971022
  have hstable : (prefixWord ++ tailWord_971022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971022).length < 2 ^ (prefixWord ++ tailWord_971022).sum := by decide
  have hdescent : baseEnd_971022 < baseStart_971022 := by decide
  rcases family_descends (prefixWord ++ tailWord_971022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971053 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_971053 : Nat := 118140960795 + 971053 * 2 ^ 59
def prefixEnd_971053 : Nat := 4983230072969 + 3 ^ 40 * 971053 * 2
def baseEnd_971053 : Nat := 166205643330164828123905

theorem tailTrace_971053 : CollatzResearch.WordTrace tailWord_971053 prefixEnd_971053 166205643330164828123905 := by
  unfold tailWord_971053
  simp only [CollatzResearch.WordTrace]
  refine ⟨35417212551048298494101813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23611475034032198996067875 35417212551048298494101813)
  ·
    refine ⟨3320363676660777983822045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35417212551048298494101813 3320363676660777983822045)
    ·
      refine ⟨1245136378747791743933267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3320363676660777983822045 1245136378747791743933267)
      ·
        refine ⟨1867704568121687615899901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245136378747791743933267 1867704568121687615899901)
        ·
          refine ⟨700389213045632855962463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1867704568121687615899901 700389213045632855962463)
          ·
            refine ⟨1050583819568449283943695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700389213045632855962463 1050583819568449283943695)
            ·
              refine ⟨1575875729352673925915543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050583819568449283943695 1575875729352673925915543)
              ·
                refine ⟨2363813594029010888873315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575875729352673925915543 2363813594029010888873315)
                ·
                  refine ⟨3545720391043516333309973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363813594029010888873315 3545720391043516333309973)
                  ·
                    refine ⟨166205643330164828123905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3545720391043516333309973 166205643330164828123905)
                    ·
                      rfl

theorem cell23_971053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_971053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971053 prefixEnd_971053 := by exact prefixLift 971053
  have htrace : WordTrace (prefixWord ++ tailWord_971053) baseStart_971053 baseEnd_971053 := by
    simpa [prefixWord, tailWord_971053, baseEnd_971053] using wordTrace_append hprefix tailTrace_971053
  have hstable : (prefixWord ++ tailWord_971053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971053).length < 2 ^ (prefixWord ++ tailWord_971053).sum := by decide
  have hdescent : baseEnd_971053 < baseStart_971053 := by decide
  rcases family_descends (prefixWord ++ tailWord_971053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971075 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 1, 8]
def baseStart_971075 : Nat := 118140960795 + 971075 * 2 ^ 59
def prefixEnd_971075 : Nat := 4983230072969 + 3 ^ 40 * 971075 * 2
def baseEnd_971075 : Nat := 166209408854964466098871

theorem tailTrace_971075 : CollatzResearch.WordTrace tailWord_971075 prefixEnd_971075 166209408854964466098871 := by
  unfold tailWord_971075
  simp only [CollatzResearch.WordTrace]
  refine ⟨35418014956968596251402679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23612009971312397500935119 35418014956968596251402679)
  ·
    refine ⟨53127022435452894377104019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35418014956968596251402679 53127022435452894377104019)
    ·
      refine ⟨79690533653179341565656029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53127022435452894377104019 79690533653179341565656029)
      ·
        refine ⟨29883950119942253087121011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79690533653179341565656029 29883950119942253087121011)
        ·
          refine ⟨44825925179913379630681517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29883950119942253087121011 44825925179913379630681517)
          ·
            refine ⟨16809721942467517361505569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44825925179913379630681517 16809721942467517361505569)
            ·
              refine ⟨12607291456850638021129177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16809721942467517361505569 12607291456850638021129177)
              ·
                refine ⟨9455468592637978515846883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12607291456850638021129177 9455468592637978515846883)
                ·
                  refine ⟨14183202888956967773770325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9455468592637978515846883 14183202888956967773770325)
                  ·
                    refine ⟨166209408854964466098871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14183202888956967773770325 166209408854964466098871)
                    ·
                      rfl

theorem cell23_971075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 8].length) (baseStart_971075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971075 prefixEnd_971075 := by exact prefixLift 971075
  have htrace : WordTrace (prefixWord ++ tailWord_971075) baseStart_971075 baseEnd_971075 := by
    simpa [prefixWord, tailWord_971075, baseEnd_971075] using wordTrace_append hprefix tailTrace_971075
  have hstable : (prefixWord ++ tailWord_971075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971075).length < 2 ^ (prefixWord ++ tailWord_971075).sum := by decide
  have hdescent : baseEnd_971075 < baseStart_971075 := by decide
  rcases family_descends (prefixWord ++ tailWord_971075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971115 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9]
def baseStart_971115 : Nat := 118140960795 + 971115 * 2 ^ 59
def prefixEnd_971115 : Nat := 4983230072969 + 3 ^ 40 * 971115 * 2
def baseEnd_971115 : Nat := 498648765791073241796429

theorem tailTrace_971115 : CollatzResearch.WordTrace tailWord_971115 prefixEnd_971115 498648765791073241796429 := by
  unfold tailWord_971115
  simp only [CollatzResearch.WordTrace]
  refine ⟨35419473876823683082858799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23612982584549122055239199 35419473876823683082858799)
  ·
    refine ⟨53129210815235524624288199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35419473876823683082858799 53129210815235524624288199)
    ·
      refine ⟨79693816222853286936432299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53129210815235524624288199 79693816222853286936432299)
      ·
        refine ⟨119540724334279930404648449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79693816222853286936432299 119540724334279930404648449)
        ·
          refine ⟨89655543250709947803486337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119540724334279930404648449 89655543250709947803486337)
          ·
            refine ⟨67241657438032460852614753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89655543250709947803486337 67241657438032460852614753)
            ·
              refine ⟨50431243078524345639461065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67241657438032460852614753 50431243078524345639461065)
              ·
                refine ⟨37823432308893259229595799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50431243078524345639461065 37823432308893259229595799)
                ·
                  refine ⟨56735148463339888844393699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37823432308893259229595799 56735148463339888844393699)
                  ·
                    refine ⟨85102722695009833266590549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56735148463339888844393699 85102722695009833266590549)
                    ·
                      refine ⟨498648765791073241796429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 85102722695009833266590549 498648765791073241796429)
                      ·
                        rfl

theorem cell23_971115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_971115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971115 prefixEnd_971115 := by exact prefixLift 971115
  have htrace : WordTrace (prefixWord ++ tailWord_971115) baseStart_971115 baseEnd_971115 := by
    simpa [prefixWord, tailWord_971115, baseEnd_971115] using wordTrace_append hprefix tailTrace_971115
  have hstable : (prefixWord ++ tailWord_971115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971115).length < 2 ^ (prefixWord ++ tailWord_971115).sum := by decide
  have hdescent : baseEnd_971115 < baseStart_971115 := by decide
  rcases family_descends (prefixWord ++ tailWord_971115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971132 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_971132 : Nat := 118140960795 + 971132 * 2 ^ 59
def prefixEnd_971132 : Nat := 4983230072969 + 3 ^ 40 * 971132 * 2
def baseEnd_971132 : Nat := 498657494962199675283851

theorem tailTrace_971132 : CollatzResearch.WordTrace tailWord_971132 prefixEnd_971132 498657494962199675283851 := by
  unfold tailWord_971132
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710046958881047493113825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23613395945174729990818433 17710046958881047493113825)
  ·
    refine ⟨13282535219160785619835369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17710046958881047493113825 13282535219160785619835369)
    ·
      refine ⟨9961901414370589214876527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13282535219160785619835369 9961901414370589214876527)
      ·
        refine ⟨14942852121555883822314791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9961901414370589214876527 14942852121555883822314791)
        ·
          refine ⟨22414278182333825733472187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14942852121555883822314791 22414278182333825733472187)
          ·
            refine ⟨33621417273500738600208281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22414278182333825733472187 33621417273500738600208281)
            ·
              refine ⟨25216062955125553950156211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33621417273500738600208281 25216062955125553950156211)
              ·
                refine ⟨37824094432688330925234317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25216062955125553950156211 37824094432688330925234317)
                ·
                  refine ⟨14184035412258124096962869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37824094432688330925234317 14184035412258124096962869)
                  ·
                    refine ⟨1329753319899199134090269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14184035412258124096962869 1329753319899199134090269)
                    ·
                      refine ⟨498657494962199675283851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329753319899199134090269 498657494962199675283851)
                      ·
                        rfl

theorem cell23_971132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_971132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971132 prefixEnd_971132 := by exact prefixLift 971132
  have htrace : WordTrace (prefixWord ++ tailWord_971132) baseStart_971132 baseEnd_971132 := by
    simpa [prefixWord, tailWord_971132, baseEnd_971132] using wordTrace_append hprefix tailTrace_971132
  have hstable : (prefixWord ++ tailWord_971132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971132).length < 2 ^ (prefixWord ++ tailWord_971132).sum := by decide
  have hdescent : baseEnd_971132 < baseStart_971132 := by decide
  rcases family_descends (prefixWord ++ tailWord_971132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971150 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_971150 : Nat := 118140960795 + 971150 * 2 ^ 59
def prefixEnd_971150 : Nat := 4983230072969 + 3 ^ 40 * 971150 * 2
def baseEnd_971150 : Nat := 498666737613980604858769

theorem tailTrace_971150 : CollatzResearch.WordTrace tailWord_971150 prefixEnd_971150 498666737613980604858769 := by
  unfold tailWord_971150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427593803962110507547863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23613833621131256040255269 4427593803962110507547863)
  ·
    refine ⟨6641390705943165761321795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4427593803962110507547863 6641390705943165761321795)
    ·
      refine ⟨9962086058914748641982693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6641390705943165761321795 9962086058914748641982693)
      ·
        refine ⟨1867891136046515370371755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9962086058914748641982693 1867891136046515370371755)
        ·
          refine ⟨2801836704069773055557633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867891136046515370371755 2801836704069773055557633)
          ·
            refine ⟨2101377528052329791668225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801836704069773055557633 2101377528052329791668225)
            ·
              refine ⟨1576033146039247343751169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101377528052329791668225 1576033146039247343751169)
              ·
                refine ⟨1182024859529435507813377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576033146039247343751169 1182024859529435507813377)
                ·
                  refine ⟨886518644647076630860033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1182024859529435507813377 886518644647076630860033)
                  ·
                    refine ⟨664888983485307473145025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 886518644647076630860033 664888983485307473145025)
                    ·
                      refine ⟨498666737613980604858769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664888983485307473145025 498666737613980604858769)
                      ·
                        rfl

theorem cell23_971150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_971150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971150 prefixEnd_971150 := by exact prefixLift 971150
  have htrace : WordTrace (prefixWord ++ tailWord_971150) baseStart_971150 baseEnd_971150 := by
    simpa [prefixWord, tailWord_971150, baseEnd_971150] using wordTrace_append hprefix tailTrace_971150
  have hstable : (prefixWord ++ tailWord_971150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971150).length < 2 ^ (prefixWord ++ tailWord_971150).sum := by decide
  have hdescent : baseEnd_971150 < baseStart_971150 := by decide
  rcases family_descends (prefixWord ++ tailWord_971150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971159 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 2, 5, 2]
def baseStart_971159 : Nat := 118140960795 + 971159 * 2 ^ 59
def prefixEnd_971159 : Nat := 4983230072969 + 3 ^ 40 * 971159 * 2
def baseEnd_971159 : Nat := 498671358939871069646227

theorem tailTrace_971159 : CollatzResearch.WordTrace tailWord_971159 prefixEnd_971159 498671358939871069646227 := by
  unfold tailWord_971159
  simp only [CollatzResearch.WordTrace]
  refine ⟨35421078688664278597460531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23614052459109519064973687 35421078688664278597460531)
  ·
    refine ⟨53131618032996417896190797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35421078688664278597460531 53131618032996417896190797)
    ·
      refine ⟨19924356762373656711071549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53131618032996417896190797 19924356762373656711071549)
      ·
        refine ⟨7471633785890121266651831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19924356762373656711071549 7471633785890121266651831)
        ·
          refine ⟨11207450678835181899977747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7471633785890121266651831 11207450678835181899977747)
          ·
            refine ⟨16811176018252772849966621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11207450678835181899977747 16811176018252772849966621)
            ·
              refine ⟨6304191006844789818737483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16811176018252772849966621 6304191006844789818737483)
              ·
                refine ⟨9456286510267184728106225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304191006844789818737483 9456286510267184728106225)
                ·
                  refine ⟨7092214882700388546079669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456286510267184728106225 7092214882700388546079669)
                  ·
                    refine ⟨664895145253161426194969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7092214882700388546079669 664895145253161426194969)
                    ·
                      refine ⟨498671358939871069646227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664895145253161426194969 498671358939871069646227)
                      ·
                        rfl

theorem cell23_971159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_971159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971159 prefixEnd_971159 := by exact prefixLift 971159
  have htrace : WordTrace (prefixWord ++ tailWord_971159) baseStart_971159 baseEnd_971159 := by
    simpa [prefixWord, tailWord_971159, baseEnd_971159] using wordTrace_append hprefix tailTrace_971159
  have hstable : (prefixWord ++ tailWord_971159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971159).length < 2 ^ (prefixWord ++ tailWord_971159).sum := by decide
  have hdescent : baseEnd_971159 < baseStart_971159 := by decide
  rcases family_descends (prefixWord ++ tailWord_971159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971166 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_971166 : Nat := 118140960795 + 971166 * 2 ^ 59
def prefixEnd_971166 : Nat := 4983230072969 + 3 ^ 40 * 971166 * 2
def baseEnd_971166 : Nat := 498674953304452542258695

theorem tailTrace_971166 : CollatzResearch.WordTrace tailWord_971166 prefixEnd_971166 498674953304452542258695 := by
  unfold tailWord_971166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427666749954864849120669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23614222666425945861976901 4427666749954864849120669)
  ·
    refine ⟨1660375031233074318420251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4427666749954864849120669 1660375031233074318420251)
    ·
      refine ⟨2490562546849611477630377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660375031233074318420251 2490562546849611477630377)
      ·
        refine ⟨1867921910137208608222783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2490562546849611477630377 1867921910137208608222783)
        ·
          refine ⟨2801882865205812912334175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867921910137208608222783 2801882865205812912334175)
          ·
            refine ⟨4202824297808719368501263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801882865205812912334175 4202824297808719368501263)
            ·
              refine ⟨6304236446713079052751895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202824297808719368501263 6304236446713079052751895)
              ·
                refine ⟨9456354670069618579127843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304236446713079052751895 9456354670069618579127843)
                ·
                  refine ⟨14184532005104427868691765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456354670069618579127843 14184532005104427868691765)
                  ·
                    refine ⟨1329799875478540112689853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14184532005104427868691765 1329799875478540112689853)
                    ·
                      refine ⟨498674953304452542258695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329799875478540112689853 498674953304452542258695)
                      ·
                        rfl

theorem cell23_971166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_971166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971166 prefixEnd_971166 := by exact prefixLift 971166
  have htrace : WordTrace (prefixWord ++ tailWord_971166) baseStart_971166 baseEnd_971166 := by
    simpa [prefixWord, tailWord_971166, baseEnd_971166] using wordTrace_append hprefix tailTrace_971166
  have hstable : (prefixWord ++ tailWord_971166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971166).length < 2 ^ (prefixWord ++ tailWord_971166).sum := by decide
  have hdescent : baseEnd_971166 < baseStart_971166 := by decide
  rcases family_descends (prefixWord ++ tailWord_971166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971201 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_971201 : Nat := 118140960795 + 971201 * 2 ^ 59
def prefixEnd_971201 : Nat := 4983230072969 + 3 ^ 40 * 971201 * 2
def baseEnd_971201 : Nat := 498692925127359905321035

theorem tailTrace_971201 : CollatzResearch.WordTrace tailWord_971201 prefixEnd_971201 498692925127359905321035 := by
  unfold tailWord_971201
  simp only [CollatzResearch.WordTrace]
  refine ⟨35422610554512119770489457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23615073703008079846992971 35422610554512119770489457)
  ·
    refine ⟨26566957915884089827867093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35422610554512119770489457 26566957915884089827867093)
    ·
      refine ⟨622663076153533355340635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26566957915884089827867093 622663076153533355340635)
      ·
        refine ⟨933994614230300033010953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622663076153533355340635 933994614230300033010953)
        ·
          refine ⟨700495960672725024758215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933994614230300033010953 700495960672725024758215)
          ·
            refine ⟨1050743941009087537137323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700495960672725024758215 1050743941009087537137323)
            ·
              refine ⟨1576115911513631305705985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050743941009087537137323 1576115911513631305705985)
              ·
                refine ⟨1182086933635223479279489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576115911513631305705985 1182086933635223479279489)
                ·
                  refine ⟨886565200226417609459617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1182086933635223479279489 886565200226417609459617)
                  ·
                    refine ⟨664923900169813207094713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 886565200226417609459617 664923900169813207094713)
                    ·
                      refine ⟨498692925127359905321035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664923900169813207094713 498692925127359905321035)
                      ·
                        rfl

theorem cell23_971201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_971201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971201 prefixEnd_971201 := by exact prefixLift 971201
  have htrace : WordTrace (prefixWord ++ tailWord_971201) baseStart_971201 baseEnd_971201 := by
    simpa [prefixWord, tailWord_971201, baseEnd_971201] using wordTrace_append hprefix tailTrace_971201
  have hstable : (prefixWord ++ tailWord_971201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971201).length < 2 ^ (prefixWord ++ tailWord_971201).sum := by decide
  have hdescent : baseEnd_971201 < baseStart_971201 := by decide
  rcases family_descends (prefixWord ++ tailWord_971201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971209 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 3]
def baseStart_971209 : Nat := 118140960795 + 971209 * 2 ^ 59
def prefixEnd_971209 : Nat := 4983230072969 + 3 ^ 40 * 971209 * 2
def baseEnd_971209 : Nat := 498697032972595874020997

theorem tailTrace_971209 : CollatzResearch.WordTrace tailWord_971209 prefixEnd_971209 498697032972595874020997 := by
  unfold tailWord_971209
  simp only [CollatzResearch.WordTrace]
  refine ⟨35422902338483137136780681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23615268225655424757853787 35422902338483137136780681)
  ·
    refine ⟨26567176753862352852585511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35422902338483137136780681 26567176753862352852585511)
    ·
      refine ⟨39850765130793529278878267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26567176753862352852585511 39850765130793529278878267)
      ·
        refine ⟨59776147696190293918317401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39850765130793529278878267 59776147696190293918317401)
        ·
          refine ⟨44832110772142720438738051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59776147696190293918317401 44832110772142720438738051)
          ·
            refine ⟨67248166158214080658107077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44832110772142720438738051 67248166158214080658107077)
            ·
              refine ⟨12609031154665140123395077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67248166158214080658107077 12609031154665140123395077)
              ·
                refine ⟨2364193341499713773136577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12609031154665140123395077 2364193341499713773136577)
                ·
                  refine ⟨1773145006124785329852433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2364193341499713773136577 1773145006124785329852433)
                  ·
                    refine ⟨1329858754593588997389325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773145006124785329852433 1329858754593588997389325)
                    ·
                      refine ⟨498697032972595874020997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329858754593588997389325 498697032972595874020997)
                      ·
                        rfl

theorem cell23_971209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_971209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971209 prefixEnd_971209 := by exact prefixLift 971209
  have htrace : WordTrace (prefixWord ++ tailWord_971209) baseStart_971209 baseEnd_971209 := by
    simpa [prefixWord, tailWord_971209, baseEnd_971209] using wordTrace_append hprefix tailTrace_971209
  have hstable : (prefixWord ++ tailWord_971209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971209).length < 2 ^ (prefixWord ++ tailWord_971209).sum := by decide
  have hdescent : baseEnd_971209 < baseStart_971209 := by decide
  rcases family_descends (prefixWord ++ tailWord_971209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971232 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_971232 : Nat := 118140960795 + 971232 * 2 ^ 59
def prefixEnd_971232 : Nat := 4983230072969 + 3 ^ 40 * 971232 * 2
def baseEnd_971232 : Nat := 498708843027649284033391

theorem tailTrace_971232 : CollatzResearch.WordTrace tailWord_971232 prefixEnd_971232 498708843027649284033391 := by
  unfold tailWord_971232
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711870608699906032433975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23615827478266541376578633 17711870608699906032433975)
  ·
    refine ⟨26567805913049859048650963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17711870608699906032433975 26567805913049859048650963)
    ·
      refine ⟨39851708869574788572976445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26567805913049859048650963 39851708869574788572976445)
      ·
        refine ⟨14944390826090545714866167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39851708869574788572976445 14944390826090545714866167)
        ·
          refine ⟨22416586239135818572299251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14944390826090545714866167 22416586239135818572299251)
          ·
            refine ⟨33624879358703727858448877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22416586239135818572299251 33624879358703727858448877)
            ·
              refine ⟨12609329759513897946918329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33624879358703727858448877 12609329759513897946918329)
              ·
                refine ⟨9456997319635423460188747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12609329759513897946918329 9456997319635423460188747)
                ·
                  refine ⟨14185495979453135190283121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456997319635423460188747 14185495979453135190283121)
                  ·
                    refine ⟨10639121984589851392712341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14185495979453135190283121 10639121984589851392712341)
                    ·
                      refine ⟨498708843027649284033391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10639121984589851392712341 498708843027649284033391)
                      ·
                        rfl

theorem cell23_971232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_971232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971232 prefixEnd_971232 := by exact prefixLift 971232
  have htrace : WordTrace (prefixWord ++ tailWord_971232) baseStart_971232 baseEnd_971232 := by
    simpa [prefixWord, tailWord_971232, baseEnd_971232] using wordTrace_append hprefix tailTrace_971232
  have hstable : (prefixWord ++ tailWord_971232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971232).length < 2 ^ (prefixWord ++ tailWord_971232).sum := by decide
  have hdescent : baseEnd_971232 < baseStart_971232 := by decide
  rcases family_descends (prefixWord ++ tailWord_971232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971239 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_971239 : Nat := 118140960795 + 971239 * 2 ^ 59
def prefixEnd_971239 : Nat := 4983230072969 + 3 ^ 40 * 971239 * 2
def baseEnd_971239 : Nat := 498712437392230756645859

theorem tailTrace_971239 : CollatzResearch.WordTrace tailWord_971239 prefixEnd_971239 498712437392230756645859 := by
  unfold tailWord_971239
  simp only [CollatzResearch.WordTrace]
  refine ⟨35423996528374452260372771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23615997685582968173581847 35423996528374452260372771)
  ·
    refine ⟨53135994792561678390559157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35423996528374452260372771 53135994792561678390559157)
    ·
      refine ⟨4981499511802657349114921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53135994792561678390559157 4981499511802657349114921)
      ·
        refine ⟨3736124633851993011836191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4981499511802657349114921 3736124633851993011836191)
        ·
          refine ⟨5604186950777989517754287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736124633851993011836191 5604186950777989517754287)
          ·
            refine ⟨8406280426166984276631431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604186950777989517754287 8406280426166984276631431)
            ·
              refine ⟨12609420639250476414947147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8406280426166984276631431 12609420639250476414947147)
              ·
                refine ⟨18914130958875714622420721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12609420639250476414947147 18914130958875714622420721)
                ·
                  refine ⟨14185598219156785966815541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18914130958875714622420721 14185598219156785966815541)
                  ·
                    refine ⟨1329899833045948684388957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14185598219156785966815541 1329899833045948684388957)
                    ·
                      refine ⟨498712437392230756645859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1329899833045948684388957 498712437392230756645859)
                      ·
                        rfl

theorem cell23_971239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_971239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971239 prefixEnd_971239 := by exact prefixLift 971239
  have htrace : WordTrace (prefixWord ++ tailWord_971239) baseStart_971239 baseEnd_971239 := by
    simpa [prefixWord, tailWord_971239, baseEnd_971239] using wordTrace_append hprefix tailTrace_971239
  have hstable : (prefixWord ++ tailWord_971239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971239).length < 2 ^ (prefixWord ++ tailWord_971239).sum := by decide
  have hdescent : baseEnd_971239 < baseStart_971239 := by decide
  rcases family_descends (prefixWord ++ tailWord_971239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971293 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_971293 : Nat := 118140960795 + 971293 * 2 ^ 59
def prefixEnd_971293 : Nat := 4983230072969 + 3 ^ 40 * 971293 * 2
def baseEnd_971293 : Nat := 166246721782524515123537

theorem tailTrace_971293 : CollatzResearch.WordTrace tailWord_971293 prefixEnd_971293 166246721782524515123537 := by
  unfold tailWord_971293
  simp only [CollatzResearch.WordTrace]
  refine ⟨35425966070178819482838533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23617310713452546321892355 35425966070178819482838533)
  ·
    refine ⟨6642368638158528653032225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35425966070178819482838533 6642368638158528653032225)
    ·
      refine ⟨4981776478618896489774169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6642368638158528653032225 4981776478618896489774169)
      ·
        refine ⟨3736332358964172367330627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4981776478618896489774169 3736332358964172367330627)
        ·
          refine ⟨5604498538446258550995941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736332358964172367330627 5604498538446258550995941)
          ·
            refine ⟨1050843475958673478311739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5604498538446258550995941 1050843475958673478311739)
            ·
              refine ⟨1576265213938010217467609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050843475958673478311739 1576265213938010217467609)
              ·
                refine ⟨1182198910453507663100707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576265213938010217467609 1182198910453507663100707)
                ·
                  refine ⟨1773298365680261494651061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182198910453507663100707 1773298365680261494651061)
                  ·
                    refine ⟨166246721782524515123537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1773298365680261494651061 166246721782524515123537)
                    ·
                      rfl

theorem cell23_971293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_971293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971293 prefixEnd_971293 := by exact prefixLift 971293
  have htrace : WordTrace (prefixWord ++ tailWord_971293) baseStart_971293 baseEnd_971293 := by
    simpa [prefixWord, tailWord_971293, baseEnd_971293] using wordTrace_append hprefix tailTrace_971293
  have hstable : (prefixWord ++ tailWord_971293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971293).length < 2 ^ (prefixWord ++ tailWord_971293).sum := by decide
  have hdescent : baseEnd_971293 < baseStart_971293 := by decide
  rcases family_descends (prefixWord ++ tailWord_971293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971306 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_971306 : Nat := 118140960795 + 971306 * 2 ^ 59
def prefixEnd_971306 : Nat := 4983230072969 + 3 ^ 40 * 971306 * 2
def baseEnd_971306 : Nat := 166248946865360664836017

theorem tailTrace_971306 : CollatzResearch.WordTrace tailWord_971306 prefixEnd_971306 166248946865360664836017 := by
  unfold tailWord_971306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856610054782930675765443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23617626812754481802041181 8856610054782930675765443)
  ·
    refine ⟨13284915082174396013648165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8856610054782930675765443 13284915082174396013648165)
    ·
      refine ⟨2490921577907699252559031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13284915082174396013648165 2490921577907699252559031)
      ·
        refine ⟨3736382366861548878838547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490921577907699252559031 3736382366861548878838547)
        ·
          refine ⟨5604573550292323318257821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736382366861548878838547 5604573550292323318257821)
          ·
            refine ⟨2101715081359621244346683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5604573550292323318257821 2101715081359621244346683)
            ·
              refine ⟨3152572622039431866520025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101715081359621244346683 3152572622039431866520025)
              ·
                refine ⟨2364429466529573899890019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3152572622039431866520025 2364429466529573899890019)
                ·
                  refine ⟨3546644199794360849835029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364429466529573899890019 3546644199794360849835029)
                  ·
                    refine ⟨166248946865360664836017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3546644199794360849835029 166248946865360664836017)
                    ·
                      rfl

theorem cell23_971306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_971306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971306 prefixEnd_971306 := by exact prefixLift 971306
  have htrace : WordTrace (prefixWord ++ tailWord_971306) baseStart_971306 baseEnd_971306 := by
    simpa [prefixWord, tailWord_971306, baseEnd_971306] using wordTrace_append hprefix tailTrace_971306
  have hstable : (prefixWord ++ tailWord_971306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971306).length < 2 ^ (prefixWord ++ tailWord_971306).sum := by decide
  have hdescent : baseEnd_971306 < baseStart_971306 := by decide
  rcases family_descends (prefixWord ++ tailWord_971306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971310 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_971310 : Nat := 118140960795 + 971310 * 2 ^ 59
def prefixEnd_971310 : Nat := 4983230072969 + 3 ^ 40 * 971310 * 2
def baseEnd_971310 : Nat := 166249631506233326286011

theorem tailTrace_971310 : CollatzResearch.WordTrace tailWord_971310 prefixEnd_971310 166249631506233326286011 := by
  unfold tailWord_971310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428323263889653923275923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23617724074078154257471589 4428323263889653923275923)
  ·
    refine ⟨6642484895834480884913885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4428323263889653923275923 6642484895834480884913885)
    ·
      refine ⟨2490931835937930331842707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6642484895834480884913885 2490931835937930331842707)
      ·
        refine ⟨3736397753906895497764061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490931835937930331842707 3736397753906895497764061)
        ·
          refine ⟨1401149157715085811661523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3736397753906895497764061 1401149157715085811661523)
          ·
            refine ⟨2101723736572628717492285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401149157715085811661523 2101723736572628717492285)
            ·
              refine ⟨788146401214735769059607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101723736572628717492285 788146401214735769059607)
              ·
                refine ⟨1182219601822103653589411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788146401214735769059607 1182219601822103653589411)
                ·
                  refine ⟨1773329402733155480384117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182219601822103653589411 1773329402733155480384117)
                  ·
                    refine ⟨166249631506233326286011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1773329402733155480384117 166249631506233326286011)
                    ·
                      rfl

theorem cell23_971310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_971310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971310 prefixEnd_971310 := by exact prefixLift 971310
  have htrace : WordTrace (prefixWord ++ tailWord_971310) baseStart_971310 baseEnd_971310 := by
    simpa [prefixWord, tailWord_971310, baseEnd_971310] using wordTrace_append hprefix tailTrace_971310
  have hstable : (prefixWord ++ tailWord_971310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971310).length < 2 ^ (prefixWord ++ tailWord_971310).sum := by decide
  have hdescent : baseEnd_971310 < baseStart_971310 := by decide
  rcases family_descends (prefixWord ++ tailWord_971310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971394 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_971394 : Nat := 118140960795 + 971394 * 2 ^ 59
def prefixEnd_971394 : Nat := 4983230072969 + 3 ^ 40 * 971394 * 2
def baseEnd_971394 : Nat := 498792026893677650207647

theorem tailTrace_971394 : CollatzResearch.WordTrace tailWord_971394 prefixEnd_971394 498792026893677650207647 := by
  unfold tailWord_971394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8857412460703228433066309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23619766561875275821510157 8857412460703228433066309)
  ·
    refine ⟨1660764836381855331199933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8857412460703228433066309 1660764836381855331199933)
    ·
      refine ⟨622786813643195749199975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1660764836381855331199933 622786813643195749199975)
      ·
        refine ⟨934180220464793623799963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622786813643195749199975 934180220464793623799963)
        ·
          refine ⟨1401270330697190435699945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934180220464793623799963 1401270330697190435699945)
          ·
            refine ⟨1050952748022892826774959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401270330697190435699945 1050952748022892826774959)
            ·
              refine ⟨1576429122034339240162439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050952748022892826774959 1576429122034339240162439)
              ·
                refine ⟨2364643683051508860243659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576429122034339240162439 2364643683051508860243659)
                ·
                  refine ⟨3546965524577263290365489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364643683051508860243659 3546965524577263290365489)
                  ·
                    refine ⟨2660224143432947467774117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3546965524577263290365489 2660224143432947467774117)
                    ·
                      refine ⟨498792026893677650207647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2660224143432947467774117 498792026893677650207647)
                      ·
                        rfl

theorem cell23_971394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_971394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971394 prefixEnd_971394 := by exact prefixLift 971394
  have htrace : WordTrace (prefixWord ++ tailWord_971394) baseStart_971394 baseEnd_971394 := by
    simpa [prefixWord, tailWord_971394, baseEnd_971394] using wordTrace_append hprefix tailTrace_971394
  have hstable : (prefixWord ++ tailWord_971394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971394).length < 2 ^ (prefixWord ++ tailWord_971394).sum := by decide
  have hdescent : baseEnd_971394 < baseStart_971394 := by decide
  rcases family_descends (prefixWord ++ tailWord_971394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971396 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_971396 : Nat := 118140960795 + 971396 * 2 ^ 59
def prefixEnd_971396 : Nat := 4983230072969 + 3 ^ 40 * 971396 * 2
def baseEnd_971396 : Nat := 166264351284995547460879

theorem tailTrace_971396 : CollatzResearch.WordTrace tailWord_971396 prefixEnd_971396 166264351284995547460879 := by
  unfold tailWord_971396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17714861394402834036919021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23619815192537112049225361 17714861394402834036919021)
  ·
    refine ⟨6643073022901062763844633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17714861394402834036919021 6643073022901062763844633)
    ·
      refine ⟨4982304767175797072883475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6643073022901062763844633 4982304767175797072883475)
      ·
        refine ⟨7473457150763695609325213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982304767175797072883475 7473457150763695609325213)
        ·
          refine ⟨2802546431536385853496955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7473457150763695609325213 2802546431536385853496955)
          ·
            refine ⟨4203819647304578780245433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802546431536385853496955 4203819647304578780245433)
            ·
              refine ⟨3152864735478434085184075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4203819647304578780245433 3152864735478434085184075)
              ·
                refine ⟨4729297103217651127776113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152864735478434085184075 4729297103217651127776113)
                ·
                  refine ⟨3546972827413238345832085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4729297103217651127776113 3546972827413238345832085)
                  ·
                    refine ⟨166264351284995547460879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3546972827413238345832085 166264351284995547460879)
                    ·
                      rfl

theorem cell23_971396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_971396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971396 prefixEnd_971396 := by exact prefixLift 971396
  have htrace : WordTrace (prefixWord ++ tailWord_971396) baseStart_971396 baseEnd_971396 := by
    simpa [prefixWord, tailWord_971396, baseEnd_971396] using wordTrace_append hprefix tailTrace_971396
  have hstable : (prefixWord ++ tailWord_971396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971396).length < 2 ^ (prefixWord ++ tailWord_971396).sum := by decide
  have hdescent : baseEnd_971396 < baseStart_971396 := by decide
  rcases family_descends (prefixWord ++ tailWord_971396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971406 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_971406 : Nat := 118140960795 + 971406 * 2 ^ 59
def prefixEnd_971406 : Nat := 4983230072969 + 3 ^ 40 * 971406 * 2
def baseEnd_971406 : Nat := 498798188661531603257591

theorem tailTrace_971406 : CollatzResearch.WordTrace tailWord_971406 prefixEnd_971406 498798188661531603257591 := by
  unfold tailWord_971406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428760939846179972712759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23620058345846293187801381 4428760939846179972712759)
  ·
    refine ⟨6643141409769269959069139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4428760939846179972712759 6643141409769269959069139)
    ·
      refine ⟨9964712114653904938603709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6643141409769269959069139 9964712114653904938603709)
      ·
        refine ⟨3736767042995214351976391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9964712114653904938603709 3736767042995214351976391)
        ·
          refine ⟨5605150564492821527964587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736767042995214351976391 5605150564492821527964587)
          ·
            refine ⟨8407725846739232291946881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5605150564492821527964587 8407725846739232291946881)
            ·
              refine ⟨6305794385054424218960161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8407725846739232291946881 6305794385054424218960161)
              ·
                refine ⟨4729345788790818164220121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6305794385054424218960161 4729345788790818164220121)
                ·
                  refine ⟨3547009341593113623165091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4729345788790818164220121 3547009341593113623165091)
                  ·
                    refine ⟨5320514012389670434747637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3547009341593113623165091 5320514012389670434747637)
                    ·
                      refine ⟨498798188661531603257591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5320514012389670434747637 498798188661531603257591)
                      ·
                        rfl

theorem cell23_971406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_971406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971406 prefixEnd_971406 := by exact prefixLift 971406
  have htrace : WordTrace (prefixWord ++ tailWord_971406) baseStart_971406 baseEnd_971406 := by
    simpa [prefixWord, tailWord_971406, baseEnd_971406] using wordTrace_append hprefix tailTrace_971406
  have hstable : (prefixWord ++ tailWord_971406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971406).length < 2 ^ (prefixWord ++ tailWord_971406).sum := by decide
  have hdescent : baseEnd_971406 < baseStart_971406 := by decide
  rcases family_descends (prefixWord ++ tailWord_971406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971420 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_971420 : Nat := 118140960795 + 971420 * 2 ^ 59
def prefixEnd_971420 : Nat := 4983230072969 + 3 ^ 40 * 971420 * 2
def baseEnd_971420 : Nat := 498805377390694548482527

theorem tailTrace_971420 : CollatzResearch.WordTrace tailWord_971420 prefixEnd_971420 498805377390694548482527 := by
  unfold tailWord_971420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17715299070359360086355857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23620398760479146781807809 17715299070359360086355857)
  ·
    refine ⟨13286474302769520064766893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17715299070359360086355857 13286474302769520064766893)
    ·
      refine ⟨4982427863538570024287585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13286474302769520064766893 4982427863538570024287585)
      ·
        refine ⟨3736820897653927518215689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4982427863538570024287585 3736820897653927518215689)
        ·
          refine ⟨2802615673240445638661767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3736820897653927518215689 2802615673240445638661767)
          ·
            refine ⟨4203923509860668457992651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802615673240445638661767 4203923509860668457992651)
            ·
              refine ⟨6305885264791002686988977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203923509860668457992651 6305885264791002686988977)
              ·
                refine ⟨4729413948593252015241733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6305885264791002686988977 4729413948593252015241733)
                ·
                  refine ⟨886765115361234752857825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4729413948593252015241733 886765115361234752857825)
                  ·
                    refine ⟨665073836520926064643369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 886765115361234752857825 665073836520926064643369)
                    ·
                      refine ⟨498805377390694548482527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665073836520926064643369 498805377390694548482527)
                      ·
                        rfl

theorem cell23_971420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_971420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971420 prefixEnd_971420 := by exact prefixLift 971420
  have htrace : WordTrace (prefixWord ++ tailWord_971420) baseStart_971420 baseEnd_971420 := by
    simpa [prefixWord, tailWord_971420, baseEnd_971420] using wordTrace_append hprefix tailTrace_971420
  have hstable : (prefixWord ++ tailWord_971420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971420).length < 2 ^ (prefixWord ++ tailWord_971420).sum := by decide
  have hdescent : baseEnd_971420 < baseStart_971420 := by decide
  rcases family_descends (prefixWord ++ tailWord_971420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971493 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_971493 : Nat := 118140960795 + 971493 * 2 ^ 59
def prefixEnd_971493 : Nat := 4983230072969 + 3 ^ 40 * 971493 * 2
def baseEnd_971493 : Nat := 498842861478472762869691

theorem tailTrace_971493 : CollatzResearch.WordTrace tailWord_971493 prefixEnd_971493 498842861478472762869691 := by
  unfold tailWord_971493
  simp only [CollatzResearch.WordTrace]
  refine ⟨35433260669454253640119133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23622173779636169093412755 35433260669454253640119133)
  ·
    refine ⟨13287472751045345115044675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35433260669454253640119133 13287472751045345115044675)
    ·
      refine ⟨19931209126568017672567013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13287472751045345115044675 19931209126568017672567013)
      ·
        refine ⟨3737101711231503313606315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19931209126568017672567013 3737101711231503313606315)
        ·
          refine ⟨5605652566847254970409473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3737101711231503313606315 5605652566847254970409473)
          ·
            refine ⟨4204239425135441227807105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5605652566847254970409473 4204239425135441227807105)
            ·
              refine ⟨3153179568851580920855329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204239425135441227807105 3153179568851580920855329)
              ·
                refine ⟨2364884676638685690641497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153179568851580920855329 2364884676638685690641497)
                ·
                  refine ⟨1773663507479014267981123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2364884676638685690641497 1773663507479014267981123)
                  ·
                    refine ⟨2660495261218521401971685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1773663507479014267981123 2660495261218521401971685)
                    ·
                      refine ⟨498842861478472762869691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2660495261218521401971685 498842861478472762869691)
                      ·
                        rfl

theorem cell23_971493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_971493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971493 prefixEnd_971493 := by exact prefixLift 971493
  have htrace : WordTrace (prefixWord ++ tailWord_971493) baseStart_971493 baseEnd_971493 := by
    simpa [prefixWord, tailWord_971493, baseEnd_971493] using wordTrace_append hprefix tailTrace_971493
  have hstable : (prefixWord ++ tailWord_971493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971493).length < 2 ^ (prefixWord ++ tailWord_971493).sum := by decide
  have hdescent : baseEnd_971493 < baseStart_971493 := by decide
  rcases family_descends (prefixWord ++ tailWord_971493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971510 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_971510 : Nat := 118140960795 + 971510 * 2 ^ 59
def prefixEnd_971510 : Nat := 4983230072969 + 3 ^ 40 * 971510 * 2
def baseEnd_971510 : Nat := 498851590649599196357113

theorem tailTrace_971510 : CollatzResearch.WordTrace tailWord_971510 prefixEnd_971510 498851590649599196357113 := by
  unfold tailWord_971510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214617544399541596467999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23622587140261777028991989 2214617544399541596467999)
  ·
    refine ⟨3321926316599312394701999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2214617544399541596467999 3321926316599312394701999)
    ·
      refine ⟨4982889474898968592052999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321926316599312394701999 4982889474898968592052999)
      ·
        refine ⟨7474334212348452888079499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982889474898968592052999 7474334212348452888079499)
        ·
          refine ⟨11211501318522679332119249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7474334212348452888079499 11211501318522679332119249)
          ·
            refine ⟨8408625988892009499089437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11211501318522679332119249 8408625988892009499089437)
            ·
              refine ⟨3153234745834503562158539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8408625988892009499089437 3153234745834503562158539)
              ·
                refine ⟨4729852118751755343237809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3153234745834503562158539 4729852118751755343237809)
                ·
                  refine ⟨3547389089063816507428357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4729852118751755343237809 3547389089063816507428357)
                  ·
                    refine ⟨665135454199465595142817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3547389089063816507428357 665135454199465595142817)
                    ·
                      refine ⟨498851590649599196357113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665135454199465595142817 498851590649599196357113)
                      ·
                        rfl

theorem cell23_971510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_971510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971510 prefixEnd_971510 := by exact prefixLift 971510
  have htrace : WordTrace (prefixWord ++ tailWord_971510) baseStart_971510 baseEnd_971510 := by
    simpa [prefixWord, tailWord_971510, baseEnd_971510] using wordTrace_append hprefix tailTrace_971510
  have hstable : (prefixWord ++ tailWord_971510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971510).length < 2 ^ (prefixWord ++ tailWord_971510).sum := by decide
  have hdescent : baseEnd_971510 < baseStart_971510 := by decide
  rcases family_descends (prefixWord ++ tailWord_971510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971588 : List Nat := [2, 3, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_971588 : Nat := 118140960795 + 971588 * 2 ^ 59
def prefixEnd_971588 : Nat := 4983230072969 + 3 ^ 40 * 971588 * 2
def baseEnd_971588 : Nat := 166297214046883297060585

theorem tailTrace_971588 : CollatzResearch.WordTrace tailWord_971588 prefixEnd_971588 166297214046883297060585 := by
  unfold tailWord_971588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17718362802055042432413709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23624483736073389909884945 17718362802055042432413709)
  ·
    refine ⟨6644386050770640912155141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17718362802055042432413709 6644386050770640912155141)
    ·
      refine ⟨1245822384519495171029089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6644386050770640912155141 1245822384519495171029089)
      ·
        refine ⟨934366788389621378271817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1245822384519495171029089 934366788389621378271817)
        ·
          refine ⟨700775091292216033703863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934366788389621378271817 700775091292216033703863)
          ·
            refine ⟨1051162636938324050555795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700775091292216033703863 1051162636938324050555795)
            ·
              refine ⟨1576743955407486075833693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051162636938324050555795 1576743955407486075833693)
              ·
                refine ⟨591278983277807278437635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1576743955407486075833693 591278983277807278437635)
                ·
                  refine ⟨886918474916710917656453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591278983277807278437635 886918474916710917656453)
                  ·
                    refine ⟨166297214046883297060585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 886918474916710917656453 166297214046883297060585)
                    ·
                      rfl

theorem cell23_971588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_971588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971588 prefixEnd_971588 := by exact prefixLift 971588
  have htrace : WordTrace (prefixWord ++ tailWord_971588) baseStart_971588 baseEnd_971588 := by
    simpa [prefixWord, tailWord_971588, baseEnd_971588] using wordTrace_append hprefix tailTrace_971588
  have hstable : (prefixWord ++ tailWord_971588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971588).length < 2 ^ (prefixWord ++ tailWord_971588).sum := by decide
  have hdescent : baseEnd_971588 < baseStart_971588 := by decide
  rcases family_descends (prefixWord ++ tailWord_971588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971593 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 4, 4]
def baseStart_971593 : Nat := 118140960795 + 971593 * 2 ^ 59
def prefixEnd_971593 : Nat := 4983230072969 + 3 ^ 40 * 971593 * 2
def baseEnd_971593 : Nat := 166298069847974123873077

theorem tailTrace_971593 : CollatzResearch.WordTrace tailWord_971593 prefixEnd_971593 166298069847974123873077 := by
  unfold tailWord_971593
  simp only [CollatzResearch.WordTrace]
  refine ⟨35436907969091970718759433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23624605312727980479172955 35436907969091970718759433)
  ·
    refine ⟨26577680976818978039069575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35436907969091970718759433 26577680976818978039069575)
    ·
      refine ⟨39866521465228467058604363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26577680976818978039069575 39866521465228467058604363)
      ·
        refine ⟨59799782197842700587906545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39866521465228467058604363 59799782197842700587906545)
        ·
          refine ⟨44849836648382025440929909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59799782197842700587906545 44849836648382025440929909)
          ·
            refine ⟨4204672185785814885087179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44849836648382025440929909 4204672185785814885087179)
            ·
              refine ⟨6307008278678722327630769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204672185785814885087179 6307008278678722327630769)
              ·
                refine ⟨4730256209009041745723077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6307008278678722327630769 4730256209009041745723077)
                ·
                  refine ⟨886923039189195327323077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4730256209009041745723077 886923039189195327323077)
                  ·
                    refine ⟨166298069847974123873077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 886923039189195327323077 166298069847974123873077)
                    ·
                      rfl

theorem cell23_971593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_971593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971593 prefixEnd_971593 := by exact prefixLift 971593
  have htrace : WordTrace (prefixWord ++ tailWord_971593) baseStart_971593 baseEnd_971593 := by
    simpa [prefixWord, tailWord_971593, baseEnd_971593] using wordTrace_append hprefix tailTrace_971593
  have hstable : (prefixWord ++ tailWord_971593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971593).length < 2 ^ (prefixWord ++ tailWord_971593).sum := by decide
  have hdescent : baseEnd_971593 < baseStart_971593 := by decide
  rcases family_descends (prefixWord ++ tailWord_971593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971600 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 5, 2, 2]
def baseStart_971600 : Nat := 118140960795 + 971600 * 2 ^ 59
def prefixEnd_971600 : Nat := 4983230072969 + 3 ^ 40 * 971600 * 2
def baseEnd_971600 : Nat := 498897803908503844231699

theorem tailTrace_971600 : CollatzResearch.WordTrace tailWord_971600 prefixEnd_971600 498897803908503844231699 := by
  unfold tailWord_971600
  simp only [CollatzResearch.WordTrace]
  refine ⟨17718581640033305457132127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23624775520044407276176169 17718581640033305457132127)
  ·
    refine ⟨26577872460049958185698191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17718581640033305457132127 26577872460049958185698191)
    ·
      refine ⟨39866808690074937278547287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26577872460049958185698191 39866808690074937278547287)
      ·
        refine ⟨59800213035112405917820931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39866808690074937278547287 59800213035112405917820931)
        ·
          refine ⟨89700319552668608876731397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59800213035112405917820931 89700319552668608876731397)
          ·
            refine ⟨16818809916125364164387137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89700319552668608876731397 16818809916125364164387137)
            ·
              refine ⟨12614107437094023123290353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16818809916125364164387137 12614107437094023123290353)
              ·
                refine ⟨9460580577820517342467765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12614107437094023123290353 9460580577820517342467765)
                ·
                  refine ⟨886929429170673500856353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9460580577820517342467765 886929429170673500856353)
                  ·
                    refine ⟨665197071878005125642265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 886929429170673500856353 665197071878005125642265)
                    ·
                      refine ⟨498897803908503844231699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665197071878005125642265 498897803908503844231699)
                      ·
                        rfl

theorem cell23_971600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 2, 2].length) (baseStart_971600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971600 prefixEnd_971600 := by exact prefixLift 971600
  have htrace : WordTrace (prefixWord ++ tailWord_971600) baseStart_971600 baseEnd_971600 := by
    simpa [prefixWord, tailWord_971600, baseEnd_971600] using wordTrace_append hprefix tailTrace_971600
  have hstable : (prefixWord ++ tailWord_971600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971600).length < 2 ^ (prefixWord ++ tailWord_971600).sum := by decide
  have hdescent : baseEnd_971600 < baseStart_971600 := by decide
  rcases family_descends (prefixWord ++ tailWord_971600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971623 : List Nat := [1, 1, 5, 1, 2, 3, 2, 8]
def baseStart_971623 : Nat := 118140960795 + 971623 * 2 ^ 59
def prefixEnd_971623 : Nat := 4983230072969 + 3 ^ 40 * 971623 * 2
def baseEnd_971623 : Nat := 18478133850502120527559

theorem tailTrace_971623 : CollatzResearch.WordTrace tailWord_971623 prefixEnd_971623 18478133850502120527559 := by
  unfold tailWord_971623
  simp only [CollatzResearch.WordTrace]
  refine ⟨35438002158983285842351523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23625334772655523894901015 35438002158983285842351523)
  ·
    refine ⟨53157003238474928763527285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35438002158983285842351523 53157003238474928763527285)
    ·
      refine ⟨4983469053607024571580683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53157003238474928763527285 4983469053607024571580683)
      ·
        refine ⟨7475203580410536857371025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983469053607024571580683 7475203580410536857371025)
        ·
          refine ⟨5606402685307902643028269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7475203580410536857371025 5606402685307902643028269)
          ·
            refine ⟨2102401006990463491135601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5606402685307902643028269 2102401006990463491135601)
            ·
              refine ⟨1576800755242847618351701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102401006990463491135601 1576800755242847618351701)
              ·
                refine ⟨18478133850502120527559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1576800755242847618351701 18478133850502120527559)
                ·
                  rfl

theorem cell23_971623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 8].length) (baseStart_971623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971623 prefixEnd_971623 := by exact prefixLift 971623
  have htrace : WordTrace (prefixWord ++ tailWord_971623) baseStart_971623 baseEnd_971623 := by
    simpa [prefixWord, tailWord_971623, baseEnd_971623] using wordTrace_append hprefix tailTrace_971623
  have hstable : (prefixWord ++ tailWord_971623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971623).length < 2 ^ (prefixWord ++ tailWord_971623).sum := by decide
  have hdescent : baseEnd_971623 < baseStart_971623 := by decide
  rcases family_descends (prefixWord ++ tailWord_971623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971637 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_971637 : Nat := 118140960795 + 971637 * 2 ^ 59
def prefixEnd_971637 : Nat := 4983230072969 + 3 ^ 40 * 971637 * 2
def baseEnd_971637 : Nat := 498916802692720199469029

theorem tailTrace_971637 : CollatzResearch.WordTrace tailWord_971637 prefixEnd_971637 498916802692720199469029 := by
  unfold tailWord_971637
  simp only [CollatzResearch.WordTrace]
  refine ⟨35438512780932566233361165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23625675187288377488907443 35438512780932566233361165)
  ·
    refine ⟨13289442292849712337510437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35438512780932566233361165 13289442292849712337510437)
    ·
      refine ⟨2491770429909321063283207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13289442292849712337510437 2491770429909321063283207)
      ·
        refine ⟨3737655644863981594924811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2491770429909321063283207 3737655644863981594924811)
        ·
          refine ⟨5606483467295972392387217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3737655644863981594924811 5606483467295972392387217)
          ·
            refine ⟨4204862600471979294290413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5606483467295972392387217 4204862600471979294290413)
            ·
              refine ⟨1576823475176992235358905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4204862600471979294290413 1576823475176992235358905)
              ·
                refine ⟨1182617606382744176519179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576823475176992235358905 1182617606382744176519179)
                ·
                  refine ⟨1773926409574116264778769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182617606382744176519179 1773926409574116264778769)
                  ·
                    refine ⟨1330444807180587198584077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773926409574116264778769 1330444807180587198584077)
                    ·
                      refine ⟨498916802692720199469029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1330444807180587198584077 498916802692720199469029)
                      ·
                        rfl

theorem cell23_971637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_971637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971637 prefixEnd_971637 := by exact prefixLift 971637
  have htrace : WordTrace (prefixWord ++ tailWord_971637) baseStart_971637 baseEnd_971637 := by
    simpa [prefixWord, tailWord_971637, baseEnd_971637] using wordTrace_append hprefix tailTrace_971637
  have hstable : (prefixWord ++ tailWord_971637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971637).length < 2 ^ (prefixWord ++ tailWord_971637).sum := by decide
  have hdescent : baseEnd_971637 < baseStart_971637 := by decide
  rcases family_descends (prefixWord ++ tailWord_971637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971702 : List Nat := [5, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_971702 : Nat := 118140960795 + 971702 * 2 ^ 59
def prefixEnd_971702 : Nat := 4983230072969 + 3 ^ 40 * 971702 * 2
def baseEnd_971702 : Nat := 498950178935262445156231

theorem tailTrace_971702 : CollatzResearch.WordTrace tailWord_971702 prefixEnd_971702 498950178935262445156231 := by
  unfold tailWord_971702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215055220356067645904835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23627255683798054889651573 2215055220356067645904835)
  ·
    refine ⟨3322582830534101468857253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2215055220356067645904835 3322582830534101468857253)
    ·
      refine ⟨622984280725144025410735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3322582830534101468857253 622984280725144025410735)
      ·
        refine ⟨934476421087716038116103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622984280725144025410735 934476421087716038116103)
        ·
          refine ⟨1401714631631574057174155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934476421087716038116103 1401714631631574057174155)
          ·
            refine ⟨2102571947447361085761233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401714631631574057174155 2102571947447361085761233)
            ·
              refine ⟨1576928960585520814320925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102571947447361085761233 1576928960585520814320925)
              ·
                refine ⟨591348360219570305370347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1576928960585520814320925 591348360219570305370347)
                ·
                  refine ⟨887022540329355458055521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591348360219570305370347 887022540329355458055521)
                  ·
                    refine ⟨665266905247016593541641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 887022540329355458055521 665266905247016593541641)
                    ·
                      refine ⟨498950178935262445156231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665266905247016593541641 498950178935262445156231)
                      ·
                        rfl

theorem cell23_971702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_971702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971702 prefixEnd_971702 := by exact prefixLift 971702
  have htrace : WordTrace (prefixWord ++ tailWord_971702) baseStart_971702 baseEnd_971702 := by
    simpa [prefixWord, tailWord_971702, baseEnd_971702] using wordTrace_append hprefix tailTrace_971702
  have hstable : (prefixWord ++ tailWord_971702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971702).length < 2 ^ (prefixWord ++ tailWord_971702).sum := by decide
  have hdescent : baseEnd_971702 < baseStart_971702 := by decide
  rcases family_descends (prefixWord ++ tailWord_971702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971730 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 7]
def baseStart_971730 : Nat := 118140960795 + 971730 * 2 ^ 59
def prefixEnd_971730 : Nat := 4983230072969 + 3 ^ 40 * 971730 * 2
def baseEnd_971730 : Nat := 55440506265954259511789

theorem tailTrace_971730 : CollatzResearch.WordTrace tailWord_971730 prefixEnd_971730 55440506265954259511789 := by
  unfold tailWord_971730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860476192398910779124161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23627936513063762077664429 8860476192398910779124161)
  ·
    refine ⟨6645357144299183084343121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8860476192398910779124161 6645357144299183084343121)
    ·
      refine ⟨4984017858224387313257341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6645357144299183084343121 4984017858224387313257341)
      ·
        refine ⟨1869006696834145242471503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4984017858224387313257341 1869006696834145242471503)
        ·
          refine ⟨2803510045251217863707255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869006696834145242471503 2803510045251217863707255)
          ·
            refine ⟨4205265067876826795560883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803510045251217863707255 4205265067876826795560883)
            ·
              refine ⟨6307897601815240193341325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205265067876826795560883 6307897601815240193341325)
              ·
                refine ⟨2365461600680715072502997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6307897601815240193341325 2365461600680715072502997)
                ·
                  refine ⟨55440506265954259511789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2365461600680715072502997 55440506265954259511789)
                  ·
                    rfl

theorem cell23_971730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_971730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971730 prefixEnd_971730 := by exact prefixLift 971730
  have htrace : WordTrace (prefixWord ++ tailWord_971730) baseStart_971730 baseEnd_971730 := by
    simpa [prefixWord, tailWord_971730, baseEnd_971730] using wordTrace_append hprefix tailTrace_971730
  have hstable : (prefixWord ++ tailWord_971730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971730).length < 2 ^ (prefixWord ++ tailWord_971730).sum := by decide
  have hdescent : baseEnd_971730 < baseStart_971730 := by decide
  rcases family_descends (prefixWord ++ tailWord_971730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971793 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_971793 : Nat := 118140960795 + 971793 * 2 ^ 59
def prefixEnd_971793 : Nat := 4983230072969 + 3 ^ 40 * 971793 * 2
def baseEnd_971793 : Nat := 498996905674821589118311

theorem tailTrace_971793 : CollatzResearch.WordTrace tailWord_971793 prefixEnd_971793 498996905674821589118311 := by
  unfold tailWord_971793
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444202568367404876040033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23629468378911603250693355 35444202568367404876040033)
  ·
    refine ⟨26583151926275553657030025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35444202568367404876040033 26583151926275553657030025)
    ·
      refine ⟨19937363944706665242772519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26583151926275553657030025 19937363944706665242772519)
      ·
        refine ⟨29906045917059997864158779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19937363944706665242772519 29906045917059997864158779)
        ·
          refine ⟨44859068875589996796238169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29906045917059997864158779 44859068875589996796238169)
          ·
            refine ⟨33644301656692497597178627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44859068875589996796238169 33644301656692497597178627)
            ·
              refine ⟨50466452485038746395767941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33644301656692497597178627 50466452485038746395767941)
              ·
                refine ⟨9462459840944764949206489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50466452485038746395767941 9462459840944764949206489)
                ·
                  refine ⟨7096844880708573711904867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9462459840944764949206489 7096844880708573711904867)
                  ·
                    refine ⟨10645267321062860567857301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7096844880708573711904867 10645267321062860567857301)
                    ·
                      refine ⟨498996905674821589118311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10645267321062860567857301 498996905674821589118311)
                      ·
                        rfl

theorem cell23_971793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_971793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971793 prefixEnd_971793 := by exact prefixLift 971793
  have htrace : WordTrace (prefixWord ++ tailWord_971793) baseStart_971793 baseEnd_971793 := by
    simpa [prefixWord, tailWord_971793, baseEnd_971793] using wordTrace_append hprefix tailTrace_971793
  have hstable : (prefixWord ++ tailWord_971793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971793).length < 2 ^ (prefixWord ++ tailWord_971793).sum := by decide
  have hdescent : baseEnd_971793 < baseStart_971793 := by decide
  rcases family_descends (prefixWord ++ tailWord_971793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971837 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 6]
def baseStart_971837 : Nat := 118140960795 + 971837 * 2 ^ 59
def prefixEnd_971837 : Nat := 4983230072969 + 3 ^ 40 * 971837 * 2
def baseEnd_971837 : Nat := 55446610980402157440901

theorem tailTrace_971837 : CollatzResearch.WordTrace tailWord_971837 prefixEnd_971837 55446610980402157440901 := by
  unfold tailWord_971837
  simp only [CollatzResearch.WordTrace]
  refine ⟨35445807380208000390641765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23630538253472000260427843 35445807380208000390641765)
  ·
    refine ⟨6646088883789000073245331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35445807380208000390641765 6646088883789000073245331)
    ·
      refine ⟨9969133325683500109867997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6646088883789000073245331 9969133325683500109867997)
      ·
        refine ⟨3738424997131312541200499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9969133325683500109867997 3738424997131312541200499)
        ·
          refine ⟨5607637495696968811800749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738424997131312541200499 5607637495696968811800749)
          ·
            refine ⟨2102864060886363304425281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5607637495696968811800749 2102864060886363304425281)
            ·
              refine ⟨1577148045664772478318961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102864060886363304425281 1577148045664772478318961)
              ·
                refine ⟨1182861034248579358739221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577148045664772478318961 1182861034248579358739221)
                ·
                  refine ⟨55446610980402157440901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1182861034248579358739221 55446610980402157440901)
                  ·
                    rfl

theorem cell23_971837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_971837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971837 prefixEnd_971837 := by exact prefixLift 971837
  have htrace : WordTrace (prefixWord ++ tailWord_971837) baseStart_971837 baseEnd_971837 := by
    simpa [prefixWord, tailWord_971837, baseEnd_971837] using wordTrace_append hprefix tailTrace_971837
  have hstable : (prefixWord ++ tailWord_971837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971837).length < 2 ^ (prefixWord ++ tailWord_971837).sum := by decide
  have hdescent : baseEnd_971837 < baseStart_971837 := by decide
  rcases family_descends (prefixWord ++ tailWord_971837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971841 : List Nat := [1, 2, 5, 1, 3, 1, 1, 4, 1, 4]
def baseStart_971841 : Nat := 118140960795 + 971841 * 2 ^ 59
def prefixEnd_971841 : Nat := 4983230072969 + 3 ^ 40 * 971841 * 2
def baseEnd_971841 : Nat := 166340517582079133772697

theorem tailTrace_971841 : CollatzResearch.WordTrace tailWord_971841 prefixEnd_971841 166340517582079133772697 := by
  unfold tailWord_971841
  simp only [CollatzResearch.WordTrace]
  refine ⟨35445953272193509073787377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23630635514795672715858251 35445953272193509073787377)
  ·
    refine ⟨26584464954145131805340533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35445953272193509073787377 26584464954145131805340533)
    ·
      refine ⟨2492293589451106106750675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26584464954145131805340533 2492293589451106106750675)
      ·
        refine ⟨3738440384176659160126013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492293589451106106750675 3738440384176659160126013)
        ·
          refine ⟨1401915144066247185047255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3738440384176659160126013 1401915144066247185047255)
          ·
            refine ⟨2102872716099370777570883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401915144066247185047255 2102872716099370777570883)
            ·
              refine ⟨3154309074149056166356325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102872716099370777570883 3154309074149056166356325)
              ·
                refine ⟨591432951402948031191811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3154309074149056166356325 591432951402948031191811)
                ·
                  refine ⟨887149427104422046787717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591432951402948031191811 887149427104422046787717)
                  ·
                    refine ⟨166340517582079133772697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 887149427104422046787717 166340517582079133772697)
                    ·
                      rfl

theorem cell23_971841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_971841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971841 prefixEnd_971841 := by exact prefixLift 971841
  have htrace : WordTrace (prefixWord ++ tailWord_971841) baseStart_971841 baseEnd_971841 := by
    simpa [prefixWord, tailWord_971841, baseEnd_971841] using wordTrace_append hprefix tailTrace_971841
  have hstable : (prefixWord ++ tailWord_971841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971841).length < 2 ^ (prefixWord ++ tailWord_971841).sum := by decide
  have hdescent : baseEnd_971841 < baseStart_971841 := by decide
  rcases family_descends (prefixWord ++ tailWord_971841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971850 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_971850 : Nat := 118140960795 + 971850 * 2 ^ 59
def prefixEnd_971850 : Nat := 4983230072969 + 3 ^ 40 * 971850 * 2
def baseEnd_971850 : Nat := 166342058024042622035183

theorem tailTrace_971850 : CollatzResearch.WordTrace tailWord_971850 prefixEnd_971850 166342058024042622035183 := by
  unfold tailWord_971850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8861570382290225902716251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23630854352773935740576669 8861570382290225902716251)
  ·
    refine ⟨13292355573435338854074377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8861570382290225902716251 13292355573435338854074377)
    ·
      refine ⟨9969266680076504140555783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13292355573435338854074377 9969266680076504140555783)
      ·
        refine ⟨14953900020114756210833675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9969266680076504140555783 14953900020114756210833675)
        ·
          refine ⟨22430850030172134316250513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14953900020114756210833675 22430850030172134316250513)
          ·
            refine ⟨16823137522629100737187885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22430850030172134316250513 16823137522629100737187885)
            ·
              refine ⟨6308676570985912776445457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16823137522629100737187885 6308676570985912776445457)
              ·
                refine ⟨4731507428239434582334093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308676570985912776445457 4731507428239434582334093)
                ·
                  refine ⟨1774315285589787968375285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4731507428239434582334093 1774315285589787968375285)
                  ·
                    refine ⟨166342058024042622035183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1774315285589787968375285 166342058024042622035183)
                    ·
                      rfl

theorem cell23_971850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_971850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971850 prefixEnd_971850 := by exact prefixLift 971850
  have htrace : WordTrace (prefixWord ++ tailWord_971850) baseStart_971850 baseEnd_971850 := by
    simpa [prefixWord, tailWord_971850, baseEnd_971850] using wordTrace_append hprefix tailTrace_971850
  have hstable : (prefixWord ++ tailWord_971850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971850).length < 2 ^ (prefixWord ++ tailWord_971850).sum := by decide
  have hdescent : baseEnd_971850 < baseStart_971850 := by decide
  rcases family_descends (prefixWord ++ tailWord_971850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971857 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 4, 3, 2]
def baseStart_971857 : Nat := 118140960795 + 971857 * 2 ^ 59
def prefixEnd_971857 : Nat := 4983230072969 + 3 ^ 40 * 971857 * 2
def baseEnd_971857 : Nat := 499029768436709338718017

theorem tailTrace_971857 : CollatzResearch.WordTrace tailWord_971857 prefixEnd_971857 499029768436709338718017 := by
  unfold tailWord_971857
  simp only [CollatzResearch.WordTrace]
  refine ⟨35446536840135543806369825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23631024560090362537579883 35446536840135543806369825)
  ·
    refine ⟨26584902630101657854777369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35446536840135543806369825 26584902630101657854777369)
    ·
      refine ⟨19938676972576243391083027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26584902630101657854777369 19938676972576243391083027)
      ·
        refine ⟨29908015458864365086624541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19938676972576243391083027 29908015458864365086624541)
        ·
          refine ⟨11215505797074136907484203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29908015458864365086624541 11215505797074136907484203)
          ·
            refine ⟨16823258695611205361226305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11215505797074136907484203 16823258695611205361226305)
            ·
              refine ⟨12617444021708404020919729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16823258695611205361226305 12617444021708404020919729)
              ·
                refine ⟨9463083016281303015689797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12617444021708404020919729 9463083016281303015689797)
                ·
                  refine ⟨1774328065552744315441837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9463083016281303015689797 1774328065552744315441837)
                  ·
                    refine ⟨665373024582279118290689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1774328065552744315441837 665373024582279118290689)
                    ·
                      refine ⟨499029768436709338718017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665373024582279118290689 499029768436709338718017)
                      ·
                        rfl

theorem cell23_971857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_971857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971857 prefixEnd_971857 := by exact prefixLift 971857
  have htrace : WordTrace (prefixWord ++ tailWord_971857) baseStart_971857 baseEnd_971857 := by
    simpa [prefixWord, tailWord_971857, baseEnd_971857] using wordTrace_append hprefix tailTrace_971857
  have hstable : (prefixWord ++ tailWord_971857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971857).length < 2 ^ (prefixWord ++ tailWord_971857).sum := by decide
  have hdescent : baseEnd_971857 < baseStart_971857 := by decide
  rcases family_descends (prefixWord ++ tailWord_971857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971881 : List Nat := [1, 2, 1, 1, 1, 7, 2, 3, 1, 1, 3]
def baseStart_971881 : Nat := 118140960795 + 971881 * 2 ^ 59
def prefixEnd_971881 : Nat := 4983230072969 + 3 ^ 40 * 971881 * 2
def baseEnd_971881 : Nat := 499042091972417244817907

theorem tailTrace_971881 : CollatzResearch.WordTrace tailWord_971881 prefixEnd_971881 499042091972417244817907 := by
  unfold tailWord_971881
  simp only [CollatzResearch.WordTrace]
  refine ⟨35447412192048595905243497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23631608128032397270162331 35447412192048595905243497)
  ·
    refine ⟨26585559144036446928932623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35447412192048595905243497 26585559144036446928932623)
    ·
      refine ⟨39878338716054670393398935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26585559144036446928932623 39878338716054670393398935)
      ·
        refine ⟨59817508074082005590098403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39878338716054670393398935 59817508074082005590098403)
        ·
          refine ⟨89726262111123008385147605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59817508074082005590098403 89726262111123008385147605)
          ·
            refine ⟨2102959268229445509026897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 89726262111123008385147605 2102959268229445509026897)
            ·
              refine ⟨1577219451172084131770173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102959268229445509026897 1577219451172084131770173)
              ·
                refine ⟨591457294189531549413815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577219451172084131770173 591457294189531549413815)
                ·
                  refine ⟨887185941284297324120723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591457294189531549413815 887185941284297324120723)
                  ·
                    refine ⟨1330778911926445986181085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 887185941284297324120723 1330778911926445986181085)
                    ·
                      refine ⟨499042091972417244817907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1330778911926445986181085 499042091972417244817907)
                      ·
                        rfl

theorem cell23_971881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 1, 3].length) (baseStart_971881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971881 prefixEnd_971881 := by exact prefixLift 971881
  have htrace : WordTrace (prefixWord ++ tailWord_971881) baseStart_971881 baseEnd_971881 := by
    simpa [prefixWord, tailWord_971881, baseEnd_971881] using wordTrace_append hprefix tailTrace_971881
  have hstable : (prefixWord ++ tailWord_971881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971881).length < 2 ^ (prefixWord ++ tailWord_971881).sum := by decide
  have hdescent : baseEnd_971881 < baseStart_971881 := by decide
  rcases family_descends (prefixWord ++ tailWord_971881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971887 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 4]
def baseStart_971887 : Nat := 118140960795 + 971887 * 2 ^ 59
def prefixEnd_971887 : Nat := 4983230072969 + 3 ^ 40 * 971887 * 2
def baseEnd_971887 : Nat := 499045172856344221342879

theorem tailTrace_971887 : CollatzResearch.WordTrace tailWord_971887 prefixEnd_971887 499045172856344221342879 := by
  unfold tailWord_971887
  simp only [CollatzResearch.WordTrace]
  refine ⟨35447631030026858929961915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23631754020017905953307943 35447631030026858929961915)
  ·
    refine ⟨53171446545040288394942873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35447631030026858929961915 53171446545040288394942873)
    ·
      refine ⟨39878584908780216296207155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53171446545040288394942873 39878584908780216296207155)
      ·
        refine ⟨59817877363170324444310733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39878584908780216296207155 59817877363170324444310733)
        ·
          refine ⟨22431704011188871666616525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59817877363170324444310733 22431704011188871666616525)
          ·
            refine ⟨8411889004195826874981197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22431704011188871666616525 8411889004195826874981197)
            ·
              refine ⟨3154458376573435078117949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8411889004195826874981197 3154458376573435078117949)
              ·
                refine ⟨1182921891215038154294231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3154458376573435078117949 1182921891215038154294231)
                ·
                  refine ⟨1774382836822557231441347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182921891215038154294231 1774382836822557231441347)
                  ·
                    refine ⟨2661574255233835847162021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1774382836822557231441347 2661574255233835847162021)
                    ·
                      refine ⟨499045172856344221342879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2661574255233835847162021 499045172856344221342879)
                      ·
                        rfl

theorem cell23_971887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_971887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971887 prefixEnd_971887 := by exact prefixLift 971887
  have htrace : WordTrace (prefixWord ++ tailWord_971887) baseStart_971887 baseEnd_971887 := by
    simpa [prefixWord, tailWord_971887, baseEnd_971887] using wordTrace_append hprefix tailTrace_971887
  have hstable : (prefixWord ++ tailWord_971887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971887).length < 2 ^ (prefixWord ++ tailWord_971887).sum := by decide
  have hdescent : baseEnd_971887 < baseStart_971887 := by decide
  rcases family_descends (prefixWord ++ tailWord_971887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971900 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_971900 : Nat := 118140960795 + 971900 * 2 ^ 59
def prefixEnd_971900 : Nat := 4983230072969 + 3 ^ 40 * 971900 * 2
def baseEnd_971900 : Nat := 499051848104852670480319

theorem tailTrace_971900 : CollatzResearch.WordTrace tailWord_971900 prefixEnd_971900 499051848104852670480319 := by
  unfold tailWord_971900
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724052589489881075092577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23632070119319841433456769 17724052589489881075092577)
  ·
    refine ⟨13293039442117410806319433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17724052589489881075092577 13293039442117410806319433)
    ·
      refine ⟨9969779581588058104739575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13293039442117410806319433 9969779581588058104739575)
      ·
        refine ⟨14954669372382087157109363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9969779581588058104739575 14954669372382087157109363)
        ·
          refine ⟨22432004058573130735664045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14954669372382087157109363 22432004058573130735664045)
          ·
            refine ⟨8412001521964924025874017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22432004058573130735664045 8412001521964924025874017)
            ·
              refine ⟨6309001141473693019405513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412001521964924025874017 6309001141473693019405513)
              ·
                refine ⟨4731750856105269764554135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6309001141473693019405513 4731750856105269764554135)
                ·
                  refine ⟨7097626284157904646831203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731750856105269764554135 7097626284157904646831203)
                  ·
                    refine ⟨10646439426236856970246805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7097626284157904646831203 10646439426236856970246805)
                    ·
                      refine ⟨499051848104852670480319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10646439426236856970246805 499051848104852670480319)
                      ·
                        rfl

theorem cell23_971900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_971900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971900 prefixEnd_971900 := by exact prefixLift 971900
  have htrace : WordTrace (prefixWord ++ tailWord_971900) baseStart_971900 baseEnd_971900 := by
    simpa [prefixWord, tailWord_971900, baseEnd_971900] using wordTrace_append hprefix tailTrace_971900
  have hstable : (prefixWord ++ tailWord_971900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971900).length < 2 ^ (prefixWord ++ tailWord_971900).sum := by decide
  have hdescent : baseEnd_971900 < baseStart_971900 := by decide
  rcases family_descends (prefixWord ++ tailWord_971900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971904 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 3, 2, 2]
def baseStart_971904 : Nat := 118140960795 + 971904 * 2 ^ 59
def prefixEnd_971904 : Nat := 4983230072969 + 3 ^ 40 * 971904 * 2
def baseEnd_971904 : Nat := 499053902027470654830301

theorem tailTrace_971904 : CollatzResearch.WordTrace tailWord_971904 prefixEnd_971904 499053902027470654830301 := by
  unfold tailWord_971904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724125535482635416665383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23632167380643513888887177 17724125535482635416665383)
  ·
    refine ⟨26586188303223953124998075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17724125535482635416665383 26586188303223953124998075)
    ·
      refine ⟨39879282454835929687497113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26586188303223953124998075 39879282454835929687497113)
      ·
        refine ⟨29909461841126947265622835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39879282454835929687497113 29909461841126947265622835)
        ·
          refine ⟨44864192761690420898434253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29909461841126947265622835 44864192761690420898434253)
          ·
            refine ⟨16824072285633907836912845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44864192761690420898434253 16824072285633907836912845)
            ·
              refine ⟨6309027107112715438842317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16824072285633907836912845 6309027107112715438842317)
              ·
                refine ⟨2365885165167268289565869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6309027107112715438842317 2365885165167268289565869)
                ·
                  refine ⟨887206936937725608587201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2365885165167268289565869 887206936937725608587201)
                  ·
                    refine ⟨665405202703294206440401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 887206936937725608587201 665405202703294206440401)
                    ·
                      refine ⟨499053902027470654830301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665405202703294206440401 499053902027470654830301)
                      ·
                        rfl

theorem cell23_971904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_971904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971904 prefixEnd_971904 := by exact prefixLift 971904
  have htrace : WordTrace (prefixWord ++ tailWord_971904) baseStart_971904 baseEnd_971904 := by
    simpa [prefixWord, tailWord_971904, baseEnd_971904] using wordTrace_append hprefix tailTrace_971904
  have hstable : (prefixWord ++ tailWord_971904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971904).length < 2 ^ (prefixWord ++ tailWord_971904).sum := by decide
  have hdescent : baseEnd_971904 < baseStart_971904 := by decide
  rcases family_descends (prefixWord ++ tailWord_971904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971927 : List Nat := [1, 1, 3, 3, 3, 1, 4, 7]
def baseStart_971927 : Nat := 118140960795 + 971927 * 2 ^ 59
def prefixEnd_971927 : Nat := 4983230072969 + 3 ^ 40 * 971927 * 2
def baseEnd_971927 : Nat := 18483915262315706105285

theorem tailTrace_971927 : CollatzResearch.WordTrace tailWord_971927 prefixEnd_971927 18483915262315706105285 := by
  unfold tailWord_971927
  simp only [CollatzResearch.WordTrace]
  refine ⟨35449089949881945761418035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23632726633254630507612023 35449089949881945761418035)
  ·
    refine ⟨53173634924822918642127053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35449089949881945761418035 53173634924822918642127053)
    ·
      refine ⟨19940113096808594490797645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53173634924822918642127053 19940113096808594490797645)
      ·
        refine ⟨7477542411303222934049117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19940113096808594490797645 7477542411303222934049117)
        ·
          refine ⟨2804078404238708600268419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7477542411303222934049117 2804078404238708600268419)
          ·
            refine ⟨4206117606358062900402629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804078404238708600268419 4206117606358062900402629)
            ·
              refine ⟨788647051192136793825493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4206117606358062900402629 788647051192136793825493)
              ·
                refine ⟨18483915262315706105285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 788647051192136793825493 18483915262315706105285)
                ·
                  rfl

theorem cell23_971927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 7].length) (baseStart_971927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971927 prefixEnd_971927 := by exact prefixLift 971927
  have htrace : WordTrace (prefixWord ++ tailWord_971927) baseStart_971927 baseEnd_971927 := by
    simpa [prefixWord, tailWord_971927, baseEnd_971927] using wordTrace_append hprefix tailTrace_971927
  have hstable : (prefixWord ++ tailWord_971927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971927).length < 2 ^ (prefixWord ++ tailWord_971927).sum := by decide
  have hdescent : baseEnd_971927 < baseStart_971927 := by decide
  rcases family_descends (prefixWord ++ tailWord_971927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971937 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_971937 : Nat := 118140960795 + 971937 * 2 ^ 59
def prefixEnd_971937 : Nat := 4983230072969 + 3 ^ 40 * 971937 * 2
def baseEnd_971937 : Nat := 499070846889069025717649

theorem tailTrace_971937 : CollatzResearch.WordTrace tailWord_971937 prefixEnd_971937 499070846889069025717649 := by
  unfold tailWord_971937
  simp only [CollatzResearch.WordTrace]
  refine ⟨35449454679845717469282065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23632969786563811646188043 35449454679845717469282065)
  ·
    refine ⟨26587091009884288101961549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35449454679845717469282065 26587091009884288101961549)
    ·
      refine ⟨9970159128706608038235581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26587091009884288101961549 9970159128706608038235581)
      ·
        refine ⟨3738809673264978014338343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9970159128706608038235581 3738809673264978014338343)
        ·
          refine ⟨5608214509897467021507515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738809673264978014338343 5608214509897467021507515)
          ·
            refine ⟨8412321764846200532261273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608214509897467021507515 8412321764846200532261273)
            ·
              refine ⟨6309241323634650399195955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412321764846200532261273 6309241323634650399195955)
              ·
                refine ⟨9463861985451975598793933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309241323634650399195955 9463861985451975598793933)
                ·
                  refine ⟨3548948244544490849547725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9463861985451975598793933 3548948244544490849547725)
                  ·
                    refine ⟨1330855591704184068580397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548948244544490849547725 1330855591704184068580397)
                    ·
                      refine ⟨499070846889069025717649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1330855591704184068580397 499070846889069025717649)
                      ·
                        rfl

theorem cell23_971937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_971937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971937 prefixEnd_971937 := by exact prefixLift 971937
  have htrace : WordTrace (prefixWord ++ tailWord_971937) baseStart_971937 baseEnd_971937 := by
    simpa [prefixWord, tailWord_971937, baseEnd_971937] using wordTrace_append hprefix tailTrace_971937
  have hstable : (prefixWord ++ tailWord_971937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971937).length < 2 ^ (prefixWord ++ tailWord_971937).sum := by decide
  have hdescent : baseEnd_971937 < baseStart_971937 := by decide
  rcases family_descends (prefixWord ++ tailWord_971937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971954 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_971954 : Nat := 118140960795 + 971954 * 2 ^ 59
def prefixEnd_971954 : Nat := 4983230072969 + 3 ^ 40 * 971954 * 2
def baseEnd_971954 : Nat := 499079576060195459205071

theorem tailTrace_971954 : CollatzResearch.WordTrace tailWord_971954 prefixEnd_971954 499079576060195459205071 := by
  unfold tailWord_971954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862518680196032343162729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23633383147189419581767277 8862518680196032343162729)
  ·
    refine ⟨6646889010147024257372047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8862518680196032343162729 6646889010147024257372047)
    ·
      refine ⟨9970333515220536386058071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6646889010147024257372047 9970333515220536386058071)
      ·
        refine ⟨14955500272830804579087107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9970333515220536386058071 14955500272830804579087107)
        ·
          refine ⟨22433250409246206868630661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14955500272830804579087107 22433250409246206868630661)
          ·
            refine ⟨4206234451733663787868249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22433250409246206868630661 4206234451733663787868249)
            ·
              refine ⟨3154675838800247840901187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4206234451733663787868249 3154675838800247840901187)
              ·
                refine ⟨4732013758200371761351781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154675838800247840901187 4732013758200371761351781)
                ·
                  refine ⟨887252579662569705253459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4732013758200371761351781 887252579662569705253459)
                  ·
                    refine ⟨1330878869493854557880189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 887252579662569705253459 1330878869493854557880189)
                    ·
                      refine ⟨499079576060195459205071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1330878869493854557880189 499079576060195459205071)
                      ·
                        rfl

theorem cell23_971954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_971954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_971954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_971954 prefixEnd_971954 := by exact prefixLift 971954
  have htrace : WordTrace (prefixWord ++ tailWord_971954) baseStart_971954 baseEnd_971954 := by
    simpa [prefixWord, tailWord_971954, baseEnd_971954] using wordTrace_append hprefix tailTrace_971954
  have hstable : (prefixWord ++ tailWord_971954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971954).length < 2 ^ (prefixWord ++ tailWord_971954).sum := by decide
  have hdescent : baseEnd_971954 < baseStart_971954 := by decide
  rcases family_descends (prefixWord ++ tailWord_971954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972011 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 2, 2, 2]
def baseStart_972011 : Nat := 118140960795 + 972011 * 2 ^ 59
def prefixEnd_972011 : Nat := 4983230072969 + 3 ^ 40 * 972011 * 2
def baseEnd_972011 : Nat := 499108844457501736192309

theorem tailTrace_972011 : CollatzResearch.WordTrace tailWord_972011 prefixEnd_972011 499108844457501736192309 := by
  unfold tailWord_972011
  simp only [CollatzResearch.WordTrace]
  refine ⟨35452153681577628107475887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23634769121051752071650591 35452153681577628107475887)
  ·
    refine ⟨53178230522366442161213831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35452153681577628107475887 53178230522366442161213831)
    ·
      refine ⟨79767345783549663241820747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53178230522366442161213831 79767345783549663241820747)
      ·
        refine ⟨119651018675324494862731121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79767345783549663241820747 119651018675324494862731121)
        ·
          refine ⟨89738264006493371147048341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119651018675324494862731121 89738264006493371147048341)
          ·
            refine ⟨4206481125304376772517891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89738264006493371147048341 4206481125304376772517891)
            ·
              refine ⟨6309721687956565158776837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206481125304376772517891 6309721687956565158776837)
              ·
                refine ⟨1183072816491855967270657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6309721687956565158776837 1183072816491855967270657)
                ·
                  refine ⟨887304612368891975452993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1183072816491855967270657 887304612368891975452993)
                  ·
                    refine ⟨665478459276668981589745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 887304612368891975452993 665478459276668981589745)
                    ·
                      refine ⟨499108844457501736192309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665478459276668981589745 499108844457501736192309)
                      ·
                        rfl

theorem cell23_972011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 2, 2].length) (baseStart_972011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972011 prefixEnd_972011 := by exact prefixLift 972011
  have htrace : WordTrace (prefixWord ++ tailWord_972011) baseStart_972011 baseEnd_972011 := by
    simpa [prefixWord, tailWord_972011, baseEnd_972011] using wordTrace_append hprefix tailTrace_972011
  have hstable : (prefixWord ++ tailWord_972011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972011).length < 2 ^ (prefixWord ++ tailWord_972011).sum := by decide
  have hdescent : baseEnd_972011 < baseStart_972011 := by decide
  rcases family_descends (prefixWord ++ tailWord_972011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972084 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_972084 : Nat := 118140960795 + 972084 * 2 ^ 59
def prefixEnd_972084 : Nat := 4983230072969 + 3 ^ 40 * 972084 * 2
def baseEnd_972084 : Nat := 499146328545279950579473

theorem tailTrace_972084 : CollatzResearch.WordTrace tailWord_972084 prefixEnd_972084 499146328545279950579473 := by
  unfold tailWord_972084
  simp only [CollatzResearch.WordTrace]
  refine ⟨17727408105156580787441653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23636544140208774383255537 17727408105156580787441653)
  ·
    refine ⟨1661944509858429448822655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17727408105156580787441653 1661944509858429448822655)
    ·
      refine ⟨2492916764787644173233983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661944509858429448822655 2492916764787644173233983)
      ·
        refine ⟨3739375147181466259850975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492916764787644173233983 3739375147181466259850975)
        ·
          refine ⟨5609062720772199389776463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3739375147181466259850975 5609062720772199389776463)
          ·
            refine ⟨8413594081158299084664695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609062720772199389776463 8413594081158299084664695)
            ·
              refine ⟨12620391121737448626997043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413594081158299084664695 12620391121737448626997043)
              ·
                refine ⟨18930586682606172940495565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12620391121737448626997043 18930586682606172940495565)
                ·
                  refine ⟨7098970005977314852685837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18930586682606172940495565 7098970005977314852685837)
                  ·
                    refine ⟨2662113752241493069757189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7098970005977314852685837 2662113752241493069757189)
                    ·
                      refine ⟨499146328545279950579473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2662113752241493069757189 499146328545279950579473)
                      ·
                        rfl

theorem cell23_972084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_972084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972084 prefixEnd_972084 := by exact prefixLift 972084
  have htrace : WordTrace (prefixWord ++ tailWord_972084) baseStart_972084 baseEnd_972084 := by
    simpa [prefixWord, tailWord_972084, baseEnd_972084] using wordTrace_append hprefix tailTrace_972084
  have hstable : (prefixWord ++ tailWord_972084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972084).length < 2 ^ (prefixWord ++ tailWord_972084).sum := by decide
  have hdescent : baseEnd_972084 < baseStart_972084 := by decide
  rcases family_descends (prefixWord ++ tailWord_972084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972102 : List Nat := [6, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_972102 : Nat := 118140960795 + 972102 * 2 ^ 59
def prefixEnd_972102 : Nat := 4983230072969 + 3 ^ 40 * 972102 * 2
def baseEnd_972102 : Nat := 55461730133006764461599

theorem tailTrace_972102 : CollatzResearch.WordTrace tailWord_972102 prefixEnd_972102 55461730133006764461599 := by
  unfold tailWord_972102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107983522632748457782455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23636981816165300432692373 1107983522632748457782455)
  ·
    refine ⟨1661975283949122686673683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1107983522632748457782455 1661975283949122686673683)
    ·
      refine ⟨2492962925923684030010525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661975283949122686673683 2492962925923684030010525)
      ·
        refine ⟨934861097221381511253947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2492962925923684030010525 934861097221381511253947)
        ·
          refine ⟨1402291645832072266880921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934861097221381511253947 1402291645832072266880921)
          ·
            refine ⟨1051718734374054200160691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402291645832072266880921 1051718734374054200160691)
            ·
              refine ⟨1577578101561081300241037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051718734374054200160691 1577578101561081300241037)
              ·
                refine ⟨591591788085405487590389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577578101561081300241037 591591788085405487590389)
                ·
                  refine ⟨55461730133006764461599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591591788085405487590389 55461730133006764461599)
                  ·
                    rfl

theorem cell23_972102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_972102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972102 prefixEnd_972102 := by exact prefixLift 972102
  have htrace : WordTrace (prefixWord ++ tailWord_972102) baseStart_972102 baseEnd_972102 := by
    simpa [prefixWord, tailWord_972102, baseEnd_972102] using wordTrace_append hprefix tailTrace_972102
  have hstable : (prefixWord ++ tailWord_972102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972102).length < 2 ^ (prefixWord ++ tailWord_972102).sum := by decide
  have hdescent : baseEnd_972102 < baseStart_972102 := by decide
  rcases family_descends (prefixWord ++ tailWord_972102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972104 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_972104 : Nat := 118140960795 + 972104 * 2 ^ 59
def prefixEnd_972104 : Nat := 4983230072969 + 3 ^ 40 * 972104 * 2
def baseEnd_972104 : Nat := 499156598158369872329381

theorem tailTrace_972104 : CollatzResearch.WordTrace tailWord_972104 prefixEnd_972104 499156598158369872329381 := by
  unfold tailWord_972104
  simp only [CollatzResearch.WordTrace]
  refine ⟨17727772835120352495305683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23637030446827136660407577 17727772835120352495305683)
  ·
    refine ⟨26591659252680528742958525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17727772835120352495305683 26591659252680528742958525)
    ·
      refine ⟨9971872219755198278609447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26591659252680528742958525 9971872219755198278609447)
      ·
        refine ⟨14957808329632797417914171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9971872219755198278609447 14957808329632797417914171)
        ·
          refine ⟨22436712494449196126871257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14957808329632797417914171 22436712494449196126871257)
          ·
            refine ⟨16827534370836897095153443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22436712494449196126871257 16827534370836897095153443)
            ·
              refine ⟨25241301556255345642730165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827534370836897095153443 25241301556255345642730165)
              ·
                refine ⟨2366372020898938654005953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25241301556255345642730165 2366372020898938654005953)
                ·
                  refine ⟨1774779015674203990504465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2366372020898938654005953 1774779015674203990504465)
                  ·
                    refine ⟨1331084261755652992878349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1774779015674203990504465 1331084261755652992878349)
                    ·
                      refine ⟨499156598158369872329381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1331084261755652992878349 499156598158369872329381)
                      ·
                        rfl

theorem cell23_972104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_972104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972104 prefixEnd_972104 := by exact prefixLift 972104
  have htrace : WordTrace (prefixWord ++ tailWord_972104) baseStart_972104 baseEnd_972104 := by
    simpa [prefixWord, tailWord_972104, baseEnd_972104] using wordTrace_append hprefix tailTrace_972104
  have hstable : (prefixWord ++ tailWord_972104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972104).length < 2 ^ (prefixWord ++ tailWord_972104).sum := by decide
  have hdescent : baseEnd_972104 < baseStart_972104 := by decide
  rcases family_descends (prefixWord ++ tailWord_972104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972141 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 6]
def baseStart_972141 : Nat := 118140960795 + 972141 * 2 ^ 59
def prefixEnd_972141 : Nat := 4983230072969 + 3 ^ 40 * 972141 * 2
def baseEnd_972141 : Nat := 55463955215842914174079

theorem tailTrace_972141 : CollatzResearch.WordTrace tailWord_972141 prefixEnd_972141 55463955215842914174079 := by
  unfold tailWord_972141
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456895171106660309708277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23637930114071106873138851 35456895171106660309708277)
  ·
    refine ⟨3324083922291249404035151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35456895171106660309708277 3324083922291249404035151)
    ·
      refine ⟨4986125883436874106052727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324083922291249404035151 4986125883436874106052727)
      ·
        refine ⟨7479188825155311159079091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986125883436874106052727 7479188825155311159079091)
        ·
          refine ⟨11218783237732966738618637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479188825155311159079091 11218783237732966738618637)
          ·
            refine ⟨4207043714149862526981989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11218783237732966738618637 4207043714149862526981989)
            ·
              refine ⟨788820696403099223809123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4207043714149862526981989 788820696403099223809123)
              ·
                refine ⟨1183231044604648835713685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788820696403099223809123 1183231044604648835713685)
                ·
                  refine ⟨55463955215842914174079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1183231044604648835713685 55463955215842914174079)
                  ·
                    rfl

theorem cell23_972141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_972141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972141 prefixEnd_972141 := by exact prefixLift 972141
  have htrace : WordTrace (prefixWord ++ tailWord_972141) baseStart_972141 baseEnd_972141 := by
    simpa [prefixWord, tailWord_972141, baseEnd_972141] using wordTrace_append hprefix tailTrace_972141
  have hstable : (prefixWord ++ tailWord_972141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972141).length < 2 ^ (prefixWord ++ tailWord_972141).sum := by decide
  have hdescent : baseEnd_972141 < baseStart_972141 := by decide
  rcases family_descends (prefixWord ++ tailWord_972141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972171 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 1, 5]
def baseStart_972171 : Nat := 118140960795 + 972171 * 2 ^ 59
def prefixEnd_972171 : Nat := 4983230072969 + 3 ^ 40 * 972171 * 2
def baseEnd_972171 : Nat := 166397000454073703397191

theorem tailTrace_972171 : CollatzResearch.WordTrace tailWord_972171 prefixEnd_972171 166397000454073703397191 := by
  unfold tailWord_972171
  simp only [CollatzResearch.WordTrace]
  refine ⟨35457989360997975433300367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23638659573998650288866911 35457989360997975433300367)
  ·
    refine ⟨53186984041496963149950551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35457989360997975433300367 53186984041496963149950551)
    ·
      refine ⟨79780476062245444724925827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53186984041496963149950551 79780476062245444724925827)
      ·
        refine ⟨119670714093368167087388741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79780476062245444724925827 119670714093368167087388741)
        ·
          refine ⟨22438258892506531328885389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119670714093368167087388741 22438258892506531328885389)
          ·
            refine ⟨8414347084689949248332021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22438258892506531328885389 8414347084689949248332021)
            ·
              refine ⟨788845039189682742031127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8414347084689949248332021 788845039189682742031127)
              ·
                refine ⟨1183267558784524113046691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788845039189682742031127 1183267558784524113046691)
                ·
                  refine ⟨1774901338176786169570037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183267558784524113046691 1774901338176786169570037)
                  ·
                    refine ⟨166397000454073703397191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1774901338176786169570037 166397000454073703397191)
                    ·
                      rfl

theorem cell23_972171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 5].length) (baseStart_972171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972171 prefixEnd_972171 := by exact prefixLift 972171
  have htrace : WordTrace (prefixWord ++ tailWord_972171) baseStart_972171 baseEnd_972171 := by
    simpa [prefixWord, tailWord_972171, baseEnd_972171] using wordTrace_append hprefix tailTrace_972171
  have hstable : (prefixWord ++ tailWord_972171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972171).length < 2 ^ (prefixWord ++ tailWord_972171).sum := by decide
  have hdescent : baseEnd_972171 < baseStart_972171 := by decide
  rcases family_descends (prefixWord ++ tailWord_972171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972185 : List Nat := [1, 2, 1, 2, 1, 5, 4, 2, 1, 1, 3]
def baseStart_972185 : Nat := 118140960795 + 972185 * 2 ^ 59
def prefixEnd_972185 : Nat := 4983230072969 + 3 ^ 40 * 972185 * 2
def baseEnd_972185 : Nat := 499198190091384055416509

theorem tailTrace_972185 : CollatzResearch.WordTrace tailWord_972185 prefixEnd_972185 499198190091384055416509 := by
  unfold tailWord_972185
  simp only [CollatzResearch.WordTrace]
  refine ⟨35458499982947255824310009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23638999988631503882873339 35458499982947255824310009)
  ·
    refine ⟨26593874987210441868232507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35458499982947255824310009 26593874987210441868232507)
    ·
      refine ⟨39890812480815662802348761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26593874987210441868232507 39890812480815662802348761)
      ·
        refine ⟨29918109360611747101761571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39890812480815662802348761 29918109360611747101761571)
        ·
          refine ⟨44877164040917620652642357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29918109360611747101761571 44877164040917620652642357)
          ·
            refine ⟨4207234128836026936185221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44877164040917620652642357 4207234128836026936185221)
            ·
              refine ⟨788856399156755050534729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4207234128836026936185221 788856399156755050534729)
              ·
                refine ⟨591642299367566287901047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788856399156755050534729 591642299367566287901047)
                ·
                  refine ⟨887463449051349431851571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591642299367566287901047 887463449051349431851571)
                  ·
                    refine ⟨1331195173577024147777357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 887463449051349431851571 1331195173577024147777357)
                    ·
                      refine ⟨499198190091384055416509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1331195173577024147777357 499198190091384055416509)
                      ·
                        rfl

theorem cell23_972185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_972185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972185 prefixEnd_972185 := by exact prefixLift 972185
  have htrace : WordTrace (prefixWord ++ tailWord_972185) baseStart_972185 baseEnd_972185 := by
    simpa [prefixWord, tailWord_972185, baseEnd_972185] using wordTrace_append hprefix tailTrace_972185
  have hstable : (prefixWord ++ tailWord_972185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972185).length < 2 ^ (prefixWord ++ tailWord_972185).sum := by decide
  have hdescent : baseEnd_972185 < baseStart_972185 := by decide
  rcases family_descends (prefixWord ++ tailWord_972185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972197 : List Nat := [1, 3, 1, 2, 1, 1, 2, 12]
def baseStart_972197 : Nat := 118140960795 + 972197 * 2 ^ 59
def prefixEnd_972197 : Nat := 4983230072969 + 3 ^ 40 * 972197 * 2
def baseEnd_972197 : Nat := 18489050068860666980239

theorem tailTrace_972197 : CollatzResearch.WordTrace tailWord_972197 prefixEnd_972197 18489050068860666980239 := by
  unfold tailWord_972197
  simp only [CollatzResearch.WordTrace]
  refine ⟨35458937658903781873746845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23639291772602521249164563 35458937658903781873746845)
  ·
    refine ⟨13297101622088918202655067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35458937658903781873746845 13297101622088918202655067)
    ·
      refine ⟨19945652433133377303982601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13297101622088918202655067 19945652433133377303982601)
      ·
        refine ⟨14959239324850032977986951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19945652433133377303982601 14959239324850032977986951)
        ·
          refine ⟨22438858987275049466980427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14959239324850032977986951 22438858987275049466980427)
          ·
            refine ⟨33658288480912574200470641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22438858987275049466980427 33658288480912574200470641)
            ·
              refine ⟨25243716360684430650352981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33658288480912574200470641 25243716360684430650352981)
              ·
                refine ⟨18489050068860666980239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 25243716360684430650352981 18489050068860666980239)
                ·
                  rfl

theorem cell23_972197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 12].length) (baseStart_972197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972197 prefixEnd_972197 := by exact prefixLift 972197
  have htrace : WordTrace (prefixWord ++ tailWord_972197) baseStart_972197 baseEnd_972197 := by
    simpa [prefixWord, tailWord_972197, baseEnd_972197] using wordTrace_append hprefix tailTrace_972197
  have hstable : (prefixWord ++ tailWord_972197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972197).length < 2 ^ (prefixWord ++ tailWord_972197).sum := by decide
  have hdescent : baseEnd_972197 < baseStart_972197 := by decide
  rcases family_descends (prefixWord ++ tailWord_972197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972204 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_972204 : Nat := 118140960795 + 972204 * 2 ^ 59
def prefixEnd_972204 : Nat := 4983230072969 + 3 ^ 40 * 972204 * 2
def baseEnd_972204 : Nat := 499207946223819481078921

theorem tailTrace_972204 : CollatzResearch.WordTrace tailWord_972204 prefixEnd_972204 499207946223819481078921 := by
  unfold tailWord_972204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17729596484939211034625833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23639461979918948046167777 17729596484939211034625833)
  ·
    refine ⟨13297197363704408275969375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17729596484939211034625833 13297197363704408275969375)
    ·
      refine ⟨19945796045556612413954063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13297197363704408275969375 19945796045556612413954063)
      ·
        refine ⟨29918694068334918620931095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19945796045556612413954063 29918694068334918620931095)
        ·
          refine ⟨44878041102502377931396643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29918694068334918620931095 44878041102502377931396643)
          ·
            refine ⟨67317061653753566897094965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44878041102502377931396643 67317061653753566897094965)
            ·
              refine ⟨6310974530039396896602653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67317061653753566897094965 6310974530039396896602653)
              ·
                refine ⟨2366615448764773836225995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6310974530039396896602653 2366615448764773836225995)
                ·
                  refine ⟨3549923173147160754338993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366615448764773836225995 3549923173147160754338993)
                  ·
                    refine ⟨2662442379860370565754245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3549923173147160754338993 2662442379860370565754245)
                    ·
                      refine ⟨499207946223819481078921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2662442379860370565754245 499207946223819481078921)
                      ·
                        rfl

theorem cell23_972204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_972204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972204 prefixEnd_972204 := by exact prefixLift 972204
  have htrace : WordTrace (prefixWord ++ tailWord_972204) baseStart_972204 baseEnd_972204 := by
    simpa [prefixWord, tailWord_972204, baseEnd_972204] using wordTrace_append hprefix tailTrace_972204
  have hstable : (prefixWord ++ tailWord_972204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972204).length < 2 ^ (prefixWord ++ tailWord_972204).sum := by decide
  have hdescent : baseEnd_972204 < baseStart_972204 := by decide
  rcases family_descends (prefixWord ++ tailWord_972204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972207 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_972207 : Nat := 118140960795 + 972207 * 2 ^ 59
def prefixEnd_972207 : Nat := 4983230072969 + 3 ^ 40 * 972207 * 2
def baseEnd_972207 : Nat := 499209486665782969341407

theorem tailTrace_972207 : CollatzResearch.WordTrace tailWord_972207 prefixEnd_972207 499209486665782969341407 := by
  unfold tailWord_972207
  simp only [CollatzResearch.WordTrace]
  refine ⟨35459302388867553581610875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23639534925911702387740583 35459302388867553581610875)
  ·
    refine ⟨53188953583301330372416313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35459302388867553581610875 53188953583301330372416313)
    ·
      refine ⟨39891715187475997779312235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53188953583301330372416313 39891715187475997779312235)
      ·
        refine ⟨59837572781213996668968353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39891715187475997779312235 59837572781213996668968353)
        ·
          refine ⟨44878179585910497501726265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59837572781213996668968353 44878179585910497501726265)
          ·
            refine ⟨33658634689432873126294699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44878179585910497501726265 33658634689432873126294699)
            ·
              refine ⟨50487952034149309689442049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33658634689432873126294699 50487952034149309689442049)
              ·
                refine ⟨37865964025611982267081537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50487952034149309689442049 37865964025611982267081537)
                ·
                  refine ⟨28399473019208986700311153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37865964025611982267081537 28399473019208986700311153)
                  ·
                    refine ⟨21299604764406740025233365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28399473019208986700311153 21299604764406740025233365)
                    ·
                      refine ⟨499209486665782969341407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21299604764406740025233365 499209486665782969341407)
                      ·
                        rfl

theorem cell23_972207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_972207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972207 prefixEnd_972207 := by exact prefixLift 972207
  have htrace : WordTrace (prefixWord ++ tailWord_972207) baseStart_972207 baseEnd_972207 := by
    simpa [prefixWord, tailWord_972207, baseEnd_972207] using wordTrace_append hprefix tailTrace_972207
  have hstable : (prefixWord ++ tailWord_972207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972207).length < 2 ^ (prefixWord ++ tailWord_972207).sum := by decide
  have hdescent : baseEnd_972207 < baseStart_972207 := by decide
  rcases family_descends (prefixWord ++ tailWord_972207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972281 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 3, 4, 2]
def baseStart_972281 : Nat := 118140960795 + 972281 * 2 ^ 59
def prefixEnd_972281 : Nat := 4983230072969 + 3 ^ 40 * 972281 * 2
def baseEnd_972281 : Nat := 499247484234215679816067

theorem tailTrace_972281 : CollatzResearch.WordTrace tailWord_972281 prefixEnd_972281 499247484234215679816067 := by
  unfold tailWord_972281
  simp only [CollatzResearch.WordTrace]
  refine ⟨35462001390599464219804697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23641334260399642813203131 35462001390599464219804697)
  ·
    refine ⟨26596501042949598164853523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35462001390599464219804697 26596501042949598164853523)
    ·
      refine ⟨39894751564424397247280285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26596501042949598164853523 39894751564424397247280285)
      ·
        refine ⟨14960531836659148967730107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39894751564424397247280285 14960531836659148967730107)
        ·
          refine ⟨22440797754988723451595161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14960531836659148967730107 22440797754988723451595161)
          ·
            refine ⟨16830598316241542588696371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22440797754988723451595161 16830598316241542588696371)
            ·
              refine ⟨25245897474362313883044557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16830598316241542588696371 25245897474362313883044557)
              ·
                refine ⟨9467211552885867706141709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25245897474362313883044557 9467211552885867706141709)
                ·
                  refine ⟨3550204332332200389803141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9467211552885867706141709 3550204332332200389803141)
                  ·
                    refine ⟨665663312312287573088089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550204332332200389803141 665663312312287573088089)
                    ·
                      refine ⟨499247484234215679816067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665663312312287573088089 499247484234215679816067)
                      ·
                        rfl

theorem cell23_972281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_972281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972281 prefixEnd_972281 := by exact prefixLift 972281
  have htrace : WordTrace (prefixWord ++ tailWord_972281) baseStart_972281 baseEnd_972281 := by
    simpa [prefixWord, tailWord_972281, baseEnd_972281] using wordTrace_append hprefix tailTrace_972281
  have hstable : (prefixWord ++ tailWord_972281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972281).length < 2 ^ (prefixWord ++ tailWord_972281).sum := by decide
  have hdescent : baseEnd_972281 < baseStart_972281 := by decide
  rcases family_descends (prefixWord ++ tailWord_972281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972284 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_972284 : Nat := 118140960795 + 972284 * 2 ^ 59
def prefixEnd_972284 : Nat := 4983230072969 + 3 ^ 40 * 972284 * 2
def baseEnd_972284 : Nat := 499249024676179168078553

theorem tailTrace_972284 : CollatzResearch.WordTrace tailWord_972284 prefixEnd_972284 499249024676179168078553 := by
  unfold tailWord_972284
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731055404794297866081953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23641407206392397154775937 17731055404794297866081953)
  ·
    refine ⟨13298291553595723399561465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17731055404794297866081953 13298291553595723399561465)
    ·
      refine ⟨9973718665196792549671099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13298291553595723399561465 9973718665196792549671099)
      ·
        refine ⟨14960577997795188824506649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9973718665196792549671099 14960577997795188824506649)
        ·
          refine ⟨11220433498346391618379987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14960577997795188824506649 11220433498346391618379987)
          ·
            refine ⟨16830650247519587427569981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11220433498346391618379987 16830650247519587427569981)
            ·
              refine ⟨6311493842819845285338743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16830650247519587427569981 6311493842819845285338743)
              ·
                refine ⟨9467240764229767928008115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311493842819845285338743 9467240764229767928008115)
                ·
                  refine ⟨14200861146344651892012173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9467240764229767928008115 14200861146344651892012173)
                  ·
                    refine ⟨5325322929879244459504565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14200861146344651892012173 5325322929879244459504565)
                    ·
                      refine ⟨499249024676179168078553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5325322929879244459504565 499249024676179168078553)
                      ·
                        rfl

theorem cell23_972284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_972284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972284 prefixEnd_972284 := by exact prefixLift 972284
  have htrace : WordTrace (prefixWord ++ tailWord_972284) baseStart_972284 baseEnd_972284 := by
    simpa [prefixWord, tailWord_972284, baseEnd_972284] using wordTrace_append hprefix tailTrace_972284
  have hstable : (prefixWord ++ tailWord_972284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972284).length < 2 ^ (prefixWord ++ tailWord_972284).sum := by decide
  have hdescent : baseEnd_972284 < baseStart_972284 := by decide
  rcases family_descends (prefixWord ++ tailWord_972284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972351 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 2, 5]
def baseStart_972351 : Nat := 118140960795 + 972351 * 2 ^ 59
def prefixEnd_972351 : Nat := 4983230072969 + 3 ^ 40 * 972351 * 2
def baseEnd_972351 : Nat := 166427809293343468646915

theorem tailTrace_972351 : CollatzResearch.WordTrace tailWord_972351 prefixEnd_972351 166427809293343468646915 := by
  unfold tailWord_972351
  simp only [CollatzResearch.WordTrace]
  refine ⟨35464554500345866174852907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23643036333563910783235271 35464554500345866174852907)
  ·
    refine ⟨53196831750518799262279361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35464554500345866174852907 53196831750518799262279361)
    ·
      refine ⟨39897623812889099446709521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53196831750518799262279361 39897623812889099446709521)
      ·
        refine ⟨29923217859666824585032141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39897623812889099446709521 29923217859666824585032141)
        ·
          refine ⟨11221206697375059219387053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29923217859666824585032141 11221206697375059219387053)
          ·
            refine ⟨4207952511515647207270145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11221206697375059219387053 4207952511515647207270145)
            ·
              refine ⟨3155964383636735405452609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207952511515647207270145 3155964383636735405452609)
              ·
                refine ⟨2366973287727551554089457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155964383636735405452609 2366973287727551554089457)
                ·
                  refine ⟨1775229965795663665567093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2366973287727551554089457 1775229965795663665567093)
                  ·
                    refine ⟨166427809293343468646915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1775229965795663665567093 166427809293343468646915)
                    ·
                      rfl

theorem cell23_972351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_972351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972351 prefixEnd_972351 := by exact prefixLift 972351
  have htrace : WordTrace (prefixWord ++ tailWord_972351) baseStart_972351 baseEnd_972351 := by
    simpa [prefixWord, tailWord_972351, baseEnd_972351] using wordTrace_append hprefix tailTrace_972351
  have hstable : (prefixWord ++ tailWord_972351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972351).length < 2 ^ (prefixWord ++ tailWord_972351).sum := by decide
  have hdescent : baseEnd_972351 < baseStart_972351 := by decide
  rcases family_descends (prefixWord ++ tailWord_972351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972365 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_972365 : Nat := 118140960795 + 972365 * 2 ^ 59
def prefixEnd_972365 : Nat := 4983230072969 + 3 ^ 40 * 972365 * 2
def baseEnd_972365 : Nat := 499290616609193351165681

theorem tailTrace_972365 : CollatzResearch.WordTrace tailWord_972365 prefixEnd_972365 499290616609193351165681 := by
  unfold tailWord_972365
  simp only [CollatzResearch.WordTrace]
  refine ⟨35465065122295146565862549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23643376748196764377241699 35465065122295146565862549)
  ·
    refine ⟨1662424927607584995274807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35465065122295146565862549 1662424927607584995274807)
    ·
      refine ⟨2493637391411377492912211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662424927607584995274807 2493637391411377492912211)
      ·
        refine ⟨3740456087117066239368317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493637391411377492912211 3740456087117066239368317)
        ·
          refine ⟨1402671032668899839763119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3740456087117066239368317 1402671032668899839763119)
          ·
            refine ⟨2104006549003349759644679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402671032668899839763119 2104006549003349759644679)
            ·
              refine ⟨3156009823505024639467019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104006549003349759644679 3156009823505024639467019)
              ·
                refine ⟨4734014735257536959200529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156009823505024639467019 4734014735257536959200529)
                ·
                  refine ⟨3550511051443152719400397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734014735257536959200529 3550511051443152719400397)
                  ·
                    refine ⟨1331441644291182269775149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550511051443152719400397 1331441644291182269775149)
                    ·
                      refine ⟨499290616609193351165681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1331441644291182269775149 499290616609193351165681)
                      ·
                        rfl

theorem cell23_972365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_972365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972365 prefixEnd_972365 := by exact prefixLift 972365
  have htrace : WordTrace (prefixWord ++ tailWord_972365) baseStart_972365 baseEnd_972365 := by
    simpa [prefixWord, tailWord_972365, baseEnd_972365] using wordTrace_append hprefix tailTrace_972365
  have hstable : (prefixWord ++ tailWord_972365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972365).length < 2 ^ (prefixWord ++ tailWord_972365).sum := by decide
  have hdescent : baseEnd_972365 < baseStart_972365 := by decide
  rcases family_descends (prefixWord ++ tailWord_972365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972388 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_972388 : Nat := 118140960795 + 972388 * 2 ^ 59
def prefixEnd_972388 : Nat := 4983230072969 + 3 ^ 40 * 972388 * 2
def baseEnd_972388 : Nat := 499302426664246761178075

theorem tailTrace_972388 : CollatzResearch.WordTrace tailWord_972388 prefixEnd_972388 499302426664246761178075 := by
  unfold tailWord_972388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17732952000605910746974909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23643936000807880995966545 17732952000605910746974909)
  ·
    refine ⟨6649857000227216530115591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17732952000605910746974909 6649857000227216530115591)
    ·
      refine ⟨9974785500340824795173387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6649857000227216530115591 9974785500340824795173387)
      ·
        refine ⟨14962178250511237192760081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9974785500340824795173387 14962178250511237192760081)
        ·
          refine ⟨11221633687883427894570061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14962178250511237192760081 11221633687883427894570061)
          ·
            refine ⟨4208112632956285460463773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11221633687883427894570061 4208112632956285460463773)
            ·
              refine ⟨1578042237358607047673915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4208112632956285460463773 1578042237358607047673915)
              ·
                refine ⟨2367063356037910571510873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578042237358607047673915 2367063356037910571510873)
                ·
                  refine ⟨1775297517028432928633155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367063356037910571510873 1775297517028432928633155)
                  ·
                    refine ⟨2662946275542649392949733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1775297517028432928633155 2662946275542649392949733)
                    ·
                      refine ⟨499302426664246761178075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2662946275542649392949733 499302426664246761178075)
                      ·
                        rfl

theorem cell23_972388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_972388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972388 prefixEnd_972388 := by exact prefixLift 972388
  have htrace : WordTrace (prefixWord ++ tailWord_972388) baseStart_972388 baseEnd_972388 := by
    simpa [prefixWord, tailWord_972388, baseEnd_972388] using wordTrace_append hprefix tailTrace_972388
  have hstable : (prefixWord ++ tailWord_972388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972388).length < 2 ^ (prefixWord ++ tailWord_972388).sum := by decide
  have hdescent : baseEnd_972388 < baseStart_972388 := by decide
  rcases family_descends (prefixWord ++ tailWord_972388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972405 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_972405 : Nat := 118140960795 + 972405 * 2 ^ 59
def prefixEnd_972405 : Nat := 4983230072969 + 3 ^ 40 * 972405 * 2
def baseEnd_972405 : Nat := 499311155835373194665497

theorem tailTrace_972405 : CollatzResearch.WordTrace tailWord_972405 prefixEnd_972405 499311155835373194665497 := by
  unfold tailWord_972405
  simp only [CollatzResearch.WordTrace]
  refine ⟨35466524042150233397318669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23644349361433488931545779 35466524042150233397318669)
  ·
    refine ⟨13299946515806337523994501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35466524042150233397318669 13299946515806337523994501)
    ·
      refine ⟨2493739971713688285748969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13299946515806337523994501 2493739971713688285748969)
      ·
        refine ⟨1870304978785266214311727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2493739971713688285748969 1870304978785266214311727)
        ·
          refine ⟨2805457468177899321467591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870304978785266214311727 2805457468177899321467591)
          ·
            refine ⟨4208186202266848982201387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805457468177899321467591 4208186202266848982201387)
            ·
              refine ⟨6312279303400273473302081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208186202266848982201387 6312279303400273473302081)
              ·
                refine ⟨4734209477550205104976561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6312279303400273473302081 4734209477550205104976561)
                ·
                  refine ⟨3550657108162653828732421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734209477550205104976561 3550657108162653828732421)
                  ·
                    refine ⟨665748207780497592887329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3550657108162653828732421 665748207780497592887329)
                    ·
                      refine ⟨499311155835373194665497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665748207780497592887329 499311155835373194665497)
                      ·
                        rfl

theorem cell23_972405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_972405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972405 prefixEnd_972405 := by exact prefixLift 972405
  have htrace : WordTrace (prefixWord ++ tailWord_972405) baseStart_972405 baseEnd_972405 := by
    simpa [prefixWord, tailWord_972405, baseEnd_972405] using wordTrace_append hprefix tailTrace_972405
  have hstable : (prefixWord ++ tailWord_972405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972405).length < 2 ^ (prefixWord ++ tailWord_972405).sum := by decide
  have hdescent : baseEnd_972405 < baseStart_972405 := by decide
  rcases family_descends (prefixWord ++ tailWord_972405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972428 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 6]
def baseStart_972428 : Nat := 118140960795 + 972428 * 2 ^ 59
def prefixEnd_972428 : Nat := 4983230072969 + 3 ^ 40 * 972428 * 2
def baseEnd_972428 : Nat := 55480329543380733853099

theorem tailTrace_972428 : CollatzResearch.WordTrace tailWord_972428 prefixEnd_972428 55480329543380733853099 := by
  unfold tailWord_972428
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733681460533454162702969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23644908614044605550270625 17733681460533454162702969)
  ·
    refine ⟨13300261095400090622027227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17733681460533454162702969 13300261095400090622027227)
    ·
      refine ⟨19950391643100135933040841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13300261095400090622027227 19950391643100135933040841)
      ·
        refine ⟨14962793732325101949780631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19950391643100135933040841 14962793732325101949780631)
        ·
          refine ⟨22444190598487652924670947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14962793732325101949780631 22444190598487652924670947)
          ·
            refine ⟨33666285897731479387006421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22444190598487652924670947 33666285897731479387006421)
            ·
              refine ⟨789053575728081548132963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33666285897731479387006421 789053575728081548132963)
              ·
                refine ⟨1183580363592122322199445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789053575728081548132963 1183580363592122322199445)
                ·
                  refine ⟨55480329543380733853099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1183580363592122322199445 55480329543380733853099)
                  ·
                    rfl

theorem cell23_972428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_972428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972428 prefixEnd_972428 := by exact prefixLift 972428
  have htrace : WordTrace (prefixWord ++ tailWord_972428) baseStart_972428 baseEnd_972428 := by
    simpa [prefixWord, tailWord_972428, baseEnd_972428] using wordTrace_append hprefix tailTrace_972428
  have hstable : (prefixWord ++ tailWord_972428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972428).length < 2 ^ (prefixWord ++ tailWord_972428).sum := by decide
  have hdescent : baseEnd_972428 < baseStart_972428 := by decide
  rcases family_descends (prefixWord ++ tailWord_972428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972491 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4]
def baseStart_972491 : Nat := 118140960795 + 972491 * 2 ^ 59
def prefixEnd_972491 : Nat := 4983230072969 + 3 ^ 40 * 972491 * 2
def baseEnd_972491 : Nat := 499355315171659858190101

theorem tailTrace_972491 : CollatzResearch.WordTrace tailWord_972491 prefixEnd_972491 499355315171659858190101 := by
  unfold tailWord_972491
  simp only [CollatzResearch.WordTrace]
  refine ⟨35469660719838670084949327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23646440479892446723299551 35469660719838670084949327)
  ·
    refine ⟨53204491079758005127423991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35469660719838670084949327 53204491079758005127423991)
    ·
      refine ⟨79806736619637007691135987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53204491079758005127423991 79806736619637007691135987)
      ·
        refine ⟨119710104929455511536703981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79806736619637007691135987 119710104929455511536703981)
        ·
          refine ⟨44891289348545816826263993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119710104929455511536703981 44891289348545816826263993)
          ·
            refine ⟨33668467011409362619697995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44891289348545816826263993 33668467011409362619697995)
            ·
              refine ⟨50502700517114043929546993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33668467011409362619697995 50502700517114043929546993)
              ·
                refine ⟨37877025387835532947160245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50502700517114043929546993 37877025387835532947160245)
                ·
                  refine ⟨3550971130109581213796273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37877025387835532947160245 3550971130109581213796273)
                  ·
                    refine ⟨2663228347582185910347205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550971130109581213796273 2663228347582185910347205)
                    ·
                      refine ⟨499355315171659858190101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2663228347582185910347205 499355315171659858190101)
                      ·
                        rfl

theorem cell23_972491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_972491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972491 prefixEnd_972491 := by exact prefixLift 972491
  have htrace : WordTrace (prefixWord ++ tailWord_972491) baseStart_972491 baseEnd_972491 := by
    simpa [prefixWord, tailWord_972491, baseEnd_972491] using wordTrace_append hprefix tailTrace_972491
  have hstable : (prefixWord ++ tailWord_972491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972491).length < 2 ^ (prefixWord ++ tailWord_972491).sum := by decide
  have hdescent : baseEnd_972491 < baseStart_972491 := by decide
  rcases family_descends (prefixWord ++ tailWord_972491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972492 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_972492 : Nat := 118140960795 + 972492 * 2 ^ 59
def prefixEnd_972492 : Nat := 4983230072969 + 3 ^ 40 * 972492 * 2
def baseEnd_972492 : Nat := 166451942884104784759199

theorem tailTrace_972492 : CollatzResearch.WordTrace tailWord_972492 prefixEnd_972492 166451942884104784759199 := by
  unfold tailWord_972492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17734848596417523627867865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23646464795223364837157153 17734848596417523627867865)
  ·
    refine ⟨13301136447313142720900899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17734848596417523627867865 13301136447313142720900899)
    ·
      refine ⟨19951704670969714081351349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13301136447313142720900899 19951704670969714081351349)
      ·
        refine ⟨1870472312903410695126689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19951704670969714081351349 1870472312903410695126689)
        ·
          refine ⟨1402854234677558021345017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870472312903410695126689 1402854234677558021345017)
          ·
            refine ⟨1052140676008168516008763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402854234677558021345017 1052140676008168516008763)
            ·
              refine ⟨1578211014012252774013145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052140676008168516008763 1578211014012252774013145)
              ·
                refine ⟨1183658260509189580509859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578211014012252774013145 1183658260509189580509859)
                ·
                  refine ⟨1775487390763784370764789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183658260509189580509859 1775487390763784370764789)
                  ·
                    refine ⟨166451942884104784759199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1775487390763784370764789 166451942884104784759199)
                    ·
                      rfl

theorem cell23_972492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_972492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972492 prefixEnd_972492 := by exact prefixLift 972492
  have htrace : WordTrace (prefixWord ++ tailWord_972492) baseStart_972492 baseEnd_972492 := by
    simpa [prefixWord, tailWord_972492, baseEnd_972492] using wordTrace_append hprefix tailTrace_972492
  have hstable : (prefixWord ++ tailWord_972492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972492).length < 2 ^ (prefixWord ++ tailWord_972492).sum := by decide
  have hdescent : baseEnd_972492 < baseStart_972492 := by decide
  rcases family_descends (prefixWord ++ tailWord_972492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972495 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 3, 2, 2]
def baseStart_972495 : Nat := 118140960795 + 972495 * 2 ^ 59
def prefixEnd_972495 : Nat := 4983230072969 + 3 ^ 40 * 972495 * 2
def baseEnd_972495 : Nat := 499357369094277842540083

theorem tailTrace_972495 : CollatzResearch.WordTrace tailWord_972495 prefixEnd_972495 499357369094277842540083 := by
  unfold tailWord_972495
  simp only [CollatzResearch.WordTrace]
  refine ⟨35469806611824178768094939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23646537741216119178729959 35469806611824178768094939)
  ·
    refine ⟨53204709917736268152142409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35469806611824178768094939 53204709917736268152142409)
    ·
      refine ⟨39903532438302201114106807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53204709917736268152142409 39903532438302201114106807)
      ·
        refine ⟨59855298657453301671160211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39903532438302201114106807 59855298657453301671160211)
        ·
          refine ⟨89782947986179952506740317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59855298657453301671160211 89782947986179952506740317)
          ·
            refine ⟨33668605494817482190027619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89782947986179952506740317 33668605494817482190027619)
            ·
              refine ⟨50502908242226223285041429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33668605494817482190027619 50502908242226223285041429)
              ·
                refine ⟨2367323823854354216486317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50502908242226223285041429 2367323823854354216486317)
                ·
                  refine ⟨887746433945382831182369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2367323823854354216486317 887746433945382831182369)
                  ·
                    refine ⟨665809825459037123386777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 887746433945382831182369 665809825459037123386777)
                    ·
                      refine ⟨499357369094277842540083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665809825459037123386777 499357369094277842540083)
                      ·
                        rfl

theorem cell23_972495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 2, 2].length) (baseStart_972495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972495 prefixEnd_972495 := by exact prefixLift 972495
  have htrace : WordTrace (prefixWord ++ tailWord_972495) baseStart_972495 baseEnd_972495 := by
    simpa [prefixWord, tailWord_972495, baseEnd_972495] using wordTrace_append hprefix tailTrace_972495
  have hstable : (prefixWord ++ tailWord_972495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972495).length < 2 ^ (prefixWord ++ tailWord_972495).sum := by decide
  have hdescent : baseEnd_972495 < baseStart_972495 := by decide
  rcases family_descends (prefixWord ++ tailWord_972495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972509 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_972509 : Nat := 118140960795 + 972509 * 2 ^ 59
def prefixEnd_972509 : Nat := 4983230072969 + 3 ^ 40 * 972509 * 2
def baseEnd_972509 : Nat := 166454852607813595921673

theorem tailTrace_972509 : CollatzResearch.WordTrace tailWord_972509 prefixEnd_972509 166454852607813595921673 := by
  unfold tailWord_972509
  simp only [CollatzResearch.WordTrace]
  refine ⟨35470317233773459159104581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23646878155848972772736387 35470317233773459159104581)
  ·
    refine ⟨6650684481332523592332109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35470317233773459159104581 6650684481332523592332109)
    ·
      refine ⟨2494006680499696347124541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6650684481332523592332109 2494006680499696347124541)
      ·
        refine ⟨935252505187386130171703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2494006680499696347124541 935252505187386130171703)
        ·
          refine ⟨1402878757781079195257555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935252505187386130171703 1402878757781079195257555)
          ·
            refine ⟨2104318136671618792886333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402878757781079195257555 2104318136671618792886333)
            ·
              refine ⟨789119301251857047332375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2104318136671618792886333 789119301251857047332375)
              ·
                refine ⟨1183678951877785570998563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789119301251857047332375 1183678951877785570998563)
                ·
                  refine ⟨1775518427816678356497845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183678951877785570998563 1775518427816678356497845)
                  ·
                    refine ⟨166454852607813595921673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1775518427816678356497845 166454852607813595921673)
                    ·
                      rfl

theorem cell23_972509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_972509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972509 prefixEnd_972509 := by exact prefixLift 972509
  have htrace : WordTrace (prefixWord ++ tailWord_972509) baseStart_972509 baseEnd_972509 := by
    simpa [prefixWord, tailWord_972509, baseEnd_972509] using wordTrace_append hprefix tailTrace_972509
  have hstable : (prefixWord ++ tailWord_972509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972509).length < 2 ^ (prefixWord ++ tailWord_972509).sum := by decide
  have hdescent : baseEnd_972509 < baseStart_972509 := by decide
  rcases family_descends (prefixWord ++ tailWord_972509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972529 : List Nat := [1, 2, 2, 2, 2, 4, 1, 4, 1, 2, 2]
def baseStart_972529 : Nat := 118140960795 + 972529 * 2 ^ 59
def prefixEnd_972529 : Nat := 4983230072969 + 3 ^ 40 * 972529 * 2
def baseEnd_972529 : Nat := 499374827436530709514927

theorem tailTrace_972529 : CollatzResearch.WordTrace tailWord_972529 prefixEnd_972529 499374827436530709514927 := by
  unfold tailWord_972529
  simp only [CollatzResearch.WordTrace]
  refine ⟨35471046693701002574832641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23647364462467335049888427 35471046693701002574832641)
  ·
    refine ⟨26603285020275751931124481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35471046693701002574832641 26603285020275751931124481)
    ·
      refine ⟨19952463765206813948343361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26603285020275751931124481 19952463765206813948343361)
      ·
        refine ⟨14964347823905110461257521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19952463765206813948343361 14964347823905110461257521)
        ·
          refine ⟨11223260867928832845943141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14964347823905110461257521 11223260867928832845943141)
          ·
            refine ⟨2104361412736656158614339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11223260867928832845943141 2104361412736656158614339)
            ·
              refine ⟨3156542119104984237921509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104361412736656158614339 3156542119104984237921509)
              ·
                refine ⟨591851647332184544610283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3156542119104984237921509 591851647332184544610283)
                ·
                  refine ⟨887777470998276816915425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591851647332184544610283 887777470998276816915425)
                  ·
                    refine ⟨665833103248707612686569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 887777470998276816915425 665833103248707612686569)
                    ·
                      refine ⟨499374827436530709514927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665833103248707612686569 499374827436530709514927)
                      ·
                        rfl

theorem cell23_972529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_972529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972529 prefixEnd_972529 := by exact prefixLift 972529
  have htrace : WordTrace (prefixWord ++ tailWord_972529) baseStart_972529 baseEnd_972529 := by
    simpa [prefixWord, tailWord_972529, baseEnd_972529] using wordTrace_append hprefix tailTrace_972529
  have hstable : (prefixWord ++ tailWord_972529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972529).length < 2 ^ (prefixWord ++ tailWord_972529).sum := by decide
  have hdescent : baseEnd_972529 < baseStart_972529 := by decide
  rcases family_descends (prefixWord ++ tailWord_972529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972531 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 2, 7]
def baseStart_972531 : Nat := 118140960795 + 972531 * 2 ^ 59
def prefixEnd_972531 : Nat := 4983230072969 + 3 ^ 40 * 972531 * 2
def baseEnd_972531 : Nat := 166458618132613233896639

theorem tailTrace_972531 : CollatzResearch.WordTrace tailWord_972531 prefixEnd_972531 166458618132613233896639 := by
  unfold tailWord_972531
  simp only [CollatzResearch.WordTrace]
  refine ⟨35471119639693756916405447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23647413093129171277603631 35471119639693756916405447)
  ·
    refine ⟨53206679459540635374608171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35471119639693756916405447 53206679459540635374608171)
    ·
      refine ⟨79810019189310953061912257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53206679459540635374608171 79810019189310953061912257)
      ·
        refine ⟨59857514391983214796434193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79810019189310953061912257 59857514391983214796434193)
        ·
          refine ⟨44893135793987411097325645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59857514391983214796434193 44893135793987411097325645)
          ·
            refine ⟨16834925922745279161497117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44893135793987411097325645 16834925922745279161497117)
            ·
              refine ⟨6313097221029479685561419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16834925922745279161497117 6313097221029479685561419)
              ·
                refine ⟨9469645831544219528342129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6313097221029479685561419 9469645831544219528342129)
                ·
                  refine ⟨7102234373658164646256597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9469645831544219528342129 7102234373658164646256597)
                  ·
                    refine ⟨166458618132613233896639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7102234373658164646256597 166458618132613233896639)
                    ·
                      rfl

theorem cell23_972531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 7].length) (baseStart_972531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972531 prefixEnd_972531 := by exact prefixLift 972531
  have htrace : WordTrace (prefixWord ++ tailWord_972531) baseStart_972531 baseEnd_972531 := by
    simpa [prefixWord, tailWord_972531, baseEnd_972531] using wordTrace_append hprefix tailTrace_972531
  have hstable : (prefixWord ++ tailWord_972531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972531).length < 2 ^ (prefixWord ++ tailWord_972531).sum := by decide
  have hdescent : baseEnd_972531 < baseStart_972531 := by decide
  rcases family_descends (prefixWord ++ tailWord_972531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972542 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_972542 : Nat := 118140960795 + 972542 * 2 ^ 59
def prefixEnd_972542 : Nat := 4983230072969 + 3 ^ 40 * 972542 * 2
def baseEnd_972542 : Nat := 499381502685039158652367

theorem tailTrace_972542 : CollatzResearch.WordTrace tailWord_972542 prefixEnd_972542 499381502685039158652367 := by
  unfold tailWord_972542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433940105331738224381985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23647680561769270530037253 4433940105331738224381985)
  ·
    refine ⟨3325455078998803668286489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4433940105331738224381985 3325455078998803668286489)
    ·
      refine ⟨2494091309249102751214867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3325455078998803668286489 2494091309249102751214867)
      ·
        refine ⟨3741136963873654126822301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494091309249102751214867 3741136963873654126822301)
        ·
          refine ⟨1402926361452620297558363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3741136963873654126822301 1402926361452620297558363)
          ·
            refine ⟨2104389542178930446337545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402926361452620297558363 2104389542178930446337545)
            ·
              refine ⟨1578292156634197834753159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104389542178930446337545 1578292156634197834753159)
              ·
                refine ⟨2367438234951296752129739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578292156634197834753159 2367438234951296752129739)
                ·
                  refine ⟨3551157352426945128194609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367438234951296752129739 3551157352426945128194609)
                  ·
                    refine ⟨2663368014320208846145957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3551157352426945128194609 2663368014320208846145957)
                    ·
                      refine ⟨499381502685039158652367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2663368014320208846145957 499381502685039158652367)
                      ·
                        rfl

theorem cell23_972542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_972542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972542 prefixEnd_972542 := by exact prefixLift 972542
  have htrace : WordTrace (prefixWord ++ tailWord_972542) baseStart_972542 baseEnd_972542 := by
    simpa [prefixWord, tailWord_972542, baseEnd_972542] using wordTrace_append hprefix tailTrace_972542
  have hstable : (prefixWord ++ tailWord_972542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972542).length < 2 ^ (prefixWord ++ tailWord_972542).sum := by decide
  have hdescent : baseEnd_972542 < baseStart_972542 := by decide
  rcases family_descends (prefixWord ++ tailWord_972542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972555 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 3, 3, 2]
def baseStart_972555 : Nat := 118140960795 + 972555 * 2 ^ 59
def prefixEnd_972555 : Nat := 4983230072969 + 3 ^ 40 * 972555 * 2
def baseEnd_972555 : Nat := 499388177933547607789807

theorem tailTrace_972555 : CollatzResearch.WordTrace tailWord_972555 prefixEnd_972555 499388177933547607789807 := by
  unfold tailWord_972555
  simp only [CollatzResearch.WordTrace]
  refine ⟨35471994991606809015279119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23647996661071206010186079 35471994991606809015279119)
  ·
    refine ⟨53207992487410213522918679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35471994991606809015279119 53207992487410213522918679)
    ·
      refine ⟨79811988731115320284378019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53207992487410213522918679 79811988731115320284378019)
      ·
        refine ⟨119717983096672980426567029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79811988731115320284378019 119717983096672980426567029)
        ·
          refine ⟨11223560915313091914990659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119717983096672980426567029 11223560915313091914990659)
          ·
            refine ⟨16835341372969637872485989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223560915313091914990659 16835341372969637872485989)
            ·
              refine ⟨3156626507431807101091123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16835341372969637872485989 3156626507431807101091123)
              ·
                refine ⟨4734939761147710651636685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156626507431807101091123 4734939761147710651636685)
                ·
                  refine ⟨1775602410430391494363757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4734939761147710651636685 1775602410430391494363757)
                  ·
                    refine ⟨665850903911396810386409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775602410430391494363757 665850903911396810386409)
                    ·
                      refine ⟨499388177933547607789807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665850903911396810386409 499388177933547607789807)
                      ·
                        rfl

theorem cell23_972555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3, 2].length) (baseStart_972555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972555 prefixEnd_972555 := by exact prefixLift 972555
  have htrace : WordTrace (prefixWord ++ tailWord_972555) baseStart_972555 baseEnd_972555 := by
    simpa [prefixWord, tailWord_972555, baseEnd_972555] using wordTrace_append hprefix tailTrace_972555
  have hstable : (prefixWord ++ tailWord_972555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972555).length < 2 ^ (prefixWord ++ tailWord_972555).sum := by decide
  have hdescent : baseEnd_972555 < baseStart_972555 := by decide
  rcases family_descends (prefixWord ++ tailWord_972555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972561 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 3, 8]
def baseStart_972561 : Nat := 118140960795 + 972561 * 2 ^ 59
def prefixEnd_972561 : Nat := 4983230072969 + 3 ^ 40 * 972561 * 2
def baseEnd_972561 : Nat := 166463752939158194771593

theorem tailTrace_972561 : CollatzResearch.WordTrace tailWord_972561 prefixEnd_972561 166463752939158194771593 := by
  unfold tailWord_972561
  simp only [CollatzResearch.WordTrace]
  refine ⟨35472213829585072039997537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23648142553056714693331691 35472213829585072039997537)
  ·
    refine ⟨26604160372188804029998153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35472213829585072039997537 26604160372188804029998153)
    ·
      refine ⟨19953120279141603022498615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26604160372188804029998153 19953120279141603022498615)
      ·
        refine ⟨29929680418712404533747923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19953120279141603022498615 29929680418712404533747923)
        ·
          refine ⟨44894520628068606800621885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29929680418712404533747923 44894520628068606800621885)
          ·
            refine ⟨16835445235525727550233207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44894520628068606800621885 16835445235525727550233207)
            ·
              refine ⟨25253167853288591325349811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16835445235525727550233207 25253167853288591325349811)
              ·
                refine ⟨37879751779932886988024717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25253167853288591325349811 37879751779932886988024717)
                ·
                  refine ⟨14204906917474832620509269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37879751779932886988024717 14204906917474832620509269)
                  ·
                    refine ⟨166463752939158194771593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14204906917474832620509269 166463752939158194771593)
                    ·
                      rfl

theorem cell23_972561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_972561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972561 prefixEnd_972561 := by exact prefixLift 972561
  have htrace : WordTrace (prefixWord ++ tailWord_972561) baseStart_972561 baseEnd_972561 := by
    simpa [prefixWord, tailWord_972561, baseEnd_972561] using wordTrace_append hprefix tailTrace_972561
  have hstable : (prefixWord ++ tailWord_972561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972561).length < 2 ^ (prefixWord ++ tailWord_972561).sum := by decide
  have hdescent : baseEnd_972561 < baseStart_972561 := by decide
  rcases family_descends (prefixWord ++ tailWord_972561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972562 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_972562 : Nat := 118140960795 + 972562 * 2 ^ 59
def prefixEnd_972562 : Nat := 4983230072969 + 3 ^ 40 * 972562 * 2
def baseEnd_972562 : Nat := 499391772298129080402275

theorem tailTrace_972562 : CollatzResearch.WordTrace tailWord_972562 prefixEnd_972562 499391772298129080402275 := by
  unfold tailWord_972562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868062575645362302695985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23648166868387632807189293 8868062575645362302695985)
  ·
    refine ⟨6651046931734021727021989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8868062575645362302695985 6651046931734021727021989)
    ·
      refine ⟨1247071299700129073816623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6651046931734021727021989 1247071299700129073816623)
      ·
        refine ⟨1870606949550193610724935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247071299700129073816623 1870606949550193610724935)
        ·
          refine ⟨2805910424325290416087403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870606949550193610724935 2805910424325290416087403)
          ·
            refine ⟨4208865636487935624131105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805910424325290416087403 4208865636487935624131105)
            ·
              refine ⟨3156649227365951718098329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4208865636487935624131105 3156649227365951718098329)
              ·
                refine ⟨2367486920524463788573747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156649227365951718098329 2367486920524463788573747)
                ·
                  refine ⟨3551230380786695682860621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367486920524463788573747 3551230380786695682860621)
                  ·
                    refine ⟨1331711392795010881072733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551230380786695682860621 1331711392795010881072733)
                    ·
                      refine ⟨499391772298129080402275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1331711392795010881072733 499391772298129080402275)
                      ·
                        rfl

theorem cell23_972562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_972562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972562 prefixEnd_972562 := by exact prefixLift 972562
  have htrace : WordTrace (prefixWord ++ tailWord_972562) baseStart_972562 baseEnd_972562 := by
    simpa [prefixWord, tailWord_972562, baseEnd_972562] using wordTrace_append hprefix tailTrace_972562
  have hstable : (prefixWord ++ tailWord_972562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972562).length < 2 ^ (prefixWord ++ tailWord_972562).sum := by decide
  have hdescent : baseEnd_972562 < baseStart_972562 := by decide
  rcases family_descends (prefixWord ++ tailWord_972562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972572 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_972572 : Nat := 118140960795 + 972572 * 2 ^ 59
def prefixEnd_972572 : Nat := 4983230072969 + 3 ^ 40 * 972572 * 2
def baseEnd_972572 : Nat := 499396907104674041277229

theorem tailTrace_972572 : CollatzResearch.WordTrace tailWord_972572 prefixEnd_972572 499396907104674041277229 := by
  unfold tailWord_972572
  simp only [CollatzResearch.WordTrace]
  refine ⟨17736307516272610459323985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23648410021696813945765313 17736307516272610459323985)
  ·
    refine ⟨13302230637204457844492989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17736307516272610459323985 13302230637204457844492989)
    ·
      refine ⟨4988336488951671691684871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13302230637204457844492989 4988336488951671691684871)
      ·
        refine ⟨7482504733427507537527307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988336488951671691684871 7482504733427507537527307)
        ·
          refine ⟨11223757100141261306290961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482504733427507537527307 11223757100141261306290961)
          ·
            refine ⟨8417817825105945979718221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11223757100141261306290961 8417817825105945979718221)
            ·
              refine ⟨3156681684414729742394333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8417817825105945979718221 3156681684414729742394333)
              ·
                refine ⟨1183755631655523653397875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3156681684414729742394333 1183755631655523653397875)
                ·
                  refine ⟨1775633447483285480096813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183755631655523653397875 1775633447483285480096813)
                  ·
                    refine ⟨665862542806232055036305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775633447483285480096813 665862542806232055036305)
                    ·
                      refine ⟨499396907104674041277229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665862542806232055036305 499396907104674041277229)
                      ·
                        rfl

theorem cell23_972572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_972572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972572 prefixEnd_972572 := by exact prefixLift 972572
  have htrace : WordTrace (prefixWord ++ tailWord_972572) baseStart_972572 baseEnd_972572 := by
    simpa [prefixWord, tailWord_972572, baseEnd_972572] using wordTrace_append hprefix tailTrace_972572
  have hstable : (prefixWord ++ tailWord_972572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972572).length < 2 ^ (prefixWord ++ tailWord_972572).sum := by decide
  have hdescent : baseEnd_972572 < baseStart_972572 := by decide
  rcases family_descends (prefixWord ++ tailWord_972572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972578 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_972578 : Nat := 118140960795 + 972578 * 2 ^ 59
def prefixEnd_972578 : Nat := 4983230072969 + 3 ^ 40 * 972578 * 2
def baseEnd_972578 : Nat := 166466662662867005934067

theorem tailTrace_972578 : CollatzResearch.WordTrace tailWord_972578 prefixEnd_972578 166466662662867005934067 := by
  unfold tailWord_972578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868208467630870985841597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23648555913682322628910925 8868208467630870985841597)
  ·
    refine ⟨3325578175361576619690599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8868208467630870985841597 3325578175361576619690599)
    ·
      refine ⟨4988367263042364929535899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3325578175361576619690599 4988367263042364929535899)
      ·
        refine ⟨7482550894563547394303849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988367263042364929535899 7482550894563547394303849)
        ·
          refine ⟨5611913170922660545727887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7482550894563547394303849 5611913170922660545727887)
          ·
            refine ⟨8417869756383990818591831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611913170922660545727887 8417869756383990818591831)
            ·
              refine ⟨12626804634575986227887747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8417869756383990818591831 12626804634575986227887747)
              ·
                refine ⟨18940206951863979341831621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12626804634575986227887747 18940206951863979341831621)
                ·
                  refine ⟨3551288803474496126593429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18940206951863979341831621 3551288803474496126593429)
                  ·
                    refine ⟨166466662662867005934067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3551288803474496126593429 166466662662867005934067)
                    ·
                      rfl

theorem cell23_972578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_972578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972578 prefixEnd_972578 := by exact prefixLift 972578
  have htrace : WordTrace (prefixWord ++ tailWord_972578) baseStart_972578 baseEnd_972578 := by
    simpa [prefixWord, tailWord_972578, baseEnd_972578] using wordTrace_append hprefix tailTrace_972578
  have hstable : (prefixWord ++ tailWord_972578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972578).length < 2 ^ (prefixWord ++ tailWord_972578).sum := by decide
  have hdescent : baseEnd_972578 < baseStart_972578 := by decide
  rcases family_descends (prefixWord ++ tailWord_972578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972591 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 11]
def baseStart_972591 : Nat := 118140960795 + 972591 * 2 ^ 59
def prefixEnd_972591 : Nat := 4983230072969 + 3 ^ 40 * 972591 * 2
def baseEnd_972591 : Nat := 55489629248567718548849

theorem tailTrace_972591 : CollatzResearch.WordTrace tailWord_972591 prefixEnd_972591 55489629248567718548849 := by
  unfold tailWord_972591
  simp only [CollatzResearch.WordTrace]
  refine ⟨35473308019476387163589627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23648872012984258109059751 35473308019476387163589627)
  ·
    refine ⟨53209962029214580745384441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35473308019476387163589627 53209962029214580745384441)
    ·
      refine ⟨39907471521910935559038331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53209962029214580745384441 39907471521910935559038331)
      ·
        refine ⟨59861207282866403338557497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39907471521910935559038331 59861207282866403338557497)
        ·
          refine ⟨44895905462149802503918123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59861207282866403338557497 44895905462149802503918123)
          ·
            refine ⟨67343858193224703755877185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44895905462149802503918123 67343858193224703755877185)
            ·
              refine ⟨50507893644918527816907889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67343858193224703755877185 50507893644918527816907889)
              ·
                refine ⟨37880920233688895862680917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50507893644918527816907889 37880920233688895862680917)
                ·
                  refine ⟨55489629248567718548849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 37880920233688895862680917 55489629248567718548849)
                  ·
                    rfl

theorem cell23_972591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 11].length) (baseStart_972591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972591 prefixEnd_972591 := by exact prefixLift 972591
  have htrace : WordTrace (prefixWord ++ tailWord_972591) baseStart_972591 baseEnd_972591 := by
    simpa [prefixWord, tailWord_972591, baseEnd_972591] using wordTrace_append hprefix tailTrace_972591
  have hstable : (prefixWord ++ tailWord_972591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972591).length < 2 ^ (prefixWord ++ tailWord_972591).sum := by decide
  have hdescent : baseEnd_972591 < baseStart_972591 := by decide
  rcases family_descends (prefixWord ++ tailWord_972591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972596 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_972596 : Nat := 118140960795 + 972596 * 2 ^ 59
def prefixEnd_972596 : Nat := 4983230072969 + 3 ^ 40 * 972596 * 2
def baseEnd_972596 : Nat := 499409230640381947377119

theorem tailTrace_972596 : CollatzResearch.WordTrace tailWord_972596 prefixEnd_972596 499409230640381947377119 := by
  unfold tailWord_972596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17736745192229136508760821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23648993589638848678347761 17736745192229136508760821)
  ·
    refine ⟨1662819861771481547696327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17736745192229136508760821 1662819861771481547696327)
    ·
      refine ⟨2494229792657222321544491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662819861771481547696327 2494229792657222321544491)
      ·
        refine ⟨3741344688985833482316737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494229792657222321544491 3741344688985833482316737)
        ·
          refine ⟨2806008516739375111737553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3741344688985833482316737 2806008516739375111737553)
          ·
            refine ⟨2104506387554531333803165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2806008516739375111737553 2104506387554531333803165)
            ·
              refine ⟨789189895332949250176187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2104506387554531333803165 789189895332949250176187)
              ·
                refine ⟨1183784842999423875264281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789189895332949250176187 1183784842999423875264281)
                ·
                  refine ⟨887838632249567906448211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1183784842999423875264281 887838632249567906448211)
                  ·
                    refine ⟨1331757948374351859672317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 887838632249567906448211 1331757948374351859672317)
                    ·
                      refine ⟨499409230640381947377119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1331757948374351859672317 499409230640381947377119)
                      ·
                        rfl

theorem cell23_972596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_972596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972596 prefixEnd_972596 := by exact prefixLift 972596
  have htrace : WordTrace (prefixWord ++ tailWord_972596) baseStart_972596 baseEnd_972596 := by
    simpa [prefixWord, tailWord_972596, baseEnd_972596] using wordTrace_append hprefix tailTrace_972596
  have hstable : (prefixWord ++ tailWord_972596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972596).length < 2 ^ (prefixWord ++ tailWord_972596).sum := by decide
  have hdescent : baseEnd_972596 < baseStart_972596 := by decide
  rcases family_descends (prefixWord ++ tailWord_972596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972602 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2]
def baseStart_972602 : Nat := 118140960795 + 972602 * 2 ^ 59
def prefixEnd_972602 : Nat := 4983230072969 + 3 ^ 40 * 972602 * 2
def baseEnd_972602 : Nat := 499412311524308923902091

theorem tailTrace_972602 : CollatzResearch.WordTrace tailWord_972602 prefixEnd_972602 499412311524308923902091 := by
  unfold tailWord_972602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868427305609134010560015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23649139481624357361493373 8868427305609134010560015)
  ·
    refine ⟨13302640958413701015840023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8868427305609134010560015 13302640958413701015840023)
    ·
      refine ⟨19953961437620551523760035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13302640958413701015840023 19953961437620551523760035)
      ·
        refine ⟨29930942156430827285640053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19953961437620551523760035 29930942156430827285640053)
        ·
          refine ⟨2806025827165390058028755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29930942156430827285640053 2806025827165390058028755)
          ·
            refine ⟨4209038740748085087043133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806025827165390058028755 4209038740748085087043133)
            ·
              refine ⟨1578389527780531907641175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4209038740748085087043133 1578389527780531907641175)
              ·
                refine ⟨2367584291670797861461763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578389527780531907641175 2367584291670797861461763)
                ·
                  refine ⟨3551376437506196792192645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367584291670797861461763 3551376437506196792192645)
                  ·
                    refine ⟨665883082032411898536121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551376437506196792192645 665883082032411898536121)
                    ·
                      refine ⟨499412311524308923902091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665883082032411898536121 499412311524308923902091)
                      ·
                        rfl

theorem cell23_972602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_972602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972602 prefixEnd_972602 := by exact prefixLift 972602
  have htrace : WordTrace (prefixWord ++ tailWord_972602) baseStart_972602 baseEnd_972602 := by
    simpa [prefixWord, tailWord_972602, baseEnd_972602] using wordTrace_append hprefix tailTrace_972602
  have hstable : (prefixWord ++ tailWord_972602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972602).length < 2 ^ (prefixWord ++ tailWord_972602).sum := by decide
  have hdescent : baseEnd_972602 < baseStart_972602 := by decide
  rcases family_descends (prefixWord ++ tailWord_972602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972642 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 7]
def baseStart_972642 : Nat := 118140960795 + 972642 * 2 ^ 59
def prefixEnd_972642 : Nat := 4983230072969 + 3 ^ 40 * 972642 * 2
def baseEnd_972642 : Nat := 55492538972276529711323

theorem tailTrace_972642 : CollatzResearch.WordTrace tailWord_972642 prefixEnd_972642 55492538972276529711323 := by
  unfold tailWord_972642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868792035572905718424045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23650112094861081915797453 8868792035572905718424045)
  ·
    refine ⟨3325797013339839644409017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8868792035572905718424045 3325797013339839644409017)
    ·
      refine ⟨2494347760004879733306763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3325797013339839644409017 2494347760004879733306763)
      ·
        refine ⟨3741521640007319599960145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494347760004879733306763 3741521640007319599960145)
        ·
          refine ⟨2806141230005489699970109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3741521640007319599960145 2806141230005489699970109)
          ·
            refine ⟨1052302961252058637488791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2806141230005489699970109 1052302961252058637488791)
            ·
              refine ⟨1578454441878087956233187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052302961252058637488791 1578454441878087956233187)
              ·
                refine ⟨2367681662817131934349781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578454441878087956233187 2367681662817131934349781)
                ·
                  refine ⟨55492538972276529711323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2367681662817131934349781 55492538972276529711323)
                  ·
                    rfl

theorem cell23_972642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_972642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972642 prefixEnd_972642 := by exact prefixLift 972642
  have htrace : WordTrace (prefixWord ++ tailWord_972642) baseStart_972642 baseEnd_972642 := by
    simpa [prefixWord, tailWord_972642, baseEnd_972642] using wordTrace_append hprefix tailTrace_972642
  have hstable : (prefixWord ++ tailWord_972642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972642).length < 2 ^ (prefixWord ++ tailWord_972642).sum := by decide
  have hdescent : baseEnd_972642 < baseStart_972642 := by decide
  rcases family_descends (prefixWord ++ tailWord_972642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972645 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 2, 5, 2]
def baseStart_972645 : Nat := 118140960795 + 972645 * 2 ^ 59
def prefixEnd_972645 : Nat := 4983230072969 + 3 ^ 40 * 972645 * 2
def baseEnd_972645 : Nat := 499434391192452255664393

theorem tailTrace_972645 : CollatzResearch.WordTrace tailWord_972645 prefixEnd_972645 499434391192452255664393 := by
  unfold tailWord_972645
  simp only [CollatzResearch.WordTrace]
  refine ⟨35475277561280754386055389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23650185040853836257370259 35475277561280754386055389)
  ·
    refine ⟨13303229085480282894770771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35475277561280754386055389 13303229085480282894770771)
    ·
      refine ⟨19954843628220424342156157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13303229085480282894770771 19954843628220424342156157)
      ·
        refine ⟨7483066360582659128308559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19954843628220424342156157 7483066360582659128308559)
        ·
          refine ⟨11224599540873988692462839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483066360582659128308559 11224599540873988692462839)
          ·
            refine ⟨16836899311310983038694259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11224599540873988692462839 16836899311310983038694259)
            ·
              refine ⟨25255348966966474558041389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16836899311310983038694259 25255348966966474558041389)
              ·
                refine ⟨9470755862612427959265521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25255348966966474558041389 9470755862612427959265521)
                ·
                  refine ⟨7103066896959320969449141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9470755862612427959265521 7103066896959320969449141)
                  ·
                    refine ⟨665912521589936340885857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7103066896959320969449141 665912521589936340885857)
                    ·
                      refine ⟨499434391192452255664393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665912521589936340885857 499434391192452255664393)
                      ·
                        rfl

theorem cell23_972645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_972645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972645 prefixEnd_972645 := by exact prefixLift 972645
  have htrace : WordTrace (prefixWord ++ tailWord_972645) baseStart_972645 baseEnd_972645 := by
    simpa [prefixWord, tailWord_972645, baseEnd_972645] using wordTrace_append hprefix tailTrace_972645
  have hstable : (prefixWord ++ tailWord_972645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972645).length < 2 ^ (prefixWord ++ tailWord_972645).sum := by decide
  have hdescent : baseEnd_972645 < baseStart_972645 := by decide
  rcases family_descends (prefixWord ++ tailWord_972645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972675 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 4]
def baseStart_972675 : Nat := 118140960795 + 972675 * 2 ^ 59
def prefixEnd_972675 : Nat := 4983230072969 + 3 ^ 40 * 972675 * 2
def baseEnd_972675 : Nat := 499449795612087138289255

theorem tailTrace_972675 : CollatzResearch.WordTrace tailWord_972675 prefixEnd_972675 499449795612087138289255 := by
  unfold tailWord_972675
  simp only [CollatzResearch.WordTrace]
  refine ⟨35476371751172069509647479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23650914500781379673098319 35476371751172069509647479)
  ·
    refine ⟨53214557626758104264471219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35476371751172069509647479 53214557626758104264471219)
    ·
      refine ⟨79821836440137156396706829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53214557626758104264471219 79821836440137156396706829)
      ·
        refine ⟨29933188665051433648765061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79821836440137156396706829 29933188665051433648765061)
        ·
          refine ⟨5612472874697143809143449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29933188665051433648765061 5612472874697143809143449)
          ·
            refine ⟨4209354656022857856857587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5612472874697143809143449 4209354656022857856857587)
            ·
              refine ⟨6314031984034286785286381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209354656022857856857587 6314031984034286785286381)
              ·
                refine ⟨2367761994012857544482393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6314031984034286785286381 2367761994012857544482393)
                ·
                  refine ⟨1775821495509643158361795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367761994012857544482393 1775821495509643158361795)
                  ·
                    refine ⟨2663732243264464737542693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1775821495509643158361795 2663732243264464737542693)
                    ·
                      refine ⟨499449795612087138289255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2663732243264464737542693 499449795612087138289255)
                      ·
                        rfl

theorem cell23_972675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_972675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972675 prefixEnd_972675 := by exact prefixLift 972675
  have htrace : WordTrace (prefixWord ++ tailWord_972675) baseStart_972675 baseEnd_972675 := by
    simpa [prefixWord, tailWord_972675, baseEnd_972675] using wordTrace_append hprefix tailTrace_972675
  have hstable : (prefixWord ++ tailWord_972675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972675).length < 2 ^ (prefixWord ++ tailWord_972675).sum := by decide
  have hdescent : baseEnd_972675 < baseStart_972675 := by decide
  rcases family_descends (prefixWord ++ tailWord_972675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972692 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_972692 : Nat := 118140960795 + 972692 * 2 ^ 59
def prefixEnd_972692 : Nat := 4983230072969 + 3 ^ 40 * 972692 * 2
def baseEnd_972692 : Nat := 499458524783213571776677

theorem tailTrace_972692 : CollatzResearch.WordTrace tailWord_972692 prefixEnd_972692 499458524783213571776677 := by
  unfold tailWord_972692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738495896055240706508165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23651327861406987608677553 17738495896055240706508165)
  ·
    refine ⟨3325967980510357632470281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17738495896055240706508165 3325967980510357632470281)
    ·
      refine ⟨2494475985382768224352711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3325967980510357632470281 2494475985382768224352711)
      ·
        refine ⟨3741713978074152336529067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494475985382768224352711 3741713978074152336529067)
        ·
          refine ⟨5612570967111228504793601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741713978074152336529067 5612570967111228504793601)
          ·
            refine ⟨4209428225333421378595201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5612570967111228504793601 4209428225333421378595201)
            ·
              refine ⟨3157071169000066033946401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209428225333421378595201 3157071169000066033946401)
              ·
                refine ⟨2367803376750049525459801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157071169000066033946401 2367803376750049525459801)
                ·
                  refine ⟨1775852532562537144094851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367803376750049525459801 1775852532562537144094851)
                  ·
                    refine ⟨2663778798843805716142277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1775852532562537144094851 2663778798843805716142277)
                    ·
                      refine ⟨499458524783213571776677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2663778798843805716142277 499458524783213571776677)
                      ·
                        rfl

theorem cell23_972692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_972692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972692 prefixEnd_972692 := by exact prefixLift 972692
  have htrace : WordTrace (prefixWord ++ tailWord_972692) baseStart_972692 baseEnd_972692 := by
    simpa [prefixWord, tailWord_972692, baseEnd_972692] using wordTrace_append hprefix tailTrace_972692
  have hstable : (prefixWord ++ tailWord_972692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972692).length < 2 ^ (prefixWord ++ tailWord_972692).sum := by decide
  have hdescent : baseEnd_972692 < baseStart_972692 := by decide
  rcases family_descends (prefixWord ++ tailWord_972692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972745 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 1, 5]
def baseStart_972745 : Nat := 118140960795 + 972745 * 2 ^ 59
def prefixEnd_972745 : Nat := 4983230072969 + 3 ^ 40 * 972745 * 2
def baseEnd_972745 : Nat := 166495246419300621471311

theorem tailTrace_972745 : CollatzResearch.WordTrace tailWord_972745 prefixEnd_972745 166495246419300621471311 := by
  unfold tailWord_972745
  simp only [CollatzResearch.WordTrace]
  refine ⟨35478924860918471464695689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23652616573945647643130459 35478924860918471464695689)
  ·
    refine ⟨26609193645688853598521767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35478924860918471464695689 26609193645688853598521767)
    ·
      refine ⟨39913790468533280397782651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26609193645688853598521767 39913790468533280397782651)
      ·
        refine ⟨59870685702799920596673977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39913790468533280397782651 59870685702799920596673977)
        ·
          refine ⟨44903014277099940447505483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59870685702799920596673977 44903014277099940447505483)
          ·
            refine ⟨67354521415649910671258225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44903014277099940447505483 67354521415649910671258225)
            ·
              refine ⟨50515891061737433003443669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67354521415649910671258225 50515891061737433003443669)
              ·
                refine ⟨1183966196759471086018211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50515891061737433003443669 1183966196759471086018211)
                ·
                  refine ⟨1775949295139206629027317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183966196759471086018211 1775949295139206629027317)
                  ·
                    refine ⟨166495246419300621471311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1775949295139206629027317 166495246419300621471311)
                    ·
                      rfl

theorem cell23_972745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_972745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972745 prefixEnd_972745 := by exact prefixLift 972745
  have htrace : WordTrace (prefixWord ++ tailWord_972745) baseStart_972745 baseEnd_972745 := by
    simpa [prefixWord, tailWord_972745, baseEnd_972745] using wordTrace_append hprefix tailTrace_972745
  have hstable : (prefixWord ++ tailWord_972745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972745).length < 2 ^ (prefixWord ++ tailWord_972745).sum := by decide
  have hdescent : baseEnd_972745 < baseStart_972745 := by decide
  rcases family_descends (prefixWord ++ tailWord_972745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972752 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 2, 3, 2]
def baseStart_972752 : Nat := 118140960795 + 972752 * 2 ^ 59
def prefixEnd_972752 : Nat := 4983230072969 + 3 ^ 40 * 972752 * 2
def baseEnd_972752 : Nat := 499489333622483337026401

theorem tailTrace_972752 : CollatzResearch.WordTrace tailWord_972752 prefixEnd_972752 499489333622483337026401 := by
  unfold tailWord_972752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17739590085946555830100255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23652786781262074440133673 17739590085946555830100255)
  ·
    refine ⟨26609385128919833745150383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17739590085946555830100255 26609385128919833745150383)
    ·
      refine ⟨39914077693379750617725575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26609385128919833745150383 39914077693379750617725575)
      ·
        refine ⟨59871116540069625926588363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39914077693379750617725575 59871116540069625926588363)
        ·
          refine ⟨89806674810104438889882545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59871116540069625926588363 89806674810104438889882545)
          ·
            refine ⟨67355006107578329167411909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89806674810104438889882545 67355006107578329167411909)
            ·
              refine ⟨12629063645170936718889733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67355006107578329167411909 12629063645170936718889733)
              ·
                refine ⟨2367949433469550634791825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12629063645170936718889733 2367949433469550634791825)
                ·
                  refine ⟨1775962075102162976093869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367949433469550634791825 1775962075102162976093869)
                  ·
                    refine ⟨665985778163311116035201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775962075102162976093869 665985778163311116035201)
                    ·
                      refine ⟨499489333622483337026401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 665985778163311116035201 499489333622483337026401)
                      ·
                        rfl

theorem cell23_972752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 3, 2].length) (baseStart_972752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972752 prefixEnd_972752 := by exact prefixLift 972752
  have htrace : WordTrace (prefixWord ++ tailWord_972752) baseStart_972752 baseEnd_972752 := by
    simpa [prefixWord, tailWord_972752, baseEnd_972752] using wordTrace_append hprefix tailTrace_972752
  have hstable : (prefixWord ++ tailWord_972752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972752).length < 2 ^ (prefixWord ++ tailWord_972752).sum := by decide
  have hdescent : baseEnd_972752 < baseStart_972752 := by decide
  rcases family_descends (prefixWord ++ tailWord_972752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972759 : List Nat := [1, 1, 3, 2, 1, 1, 3, 6, 1, 1, 3]
def baseStart_972759 : Nat := 118140960795 + 972759 * 2 ^ 59
def prefixEnd_972759 : Nat := 4983230072969 + 3 ^ 40 * 972759 * 2
def baseEnd_972759 : Nat := 499492927987064809638869

theorem tailTrace_972759 : CollatzResearch.WordTrace tailWord_972759 prefixEnd_972759 499492927987064809638869 := by
  unfold tailWord_972759
  simp only [CollatzResearch.WordTrace]
  refine ⟨35479435482867751855705331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23652956988578501237136887 35479435482867751855705331)
  ·
    refine ⟨53219153224301627783557997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35479435482867751855705331 53219153224301627783557997)
    ·
      refine ⟨19957182459113110418834249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53219153224301627783557997 19957182459113110418834249)
      ·
        refine ⟨14967886844334832814125687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19957182459113110418834249 14967886844334832814125687)
        ·
          refine ⟨22451830266502249221188531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14967886844334832814125687 22451830266502249221188531)
          ·
            refine ⟨33677745399753373831782797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22451830266502249221188531 33677745399753373831782797)
            ·
              refine ⟨12629154524907515186918549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33677745399753373831782797 12629154524907515186918549)
              ·
                refine ⟨591991618355039774386807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12629154524907515186918549 591991618355039774386807)
                ·
                  refine ⟨887987427532559661580211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591991618355039774386807 887987427532559661580211)
                  ·
                    refine ⟨1331981141298839492370317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 887987427532559661580211 1331981141298839492370317)
                    ·
                      refine ⟨499492927987064809638869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1331981141298839492370317 499492927987064809638869)
                      ·
                        rfl

theorem cell23_972759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_972759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972759 prefixEnd_972759 := by exact prefixLift 972759
  have htrace : WordTrace (prefixWord ++ tailWord_972759) baseStart_972759 baseEnd_972759 := by
    simpa [prefixWord, tailWord_972759, baseEnd_972759] using wordTrace_append hprefix tailTrace_972759
  have hstable : (prefixWord ++ tailWord_972759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972759).length < 2 ^ (prefixWord ++ tailWord_972759).sum := by decide
  have hdescent : baseEnd_972759 < baseStart_972759 := by decide
  rcases family_descends (prefixWord ++ tailWord_972759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972795 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4]
def baseStart_972795 : Nat := 118140960795 + 972795 * 2 ^ 59
def prefixEnd_972795 : Nat := 4983230072969 + 3 ^ 40 * 972795 * 2
def baseEnd_972795 : Nat := 499511413290626668788703

theorem tailTrace_972795 : CollatzResearch.WordTrace tailWord_972795 prefixEnd_972795 499511413290626668788703 := by
  unfold tailWord_972795
  simp only [CollatzResearch.WordTrace]
  refine ⟨35480748510737330004015839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23653832340491553336010559 35480748510737330004015839)
  ·
    refine ⟨53221122766105995006023759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35480748510737330004015839 53221122766105995006023759)
    ·
      refine ⟨79831684149158992509035639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53221122766105995006023759 79831684149158992509035639)
      ·
        refine ⟨119747526223738488763553459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79831684149158992509035639 119747526223738488763553459)
        ·
          refine ⟨179621289335607733145330189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119747526223738488763553459 179621289335607733145330189)
          ·
            refine ⟨67357983500852899929498821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179621289335607733145330189 67357983500852899929498821)
            ·
              refine ⟨12629621906409918736781029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67357983500852899929498821 12629621906409918736781029)
              ·
                refine ⟨2368054107451859763146443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12629621906409918736781029 2368054107451859763146443)
                ·
                  refine ⟨3552081161177789644719665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368054107451859763146443 3552081161177789644719665)
                  ·
                    refine ⟨2664060870883342233539749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552081161177789644719665 2664060870883342233539749)
                    ·
                      refine ⟨499511413290626668788703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2664060870883342233539749 499511413290626668788703)
                      ·
                        rfl

theorem cell23_972795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4].length) (baseStart_972795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972795 prefixEnd_972795 := by exact prefixLift 972795
  have htrace : WordTrace (prefixWord ++ tailWord_972795) baseStart_972795 baseEnd_972795 := by
    simpa [prefixWord, tailWord_972795, baseEnd_972795] using wordTrace_append hprefix tailTrace_972795
  have hstable : (prefixWord ++ tailWord_972795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972795).length < 2 ^ (prefixWord ++ tailWord_972795).sum := by decide
  have hdescent : baseEnd_972795 < baseStart_972795 := by decide
  rcases family_descends (prefixWord ++ tailWord_972795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972805 : List Nat := [1, 3, 1, 1, 2, 6, 9]
def baseStart_972805 : Nat := 118140960795 + 972805 * 2 ^ 59
def prefixEnd_972805 : Nat := 4983230072969 + 3 ^ 40 * 972805 * 2
def baseEnd_972805 : Nat := 6166870964162612711897

theorem tailTrace_972805 : CollatzResearch.WordTrace tailWord_972805 prefixEnd_972805 6166870964162612711897 := by
  unfold tailWord_972805
  simp only [CollatzResearch.WordTrace]
  refine ⟨35481113240701101711879869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23654075493800734474586579 35481113240701101711879869)
  ·
    refine ⟨13305417465262913141954951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35481113240701101711879869 13305417465262913141954951)
    ·
      refine ⟨19958126197894369712932427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13305417465262913141954951 19958126197894369712932427)
      ·
        refine ⟨29937189296841554569398641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19958126197894369712932427 29937189296841554569398641)
        ·
          refine ⟨22452891972631165927048981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29937189296841554569398641 22452891972631165927048981)
          ·
            refine ⟨1052479311217085902830421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22452891972631165927048981 1052479311217085902830421)
            ·
              refine ⟨6166870964162612711897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1052479311217085902830421 6166870964162612711897)
              ·
                rfl

theorem cell23_972805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 9].length) (baseStart_972805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972805 prefixEnd_972805 := by exact prefixLift 972805
  have htrace : WordTrace (prefixWord ++ tailWord_972805) baseStart_972805 baseEnd_972805 := by
    simpa [prefixWord, tailWord_972805, baseEnd_972805] using wordTrace_append hprefix tailTrace_972805
  have hstable : (prefixWord ++ tailWord_972805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972805).length < 2 ^ (prefixWord ++ tailWord_972805).sum := by decide
  have hdescent : baseEnd_972805 < baseStart_972805 := by decide
  rcases family_descends (prefixWord ++ tailWord_972805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972826 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_972826 : Nat := 118140960795 + 972826 * 2 ^ 59
def prefixEnd_972826 : Nat := 4983230072969 + 3 ^ 40 * 972826 * 2
def baseEnd_972826 : Nat := 166509110396972015833687

theorem tailTrace_972826 : CollatzResearch.WordTrace tailWord_972826 prefixEnd_972826 166509110396972015833687 := by
  unfold tailWord_972826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8870469793406255574598583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23654586115750014865596221 8870469793406255574598583)
  ·
    refine ⟨13305704690109383361897875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8870469793406255574598583 13305704690109383361897875)
    ·
      refine ⟨19958557035164075042846813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13305704690109383361897875 19958557035164075042846813)
      ·
        refine ⟨7484458888186528141067555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19958557035164075042846813 7484458888186528141067555)
        ·
          refine ⟨11226688332279792211601333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7484458888186528141067555 11226688332279792211601333)
          ·
            refine ⟨1052502031151230519837625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11226688332279792211601333 1052502031151230519837625)
            ·
              refine ⟨789376523363422889878219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052502031151230519837625 789376523363422889878219)
              ·
                refine ⟨1184064785045134334817329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789376523363422889878219 1184064785045134334817329)
                ·
                  refine ⟨888048588783850751112997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184064785045134334817329 888048588783850751112997)
                  ·
                    refine ⟨166509110396972015833687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888048588783850751112997 166509110396972015833687)
                    ·
                      rfl

theorem cell23_972826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_972826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972826 prefixEnd_972826 := by exact prefixLift 972826
  have htrace : WordTrace (prefixWord ++ tailWord_972826) baseStart_972826 baseEnd_972826 := by
    simpa [prefixWord, tailWord_972826, baseEnd_972826] using wordTrace_append hprefix tailTrace_972826
  have hstable : (prefixWord ++ tailWord_972826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972826).length < 2 ^ (prefixWord ++ tailWord_972826).sum := by decide
  have hdescent : baseEnd_972826 < baseStart_972826 := by decide
  rcases family_descends (prefixWord ++ tailWord_972826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972889 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 1, 4, 2]
def baseStart_972889 : Nat := 118140960795 + 972889 * 2 ^ 59
def prefixEnd_972889 : Nat := 4983230072969 + 3 ^ 40 * 972889 * 2
def baseEnd_972889 : Nat := 499559680472149301013271

theorem tailTrace_972889 : CollatzResearch.WordTrace tailWord_972889 prefixEnd_972889 499559680472149301013271 := by
  unfold tailWord_972889
  simp only [CollatzResearch.WordTrace]
  refine ⟨35484176972396784057937721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23656117981597856038625147 35484176972396784057937721)
  ·
    refine ⟨26613132729297588043453291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35484176972396784057937721 26613132729297588043453291)
    ·
      refine ⟨39919699093946382065179937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26613132729297588043453291 39919699093946382065179937)
      ·
        refine ⟨29939774320459786548884953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39919699093946382065179937 29939774320459786548884953)
        ·
          refine ⟨22454830740344839911663715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29939774320459786548884953 22454830740344839911663715)
          ·
            refine ⟨33682246110517259867495573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22454830740344839911663715 33682246110517259867495573)
            ·
              refine ⟨1578855286430496556288855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33682246110517259867495573 1578855286430496556288855)
              ·
                refine ⟨2368282929645744834433283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578855286430496556288855 2368282929645744834433283)
                ·
                  refine ⟨3552424394468617251649925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368282929645744834433283 3552424394468617251649925)
                  ·
                    refine ⟨666079573962865734684361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3552424394468617251649925 666079573962865734684361)
                    ·
                      refine ⟨499559680472149301013271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666079573962865734684361 499559680472149301013271)
                      ·
                        rfl

theorem cell23_972889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_972889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972889 prefixEnd_972889 := by exact prefixLift 972889
  have htrace : WordTrace (prefixWord ++ tailWord_972889) baseStart_972889 baseEnd_972889 := by
    simpa [prefixWord, tailWord_972889, baseEnd_972889] using wordTrace_append hprefix tailTrace_972889
  have hstable : (prefixWord ++ tailWord_972889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972889).length < 2 ^ (prefixWord ++ tailWord_972889).sum := by decide
  have hdescent : baseEnd_972889 < baseStart_972889 := by decide
  rcases family_descends (prefixWord ++ tailWord_972889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972929 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 7]
def baseStart_972929 : Nat := 118140960795 + 972929 * 2 ^ 59
def prefixEnd_972929 : Nat := 4983230072969 + 3 ^ 40 * 972929 * 2
def baseEnd_972929 : Nat := 55508913299814349390343

theorem tailTrace_972929 : CollatzResearch.WordTrace tailWord_972929 prefixEnd_972929 55508913299814349390343 := by
  unfold tailWord_972929
  simp only [CollatzResearch.WordTrace]
  refine ⟨35485635892251870889393841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23657090594834580592929227 35485635892251870889393841)
  ·
    refine ⟨26614226919188903167045381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35485635892251870889393841 26614226919188903167045381)
    ·
      refine ⟨4990167547347919343821009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26614226919188903167045381 4990167547347919343821009)
      ·
        refine ⟨3742625660510939507865757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4990167547347919343821009 3742625660510939507865757)
        ·
          refine ⟨1403484622691602315449659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3742625660510939507865757 1403484622691602315449659)
          ·
            refine ⟨2105226934037403473174489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403484622691602315449659 2105226934037403473174489)
            ·
              refine ⟨1578920200528052604880867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105226934037403473174489 1578920200528052604880867)
              ·
                refine ⟨2368380300792078907321301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578920200528052604880867 2368380300792078907321301)
                ·
                  refine ⟨55508913299814349390343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2368380300792078907321301 55508913299814349390343)
                  ·
                    rfl

theorem cell23_972929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 7].length) (baseStart_972929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972929 prefixEnd_972929 := by exact prefixLift 972929
  have htrace : WordTrace (prefixWord ++ tailWord_972929) baseStart_972929 baseEnd_972929 := by
    simpa [prefixWord, tailWord_972929, baseEnd_972929] using wordTrace_append hprefix tailTrace_972929
  have hstable : (prefixWord ++ tailWord_972929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972929).length < 2 ^ (prefixWord ++ tailWord_972929).sum := by decide
  have hdescent : baseEnd_972929 < baseStart_972929 := by decide
  rcases family_descends (prefixWord ++ tailWord_972929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972955 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 2, 8]
def baseStart_972955 : Nat := 118140960795 + 972955 * 2 ^ 59
def prefixEnd_972955 : Nat := 4983230072969 + 3 ^ 40 * 972955 * 2
def baseEnd_972955 : Nat := 166531190065115347595989

theorem tailTrace_972955 : CollatzResearch.WordTrace tailWord_972955 prefixEnd_972955 166531190065115347595989 := by
  unfold tailWord_972955
  simp only [CollatzResearch.WordTrace]
  refine ⟨35486584190157677329840319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23657722793438451553226879 35486584190157677329840319)
  ·
    refine ⟨53229876285236515994760479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35486584190157677329840319 53229876285236515994760479)
    ·
      refine ⟨79844814427854773992140719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53229876285236515994760479 79844814427854773992140719)
      ·
        refine ⟨119767221641782160988211079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79844814427854773992140719 119767221641782160988211079)
        ·
          refine ⟨179650832462673241482316619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119767221641782160988211079 179650832462673241482316619)
          ·
            refine ⟨269476248694009862223474929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179650832462673241482316619 269476248694009862223474929)
            ·
              refine ⟨202107186520507396667606197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269476248694009862223474929 202107186520507396667606197)
              ·
                refine ⟨18947548736297568437588081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202107186520507396667606197 18947548736297568437588081)
                ·
                  refine ⟨14210661552223176328191061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18947548736297568437588081 14210661552223176328191061)
                  ·
                    refine ⟨166531190065115347595989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14210661552223176328191061 166531190065115347595989)
                    ·
                      rfl

theorem cell23_972955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_972955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972955 prefixEnd_972955 := by exact prefixLift 972955
  have htrace : WordTrace (prefixWord ++ tailWord_972955) baseStart_972955 baseEnd_972955 := by
    simpa [prefixWord, tailWord_972955, baseEnd_972955] using wordTrace_append hprefix tailTrace_972955
  have hstable : (prefixWord ++ tailWord_972955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972955).length < 2 ^ (prefixWord ++ tailWord_972955).sum := by decide
  have hdescent : baseEnd_972955 < baseStart_972955 := by decide
  rcases family_descends (prefixWord ++ tailWord_972955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972980 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 7]
def baseStart_972980 : Nat := 118140960795 + 972980 * 2 ^ 59
def prefixEnd_972980 : Nat := 4983230072969 + 3 ^ 40 * 972980 * 2
def baseEnd_972980 : Nat := 55511823023523160552817

theorem tailTrace_972980 : CollatzResearch.WordTrace tailWord_972980 prefixEnd_972980 55511823023523160552817 := by
  unfold tailWord_972980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743748007533553299750197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23658330676711404399666929 17743748007533553299750197)
  ·
    refine ⟨1663476375706270621851581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17743748007533553299750197 1663476375706270621851581)
    ·
      refine ⟨623803640889851483194343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1663476375706270621851581 623803640889851483194343)
      ·
        refine ⟨935705461334777224791515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623803640889851483194343 935705461334777224791515)
        ·
          refine ⟨1403558192002165837187273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935705461334777224791515 1403558192002165837187273)
          ·
            refine ⟨1052668644001624377890455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403558192002165837187273 1052668644001624377890455)
            ·
              refine ⟨1579002966002436566835683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052668644001624377890455 1579002966002436566835683)
              ·
                refine ⟨2368504449003654850253525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579002966002436566835683 2368504449003654850253525)
                ·
                  refine ⟨55511823023523160552817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2368504449003654850253525 55511823023523160552817)
                  ·
                    rfl

theorem cell23_972980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_972980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_972980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_972980 prefixEnd_972980 := by exact prefixLift 972980
  have htrace : WordTrace (prefixWord ++ tailWord_972980) baseStart_972980 baseEnd_972980 := by
    simpa [prefixWord, tailWord_972980, baseEnd_972980] using wordTrace_append hprefix tailTrace_972980
  have hstable : (prefixWord ++ tailWord_972980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972980).length < 2 ^ (prefixWord ++ tailWord_972980).sum := by decide
  have hdescent : baseEnd_972980 < baseStart_972980 := by decide
  rcases family_descends (prefixWord ++ tailWord_972980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973016 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_973016 : Nat := 118140960795 + 973016 * 2 ^ 59
def prefixEnd_973016 : Nat := 4983230072969 + 3 ^ 40 * 973016 * 2
def baseEnd_973016 : Nat := 499624892515270304125187

theorem tailTrace_973016 : CollatzResearch.WordTrace tailWord_973016 prefixEnd_973016 499624892515270304125187 := by
  unfold tailWord_973016
  simp only [CollatzResearch.WordTrace]
  refine ⟨17744404521468342373905451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23659206028624456498540601 17744404521468342373905451)
  ·
    refine ⟨26616606782202513560858177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17744404521468342373905451 26616606782202513560858177)
    ·
      refine ⟨19962455086651885170643633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26616606782202513560858177 19962455086651885170643633)
      ·
        refine ⟨14971841314988913877982725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19962455086651885170643633 14971841314988913877982725)
        ·
          refine ⟨2807220246560421352121761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14971841314988913877982725 2807220246560421352121761)
          ·
            refine ⟨2105415184920316014091321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2807220246560421352121761 2105415184920316014091321)
            ·
              refine ⟨1579061388690237010568491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105415184920316014091321 1579061388690237010568491)
              ·
                refine ⟨2368592083035355515852737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579061388690237010568491 2368592083035355515852737)
                ·
                  refine ⟨1776444062276516636889553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368592083035355515852737 1776444062276516636889553)
                  ·
                    refine ⟨1332333046707387477667165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1776444062276516636889553 1332333046707387477667165)
                    ·
                      refine ⟨499624892515270304125187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1332333046707387477667165 499624892515270304125187)
                      ·
                        rfl

theorem cell23_973016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_973016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973016 prefixEnd_973016 := by exact prefixLift 973016
  have htrace : WordTrace (prefixWord ++ tailWord_973016) baseStart_973016 baseEnd_973016 := by
    simpa [prefixWord, tailWord_973016, baseEnd_973016] using wordTrace_append hprefix tailTrace_973016
  have hstable : (prefixWord ++ tailWord_973016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973016).length < 2 ^ (prefixWord ++ tailWord_973016).sum := by decide
  have hdescent : baseEnd_973016 < baseStart_973016 := by decide
  rcases family_descends (prefixWord ++ tailWord_973016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973073 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 2, 3, 2]
def baseStart_973073 : Nat := 118140960795 + 973073 * 2 ^ 59
def prefixEnd_973073 : Nat := 4983230072969 + 3 ^ 40 * 973073 * 2
def baseEnd_973073 : Nat := 499654160912576581112425

theorem tailTrace_973073 : CollatzResearch.WordTrace tailWord_973073 prefixEnd_973073 499654160912576581112425 := by
  unfold tailWord_973073
  simp only [CollatzResearch.WordTrace]
  refine ⟨35490888003730183482635873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23660592002486788988423915 35490888003730183482635873)
  ·
    refine ⟨26618166002797637611976905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35490888003730183482635873 26618166002797637611976905)
    ·
      refine ⟨19963624502098228208982679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26618166002797637611976905 19963624502098228208982679)
      ·
        refine ⟨29945436753147342313474019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19963624502098228208982679 29945436753147342313474019)
        ·
          refine ⟨44918155129721013470211029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29945436753147342313474019 44918155129721013470211029)
          ·
            refine ⟨1052769260852836253208071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44918155129721013470211029 1052769260852836253208071)
            ·
              refine ⟨1579153891279254379812107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052769260852836253208071 1579153891279254379812107)
              ·
                refine ⟨2368730836918881569718161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579153891279254379812107 2368730836918881569718161)
                ·
                  refine ⟨1776548127689161177288621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368730836918881569718161 1776548127689161177288621)
                  ·
                    refine ⟨666205547883435441483233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776548127689161177288621 666205547883435441483233)
                    ·
                      refine ⟨499654160912576581112425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666205547883435441483233 499654160912576581112425)
                      ·
                        rfl

theorem cell23_973073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_973073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973073 prefixEnd_973073 := by exact prefixLift 973073
  have htrace : WordTrace (prefixWord ++ tailWord_973073) baseStart_973073 baseEnd_973073 := by
    simpa [prefixWord, tailWord_973073, baseEnd_973073] using wordTrace_append hprefix tailTrace_973073
  have hstable : (prefixWord ++ tailWord_973073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973073).length < 2 ^ (prefixWord ++ tailWord_973073).sum := by decide
  have hdescent : baseEnd_973073 < baseStart_973073 := by decide
  rcases family_descends (prefixWord ++ tailWord_973073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973079 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 1, 6]
def baseStart_973079 : Nat := 118140960795 + 973079 * 2 ^ 59
def prefixEnd_973079 : Nat := 4983230072969 + 3 ^ 40 * 973079 * 2
def baseEnd_973079 : Nat := 166552413932167852545799

theorem tailTrace_973079 : CollatzResearch.WordTrace tailWord_973079 prefixEnd_973079 166552413932167852545799 := by
  unfold tailWord_973079
  simp only [CollatzResearch.WordTrace]
  refine ⟨35491106841708446507354291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23660737894472297671569527 35491106841708446507354291)
  ·
    refine ⟨53236660262562669761031437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35491106841708446507354291 53236660262562669761031437)
    ·
      refine ⟨19963747598461001160386789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53236660262562669761031437 19963747598461001160386789)
      ·
        refine ⟨3743202674711437717572523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19963747598461001160386789 3743202674711437717572523)
        ·
          refine ⟨5614804012067156576358785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743202674711437717572523 5614804012067156576358785)
          ·
            refine ⟨4211103009050367432269089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5614804012067156576358785 4211103009050367432269089)
            ·
              refine ⟨3158327256787775574201817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211103009050367432269089 3158327256787775574201817)
              ·
                refine ⟨2368745442590831680651363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158327256787775574201817 2368745442590831680651363)
                ·
                  refine ⟨3553118163886247520977045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368745442590831680651363 3553118163886247520977045)
                  ·
                    refine ⟨166552413932167852545799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3553118163886247520977045 166552413932167852545799)
                    ·
                      rfl

theorem cell23_973079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_973079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973079 prefixEnd_973079 := by exact prefixLift 973079
  have htrace : WordTrace (prefixWord ++ tailWord_973079) baseStart_973079 baseEnd_973079 := by
    simpa [prefixWord, tailWord_973079, baseEnd_973079] using wordTrace_append hprefix tailTrace_973079
  have hstable : (prefixWord ++ tailWord_973079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973079).length < 2 ^ (prefixWord ++ tailWord_973079).sum := by decide
  have hdescent : baseEnd_973079 < baseStart_973079 := by decide
  rcases family_descends (prefixWord ++ tailWord_973079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973106 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_973106 : Nat := 118140960795 + 973106 * 2 ^ 59
def prefixEnd_973106 : Nat := 4983230072969 + 3 ^ 40 * 973106 * 2
def baseEnd_973106 : Nat := 499671105774174951999773

theorem tailTrace_973106 : CollatzResearch.WordTrace tailWord_973106 prefixEnd_973106 499671105774174951999773 := by
  unfold tailWord_973106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873022903152657529646793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23661394408407086745724781 8873022903152657529646793)
  ·
    refine ⟨6654767177364493147235095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8873022903152657529646793 6654767177364493147235095)
    ·
      refine ⟨9982150766046739720852643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6654767177364493147235095 9982150766046739720852643)
      ·
        refine ⟨14973226149070109581278965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9982150766046739720852643 14973226149070109581278965)
        ·
          refine ⟨1403739951475322773244903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14973226149070109581278965 1403739951475322773244903)
          ·
            refine ⟨2105609927212984159867355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403739951475322773244903 2105609927212984159867355)
            ·
              refine ⟨3158414890819476239801033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105609927212984159867355 3158414890819476239801033)
              ·
                refine ⟨2368811168114607179850775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158414890819476239801033 2368811168114607179850775)
                ·
                  refine ⟨3553216752171910769776163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368811168114607179850775 3553216752171910769776163)
                  ·
                    refine ⟨5329825128257866154664245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553216752171910769776163 5329825128257866154664245)
                    ·
                      refine ⟨499671105774174951999773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5329825128257866154664245 499671105774174951999773)
                      ·
                        rfl

theorem cell23_973106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_973106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973106 prefixEnd_973106 := by exact prefixLift 973106
  have htrace : WordTrace (prefixWord ++ tailWord_973106) baseStart_973106 baseEnd_973106 := by
    simpa [prefixWord, tailWord_973106, baseEnd_973106] using wordTrace_append hprefix tailTrace_973106
  have hstable : (prefixWord ++ tailWord_973106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973106).length < 2 ^ (prefixWord ++ tailWord_973106).sum := by decide
  have hdescent : baseEnd_973106 < baseStart_973106 := by decide
  rcases family_descends (prefixWord ++ tailWord_973106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973136 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 4, 1, 3]
def baseStart_973136 : Nat := 118140960795 + 973136 * 2 ^ 59
def prefixEnd_973136 : Nat := 4983230072969 + 3 ^ 40 * 973136 * 2
def baseEnd_973136 : Nat := 499686510193809834624635

theorem tailTrace_973136 : CollatzResearch.WordTrace tailWord_973136 prefixEnd_973136 499686510193809834624635 := by
  unfold tailWord_973136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17746592901250972621089631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23662123868334630161452841 17746592901250972621089631)
  ·
    refine ⟨26619889351876458931634447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17746592901250972621089631 26619889351876458931634447)
    ·
      refine ⟨39929834027814688397451671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26619889351876458931634447 39929834027814688397451671)
      ·
        refine ⟨59894751041722032596177507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39929834027814688397451671 59894751041722032596177507)
        ·
          refine ⟨89842126562583048894266261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59894751041722032596177507 89842126562583048894266261)
          ·
            refine ⟨4211349682621080416918731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89842126562583048894266261 4211349682621080416918731)
            ·
              refine ⟨6317024523931620625378097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211349682621080416918731 6317024523931620625378097)
              ·
                refine ⟨4737768392948715469033573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6317024523931620625378097 4737768392948715469033573)
                ·
                  refine ⟨888331573677884150443795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4737768392948715469033573 888331573677884150443795)
                  ·
                    refine ⟨1332497360516826225665693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888331573677884150443795 1332497360516826225665693)
                    ·
                      refine ⟨499686510193809834624635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1332497360516826225665693 499686510193809834624635)
                      ·
                        rfl

theorem cell23_973136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 1, 3].length) (baseStart_973136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973136 prefixEnd_973136 := by exact prefixLift 973136
  have htrace : WordTrace (prefixWord ++ tailWord_973136) baseStart_973136 baseEnd_973136 := by
    simpa [prefixWord, tailWord_973136, baseEnd_973136] using wordTrace_append hprefix tailTrace_973136
  have hstable : (prefixWord ++ tailWord_973136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973136).length < 2 ^ (prefixWord ++ tailWord_973136).sum := by decide
  have hdescent : baseEnd_973136 < baseStart_973136 := by decide
  rcases family_descends (prefixWord ++ tailWord_973136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973137 : List Nat := [1, 2, 2, 1, 4, 4, 1, 3, 1, 2, 2]
def baseStart_973137 : Nat := 118140960795 + 973137 * 2 ^ 59
def prefixEnd_973137 : Nat := 4983230072969 + 3 ^ 40 * 973137 * 2
def baseEnd_973137 : Nat := 499687023674464330712131

theorem tailTrace_973137 : CollatzResearch.WordTrace tailWord_973137 prefixEnd_973137 499687023674464330712131 := by
  unfold tailWord_973137
  simp only [CollatzResearch.WordTrace]
  refine ⟨35493222275498322412965665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23662148183665548275310443 35493222275498322412965665)
  ·
    refine ⟨26619916706623741809724249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35493222275498322412965665 26619916706623741809724249)
    ·
      refine ⟨19964937529967806357293187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26619916706623741809724249 19964937529967806357293187)
      ·
        refine ⟨29947406294951709535939781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19964937529967806357293187 29947406294951709535939781)
        ·
          refine ⟨5615138680303445537988709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29947406294951709535939781 5615138680303445537988709)
          ·
            refine ⟨1052838502556896038372883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5615138680303445537988709 1052838502556896038372883)
            ·
              refine ⟨1579257753835344057559325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052838502556896038372883 1579257753835344057559325)
              ·
                refine ⟨592221657688254021584747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1579257753835344057559325 592221657688254021584747)
                ·
                  refine ⟨888332486532381032377121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592221657688254021584747 888332486532381032377121)
                  ·
                    refine ⟨666249364899285774282841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 888332486532381032377121 666249364899285774282841)
                    ·
                      refine ⟨499687023674464330712131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666249364899285774282841 499687023674464330712131)
                      ·
                        rfl

theorem cell23_973137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_973137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973137 prefixEnd_973137 := by exact prefixLift 973137
  have htrace : WordTrace (prefixWord ++ tailWord_973137) baseStart_973137 baseEnd_973137 := by
    simpa [prefixWord, tailWord_973137, baseEnd_973137] using wordTrace_append hprefix tailTrace_973137
  have hstable : (prefixWord ++ tailWord_973137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973137).length < 2 ^ (prefixWord ++ tailWord_973137).sum := by decide
  have hdescent : baseEnd_973137 < baseStart_973137 := by decide
  rcases family_descends (prefixWord ++ tailWord_973137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973146 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2]
def baseStart_973146 : Nat := 118140960795 + 973146 * 2 ^ 59
def prefixEnd_973146 : Nat := 4983230072969 + 3 ^ 40 * 973146 * 2
def baseEnd_973146 : Nat := 499691645000354795499589

theorem tailTrace_973146 : CollatzResearch.WordTrace tailWord_973146 prefixEnd_973146 499691645000354795499589 := by
  unfold tailWord_973146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873387633116429237510823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23662367021643811300028861 8873387633116429237510823)
  ·
    refine ⟨13310081449674643856266235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8873387633116429237510823 13310081449674643856266235)
    ·
      refine ⟨19965122174511965784399353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13310081449674643856266235 19965122174511965784399353)
      ·
        refine ⟨14973841630883974338299515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19965122174511965784399353 14973841630883974338299515)
        ·
          refine ⟨22460762446325961507449273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14973841630883974338299515 22460762446325961507449273)
          ·
            refine ⟨16845571834744471130586955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22460762446325961507449273 16845571834744471130586955)
            ·
              refine ⟨25268357752116706695880433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16845571834744471130586955 25268357752116706695880433)
              ·
                refine ⟨18951268314087530021910325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25268357752116706695880433 18951268314087530021910325)
                ·
                  refine ⟨1776681404445705939554093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18951268314087530021910325 1776681404445705939554093)
                  ·
                    refine ⟨666255526667139727332785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1776681404445705939554093 666255526667139727332785)
                    ·
                      refine ⟨499691645000354795499589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666255526667139727332785 499691645000354795499589)
                      ·
                        rfl

theorem cell23_973146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_973146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973146 prefixEnd_973146 := by exact prefixLift 973146
  have htrace : WordTrace (prefixWord ++ tailWord_973146) baseStart_973146 baseEnd_973146 := by
    simpa [prefixWord, tailWord_973146, baseEnd_973146] using wordTrace_append hprefix tailTrace_973146
  have hstable : (prefixWord ++ tailWord_973146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973146).length < 2 ^ (prefixWord ++ tailWord_973146).sum := by decide
  have hdescent : baseEnd_973146 < baseStart_973146 := by decide
  rcases family_descends (prefixWord ++ tailWord_973146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973154 : List Nat := [3, 3, 2, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_973154 : Nat := 118140960795 + 973154 * 2 ^ 59
def prefixEnd_973154 : Nat := 4983230072969 + 3 ^ 40 * 973154 * 2
def baseEnd_973154 : Nat := 499695752845590764199553

theorem tailTrace_973154 : CollatzResearch.WordTrace tailWord_973154 prefixEnd_973154 499695752845590764199553 := by
  unfold tailWord_973154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873460579109183579083629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23662561544291156210889677 8873460579109183579083629)
  ·
    refine ⟨3327547717165943842156361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8873460579109183579083629 3327547717165943842156361)
    ·
      refine ⟨2495660787874457881617271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3327547717165943842156361 2495660787874457881617271)
      ·
        refine ⟨3743491181811686822425907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495660787874457881617271 3743491181811686822425907)
        ·
          refine ⟨5615236772717530233638861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743491181811686822425907 5615236772717530233638861)
          ·
            refine ⟨2105713789769073837614573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5615236772717530233638861 2105713789769073837614573)
            ·
              refine ⟨789642671163402689105465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2105713789769073837614573 789642671163402689105465)
              ·
                refine ⟨592232003372552016829099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789642671163402689105465 592232003372552016829099)
                ·
                  refine ⟨888348005058828025243649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592232003372552016829099 888348005058828025243649)
                  ·
                    refine ⟨666261003794121018932737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 888348005058828025243649 666261003794121018932737)
                    ·
                      refine ⟨499695752845590764199553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666261003794121018932737 499695752845590764199553)
                      ·
                        rfl

theorem cell23_973154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_973154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973154 prefixEnd_973154 := by exact prefixLift 973154
  have htrace : WordTrace (prefixWord ++ tailWord_973154) baseStart_973154 baseEnd_973154 := by
    simpa [prefixWord, tailWord_973154, baseEnd_973154] using wordTrace_append hprefix tailTrace_973154
  have hstable : (prefixWord ++ tailWord_973154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973154).length < 2 ^ (prefixWord ++ tailWord_973154).sum := by decide
  have hdescent : baseEnd_973154 < baseStart_973154 := by decide
  rcases family_descends (prefixWord ++ tailWord_973154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973170 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_973170 : Nat := 118140960795 + 973170 * 2 ^ 59
def prefixEnd_973170 : Nat := 4983230072969 + 3 ^ 40 * 973170 * 2
def baseEnd_973170 : Nat := 499703968536062701599479

theorem tailTrace_973170 : CollatzResearch.WordTrace tailWord_973170 prefixEnd_973170 499703968536062701599479 := by
  unfold tailWord_973170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873606471094692262229241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23662950589585846032611309 8873606471094692262229241)
  ·
    refine ⟨6655204853321019196671931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8873606471094692262229241 6655204853321019196671931)
    ·
      refine ⟨9982807279981528795007897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6655204853321019196671931 9982807279981528795007897)
      ·
        refine ⟨7487105459986146596255923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9982807279981528795007897 7487105459986146596255923)
        ·
          refine ⟨11230658189979219894383885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7487105459986146596255923 11230658189979219894383885)
          ·
            refine ⟨4211496821242207460393957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11230658189979219894383885 4211496821242207460393957)
            ·
              refine ⟨789655653982913898823867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4211496821242207460393957 789655653982913898823867)
              ·
                refine ⟨1184483480974370848235801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789655653982913898823867 1184483480974370848235801)
                ·
                  refine ⟨888362610730778136176851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184483480974370848235801 888362610730778136176851)
                  ·
                    refine ⟨1332543916096167204265277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888362610730778136176851 1332543916096167204265277)
                    ·
                      refine ⟨499703968536062701599479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1332543916096167204265277 499703968536062701599479)
                      ·
                        rfl

theorem cell23_973170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_973170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973170 prefixEnd_973170 := by exact prefixLift 973170
  have htrace : WordTrace (prefixWord ++ tailWord_973170) baseStart_973170 baseEnd_973170 := by
    simpa [prefixWord, tailWord_973170, baseEnd_973170] using wordTrace_append hprefix tailTrace_973170
  have hstable : (prefixWord ++ tailWord_973170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973170).length < 2 ^ (prefixWord ++ tailWord_973170).sum := by decide
  have hdescent : baseEnd_973170 < baseStart_973170 := by decide
  rcases family_descends (prefixWord ++ tailWord_973170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973174 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_973174 : Nat := 118140960795 + 973174 * 2 ^ 59
def prefixEnd_973174 : Nat := 4983230072969 + 3 ^ 40 * 973174 * 2
def baseEnd_973174 : Nat := 499706022458680685949461

theorem tailTrace_973174 : CollatzResearch.WordTrace tailWord_973174 prefixEnd_973174 499706022458680685949461 := by
  unfold tailWord_973174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218410736022767358253911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23663047850909518488041717 2218410736022767358253911)
  ·
    refine ⟨3327616104034151037380867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2218410736022767358253911 3327616104034151037380867)
    ·
      refine ⟨4991424156051226556071301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327616104034151037380867 4991424156051226556071301)
      ·
        refine ⟨935892029259604979263369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4991424156051226556071301 935892029259604979263369)
        ·
          refine ⟨701919021944703734447527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935892029259604979263369 701919021944703734447527)
          ·
            refine ⟨1052878532917055601671291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701919021944703734447527 1052878532917055601671291)
            ·
              refine ⟨1579317799375583402506937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052878532917055601671291 1579317799375583402506937)
              ·
                refine ⟨1184488349531687551880203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579317799375583402506937 1184488349531687551880203)
                ·
                  refine ⟨1776732524297531327820305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184488349531687551880203 1776732524297531327820305)
                  ·
                    refine ⟨1332549393223148495865229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1776732524297531327820305 1332549393223148495865229)
                    ·
                      refine ⟨499706022458680685949461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1332549393223148495865229 499706022458680685949461)
                      ·
                        rfl

theorem cell23_973174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_973174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973174 prefixEnd_973174 := by exact prefixLift 973174
  have htrace : WordTrace (prefixWord ++ tailWord_973174) baseStart_973174 baseEnd_973174 := by
    simpa [prefixWord, tailWord_973174, baseEnd_973174] using wordTrace_append hprefix tailTrace_973174
  have hstable : (prefixWord ++ tailWord_973174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973174).length < 2 ^ (prefixWord ++ tailWord_973174).sum := by decide
  have hdescent : baseEnd_973174 < baseStart_973174 := by decide
  rcases family_descends (prefixWord ++ tailWord_973174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973179 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5]
def baseStart_973179 : Nat := 118140960795 + 973179 * 2 ^ 59
def prefixEnd_973179 : Nat := 4983230072969 + 3 ^ 40 * 973179 * 2
def baseEnd_973179 : Nat := 499708589861953166386937

theorem tailTrace_973179 : CollatzResearch.WordTrace tailWord_973179 prefixEnd_973179 499708589861953166386937 := by
  unfold tailWord_973179
  simp only [CollatzResearch.WordTrace]
  refine ⟨35494754141346163585994591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23663169427564109057329727 35494754141346163585994591)
  ·
    refine ⟨53242131212019245378991887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35494754141346163585994591 53242131212019245378991887)
    ·
      refine ⟨79863196818028868068487831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53242131212019245378991887 79863196818028868068487831)
      ·
        refine ⟨119794795227043302102731747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79863196818028868068487831 119794795227043302102731747)
        ·
          refine ⟨179692192840564953154097621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119794795227043302102731747 179692192840564953154097621)
          ·
            refine ⟨4211535769700741089549163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 179692192840564953154097621 4211535769700741089549163)
            ·
              refine ⟨6317303654551111634323745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211535769700741089549163 6317303654551111634323745)
              ·
                refine ⟨4737977740913333725742809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6317303654551111634323745 4737977740913333725742809)
                ·
                  refine ⟨3553483305685000294307107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4737977740913333725742809 3553483305685000294307107)
                  ·
                    refine ⟨5330224958527500441460661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553483305685000294307107 5330224958527500441460661)
                    ·
                      refine ⟨499708589861953166386937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5330224958527500441460661 499708589861953166386937)
                      ·
                        rfl

theorem cell23_973179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_973179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973179 prefixEnd_973179 := by exact prefixLift 973179
  have htrace : WordTrace (prefixWord ++ tailWord_973179) baseStart_973179 baseEnd_973179 := by
    simpa [prefixWord, tailWord_973179, baseEnd_973179] using wordTrace_append hprefix tailTrace_973179
  have hstable : (prefixWord ++ tailWord_973179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973179).length < 2 ^ (prefixWord ++ tailWord_973179).sum := by decide
  have hdescent : baseEnd_973179 < baseStart_973179 := by decide
  rcases family_descends (prefixWord ++ tailWord_973179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973189 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_973189 : Nat := 118140960795 + 973189 * 2 ^ 59
def prefixEnd_973189 : Nat := 4983230072969 + 3 ^ 40 * 973189 * 2
def baseEnd_973189 : Nat := 499713724668498127261891

theorem tailTrace_973189 : CollatzResearch.WordTrace tailWord_973189 prefixEnd_973189 499713724668498127261891 := by
  unfold tailWord_973189
  simp only [CollatzResearch.WordTrace]
  refine ⟨35495118871309935293858621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23663412580873290195905747 35495118871309935293858621)
  ·
    refine ⟨13310669576741225735196983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35495118871309935293858621 13310669576741225735196983)
    ·
      refine ⟨19966004365111838602795475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13310669576741225735196983 19966004365111838602795475)
      ·
        refine ⟨29949006547667757904193213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19966004365111838602795475 29949006547667757904193213)
        ·
          refine ⟨11230877455375409214072455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29949006547667757904193213 11230877455375409214072455)
          ·
            refine ⟨16846316183063113821108683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11230877455375409214072455 16846316183063113821108683)
            ·
              refine ⟨25269474274594670731663025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16846316183063113821108683 25269474274594670731663025)
              ·
                refine ⟨18952105705946003048747269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25269474274594670731663025 18952105705946003048747269)
                ·
                  refine ⟨3553519819864875571640113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18952105705946003048747269 3553519819864875571640113)
                  ·
                    refine ⟨2665139864898656678730085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3553519819864875571640113 2665139864898656678730085)
                    ·
                      refine ⟨499713724668498127261891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2665139864898656678730085 499713724668498127261891)
                      ·
                        rfl

theorem cell23_973189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_973189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973189 prefixEnd_973189 := by exact prefixLift 973189
  have htrace : WordTrace (prefixWord ++ tailWord_973189) baseStart_973189 baseEnd_973189 := by
    simpa [prefixWord, tailWord_973189, baseEnd_973189] using wordTrace_append hprefix tailTrace_973189
  have hstable : (prefixWord ++ tailWord_973189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973189).length < 2 ^ (prefixWord ++ tailWord_973189).sum := by decide
  have hdescent : baseEnd_973189 < baseStart_973189 := by decide
  rcases family_descends (prefixWord ++ tailWord_973189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973193 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 1, 4, 2]
def baseStart_973193 : Nat := 118140960795 + 973193 * 2 ^ 59
def prefixEnd_973193 : Nat := 4983230072969 + 3 ^ 40 * 973193 * 2
def baseEnd_973193 : Nat := 499715778591116111611873

theorem tailTrace_973193 : CollatzResearch.WordTrace tailWord_973193 prefixEnd_973193 499715778591116111611873 := by
  unfold tailWord_973193
  simp only [CollatzResearch.WordTrace]
  refine ⟨35495264763295443977004233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23663509842196962651336155 35495264763295443977004233)
  ·
    refine ⟨26621448572471582982753175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35495264763295443977004233 26621448572471582982753175)
    ·
      refine ⟨39932172858707374474129763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26621448572471582982753175 39932172858707374474129763)
      ·
        refine ⟨59898259288061061711194645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39932172858707374474129763 59898259288061061711194645)
        ·
          refine ⟨2807730904127862267712249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59898259288061061711194645 2807730904127862267712249)
          ·
            refine ⟨2105798178095896700784187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2807730904127862267712249 2105798178095896700784187)
            ·
              refine ⟨3158697267143845051176281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105798178095896700784187 3158697267143845051176281)
              ·
                refine ⟨2369022950357883788382211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158697267143845051176281 2369022950357883788382211)
                ·
                  refine ⟨3553534425536825682573317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369022950357883788382211 3553534425536825682573317)
                  ·
                    refine ⟨666287704788154815482497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3553534425536825682573317 666287704788154815482497)
                    ·
                      refine ⟨499715778591116111611873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666287704788154815482497 499715778591116111611873)
                      ·
                        rfl

theorem cell23_973193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 4, 2].length) (baseStart_973193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973193 prefixEnd_973193 := by exact prefixLift 973193
  have htrace : WordTrace (prefixWord ++ tailWord_973193) baseStart_973193 baseEnd_973193 := by
    simpa [prefixWord, tailWord_973193, baseEnd_973193] using wordTrace_append hprefix tailTrace_973193
  have hstable : (prefixWord ++ tailWord_973193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973193).length < 2 ^ (prefixWord ++ tailWord_973193).sum := by decide
  have hdescent : baseEnd_973193 < baseStart_973193 := by decide
  rcases family_descends (prefixWord ++ tailWord_973193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973210 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2]
def baseStart_973210 : Nat := 118140960795 + 973210 * 2 ^ 59
def prefixEnd_973210 : Nat := 4983230072969 + 3 ^ 40 * 973210 * 2
def baseEnd_973210 : Nat := 499724507762242545099295

theorem tailTrace_973210 : CollatzResearch.WordTrace tailWord_973210 prefixEnd_973210 499724507762242545099295 := by
  unfold tailWord_973210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873971201058463970093271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23663923202822570586915389 8873971201058463970093271)
  ·
    refine ⟨13310956801587695955139907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8873971201058463970093271 13310956801587695955139907)
    ·
      refine ⟨19966435202381543932709861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13310956801587695955139907 19966435202381543932709861)
      ·
        refine ⟨3743706600446539487383099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19966435202381543932709861 3743706600446539487383099)
        ·
          refine ⟨5615559900669809231074649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743706600446539487383099 5615559900669809231074649)
          ·
            refine ⟨4211669925502356923305987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5615559900669809231074649 4211669925502356923305987)
            ·
              refine ⟨6317504888253535384958981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211669925502356923305987 6317504888253535384958981)
              ·
                refine ⟨1184532166547537884679809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6317504888253535384958981 1184532166547537884679809)
                ·
                  refine ⟨888399124910653413509857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184532166547537884679809 888399124910653413509857)
                  ·
                    refine ⟨666299343682990060132393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 888399124910653413509857 666299343682990060132393)
                    ·
                      refine ⟨499724507762242545099295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666299343682990060132393 499724507762242545099295)
                      ·
                        rfl

theorem cell23_973210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_973210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973210 prefixEnd_973210 := by exact prefixLift 973210
  have htrace : WordTrace (prefixWord ++ tailWord_973210) baseStart_973210 baseEnd_973210 := by
    simpa [prefixWord, tailWord_973210, baseEnd_973210] using wordTrace_append hprefix tailTrace_973210
  have hstable : (prefixWord ++ tailWord_973210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973210).length < 2 ^ (prefixWord ++ tailWord_973210).sum := by decide
  have hdescent : baseEnd_973210 < baseStart_973210 := by decide
  rcases family_descends (prefixWord ++ tailWord_973210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973339 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10]
def baseStart_973339 : Nat := 118140960795 + 973339 * 2 ^ 59
def prefixEnd_973339 : Nat := 4983230072969 + 3 ^ 40 * 973339 * 2
def baseEnd_973339 : Nat := 499790746766672540386201

theorem tailTrace_973339 : CollatzResearch.WordTrace tailWord_973339 prefixEnd_973339 499790746766672540386201 := by
  unfold tailWord_973339
  simp only [CollatzResearch.WordTrace]
  refine ⟨35500589820766510911819071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23667059880511007274546047 35500589820766510911819071)
  ·
    refine ⟨53250884731149766367728607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35500589820766510911819071 53250884731149766367728607)
    ·
      refine ⟨79876327096724649551592911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53250884731149766367728607 79876327096724649551592911)
      ·
        refine ⟨119814490645086974327389367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79876327096724649551592911 119814490645086974327389367)
        ·
          refine ⟨179721735967630461491084051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119814490645086974327389367 179721735967630461491084051)
          ·
            refine ⟨269582603951445692236626077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179721735967630461491084051 269582603951445692236626077)
            ·
              refine ⟨101093476481792134588734779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269582603951445692236626077 101093476481792134588734779)
              ·
                refine ⟨151640214722688201883102169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101093476481792134588734779 151640214722688201883102169)
                ·
                  refine ⟨113730161042016151412326627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151640214722688201883102169 113730161042016151412326627)
                  ·
                    refine ⟨170595241563024227118489941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113730161042016151412326627 170595241563024227118489941)
                    ·
                      refine ⟨499790746766672540386201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 170595241563024227118489941 499790746766672540386201)
                      ·
                        rfl

theorem cell23_973339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_973339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973339 prefixEnd_973339 := by exact prefixLift 973339
  have htrace : WordTrace (prefixWord ++ tailWord_973339) baseStart_973339 baseEnd_973339 := by
    simpa [prefixWord, tailWord_973339, baseEnd_973339] using wordTrace_append hprefix tailTrace_973339
  have hstable : (prefixWord ++ tailWord_973339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973339).length < 2 ^ (prefixWord ++ tailWord_973339).sum := by decide
  have hdescent : baseEnd_973339 < baseStart_973339 := by decide
  rcases family_descends (prefixWord ++ tailWord_973339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973340 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 6]
def baseStart_973340 : Nat := 118140960795 + 973340 * 2 ^ 59
def prefixEnd_973340 : Nat := 4983230072969 + 3 ^ 40 * 973340 * 2
def baseEnd_973340 : Nat := 55532362249703004052633

theorem tailTrace_973340 : CollatzResearch.WordTrace tailWord_973340 prefixEnd_973340 55532362249703004052633 := by
  unfold tailWord_973340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17750313146881444041302737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23667084195841925388403649 17750313146881444041302737)
  ·
    refine ⟨13312734860161083030977053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17750313146881444041302737 13312734860161083030977053)
    ·
      refine ⟨4992275572560406136616395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13312734860161083030977053 4992275572560406136616395)
      ·
        refine ⟨7488413358840609204924593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992275572560406136616395 7488413358840609204924593)
        ·
          refine ⟨5616310019130456903693445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7488413358840609204924593 5616310019130456903693445)
          ·
            refine ⟨1053058128586960669442521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5616310019130456903693445 1053058128586960669442521)
            ·
              refine ⟨789793596440220502081891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053058128586960669442521 789793596440220502081891)
              ·
                refine ⟨1184690394660330753122837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789793596440220502081891 1184690394660330753122837)
                ·
                  refine ⟨55532362249703004052633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1184690394660330753122837 55532362249703004052633)
                  ·
                    rfl

theorem cell23_973340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_973340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973340 prefixEnd_973340 := by exact prefixLift 973340
  have htrace : WordTrace (prefixWord ++ tailWord_973340) baseStart_973340 baseEnd_973340 := by
    simpa [prefixWord, tailWord_973340, baseEnd_973340] using wordTrace_append hprefix tailTrace_973340
  have hstable : (prefixWord ++ tailWord_973340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973340).length < 2 ^ (prefixWord ++ tailWord_973340).sum := by decide
  have hdescent : baseEnd_973340 < baseStart_973340 := by decide
  rcases family_descends (prefixWord ++ tailWord_973340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973343 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 6, 3, 2]
def baseStart_973343 : Nat := 118140960795 + 973343 * 2 ^ 59
def prefixEnd_973343 : Nat := 4983230072969 + 3 ^ 40 * 973343 * 2
def baseEnd_973343 : Nat := 499792800689290524736183

theorem tailTrace_973343 : CollatzResearch.WordTrace tailWord_973343 prefixEnd_973343 499792800689290524736183 := by
  unfold tailWord_973343
  simp only [CollatzResearch.WordTrace]
  refine ⟨35500735712752019594964683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23667157141834679729976455 35500735712752019594964683)
  ·
    refine ⟨53251103569128029392447025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35500735712752019594964683 53251103569128029392447025)
    ·
      refine ⟨39938327676846022044335269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53251103569128029392447025 39938327676846022044335269)
      ·
        refine ⟨7488436439408629133312863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39938327676846022044335269 7488436439408629133312863)
        ·
          refine ⟨11232654659112943699969295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7488436439408629133312863 11232654659112943699969295)
          ·
            refine ⟨16848981988669415549953943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11232654659112943699969295 16848981988669415549953943)
            ·
              refine ⟨25273472983004123324930915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16848981988669415549953943 25273472983004123324930915)
              ·
                refine ⟨37910209474506184987396373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25273472983004123324930915 37910209474506184987396373)
                ·
                  refine ⟨1777041069117477421284205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37910209474506184987396373 1777041069117477421284205)
                  ·
                    refine ⟨666390400919054032981577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777041069117477421284205 666390400919054032981577)
                    ·
                      refine ⟨499792800689290524736183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666390400919054032981577 499792800689290524736183)
                      ·
                        rfl

theorem cell23_973343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_973343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973343 prefixEnd_973343 := by exact prefixLift 973343
  have htrace : WordTrace (prefixWord ++ tailWord_973343) baseStart_973343 baseEnd_973343 := by
    simpa [prefixWord, tailWord_973343, baseEnd_973343] using wordTrace_append hprefix tailTrace_973343
  have hstable : (prefixWord ++ tailWord_973343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973343).length < 2 ^ (prefixWord ++ tailWord_973343).sum := by decide
  have hdescent : baseEnd_973343 < baseStart_973343 := by decide
  rcases family_descends (prefixWord ++ tailWord_973343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973370 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_973370 : Nat := 118140960795 + 973370 * 2 ^ 59
def prefixEnd_973370 : Nat := 4983230072969 + 3 ^ 40 * 973370 * 2
def baseEnd_973370 : Nat := 166602221555653973032853

theorem tailTrace_973370 : CollatzResearch.WordTrace tailWord_973370 prefixEnd_973370 166602221555653973032853 := by
  unfold tailWord_973370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8875430120913550801549391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23667813655769468804131709 8875430120913550801549391)
  ·
    refine ⟨13313145181370326202324087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8875430120913550801549391 13313145181370326202324087)
    ·
      refine ⟨19969717772055489303486131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13313145181370326202324087 19969717772055489303486131)
      ·
        refine ⟨29954576658083233955229197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19969717772055489303486131 29954576658083233955229197)
        ·
          refine ⟨11232966246781212733210949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29954576658083233955229197 11232966246781212733210949)
          ·
            refine ⟨2106181171271477387477053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11232966246781212733210949 2106181171271477387477053)
            ·
              refine ⟨789817939226804020303895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2106181171271477387477053 789817939226804020303895)
              ·
                refine ⟨1184726908840206030455843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789817939226804020303895 1184726908840206030455843)
                ·
                  refine ⟨1777090363260309045683765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184726908840206030455843 1777090363260309045683765)
                  ·
                    refine ⟨166602221555653973032853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1777090363260309045683765 166602221555653973032853)
                    ·
                      rfl

theorem cell23_973370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_973370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973370 prefixEnd_973370 := by exact prefixLift 973370
  have htrace : WordTrace (prefixWord ++ tailWord_973370) baseStart_973370 baseEnd_973370 := by
    simpa [prefixWord, tailWord_973370, baseEnd_973370] using wordTrace_append hprefix tailTrace_973370
  have hstable : (prefixWord ++ tailWord_973370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973370).length < 2 ^ (prefixWord ++ tailWord_973370).sum := by decide
  have hdescent : baseEnd_973370 < baseStart_973370 := by decide
  rcases family_descends (prefixWord ++ tailWord_973370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973393 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_973393 : Nat := 118140960795 + 973393 * 2 ^ 59
def prefixEnd_973393 : Nat := 4983230072969 + 3 ^ 40 * 973393 * 2
def baseEnd_973393 : Nat := 499818474722015329110953

theorem tailTrace_973393 : CollatzResearch.WordTrace tailWord_973393 prefixEnd_973393 499818474722015329110953 := by
  unfold tailWord_973393
  simp only [CollatzResearch.WordTrace]
  refine ⟨35502559362570878134284833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23668372908380585422856555 35502559362570878134284833)
  ·
    refine ⟨26626919521928158600713625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35502559362570878134284833 26626919521928158600713625)
    ·
      refine ⟨19970189641446118950535219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26626919521928158600713625 19970189641446118950535219)
      ·
        refine ⟨29955284462169178425802829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19970189641446118950535219 29955284462169178425802829)
        ·
          refine ⟨11233231673313441909676061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29955284462169178425802829 11233231673313441909676061)
          ·
            refine ⟨4212461877492540716128523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11233231673313441909676061 4212461877492540716128523)
            ·
              refine ⟨6318692816238811074192785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212461877492540716128523 6318692816238811074192785)
              ·
                refine ⟨4739019612179108305644589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6318692816238811074192785 4739019612179108305644589)
                ·
                  refine ⟨1777132354567165614616721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4739019612179108305644589 1777132354567165614616721)
                  ·
                    refine ⟨1332849265925374210962541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1777132354567165614616721 1332849265925374210962541)
                    ·
                      refine ⟨499818474722015329110953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1332849265925374210962541 499818474722015329110953)
                      ·
                        rfl

theorem cell23_973393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_973393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973393 prefixEnd_973393 := by exact prefixLift 973393
  have htrace : WordTrace (prefixWord ++ tailWord_973393) baseStart_973393 baseEnd_973393 := by
    simpa [prefixWord, tailWord_973393, baseEnd_973393] using wordTrace_append hprefix tailTrace_973393
  have hstable : (prefixWord ++ tailWord_973393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973393).length < 2 ^ (prefixWord ++ tailWord_973393).sum := by decide
  have hdescent : baseEnd_973393 < baseStart_973393 := by decide
  rcases family_descends (prefixWord ++ tailWord_973393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973423 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 3]
def baseStart_973423 : Nat := 118140960795 + 973423 * 2 ^ 59
def prefixEnd_973423 : Nat := 4983230072969 + 3 ^ 40 * 973423 * 2
def baseEnd_973423 : Nat := 499833879141650211735815

theorem tailTrace_973423 : CollatzResearch.WordTrace tailWord_973423 prefixEnd_973423 499833879141650211735815 := by
  unfold tailWord_973423
  simp only [CollatzResearch.WordTrace]
  refine ⟨35503653552462193257876923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23669102368308128838584615 35503653552462193257876923)
  ·
    refine ⟨53255480328693289886815385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35503653552462193257876923 53255480328693289886815385)
    ·
      refine ⟨39941610246519967415111539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53255480328693289886815385 39941610246519967415111539)
      ·
        refine ⟨59912415369779951122667309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39941610246519967415111539 59912415369779951122667309)
        ·
          refine ⟨22467155763667481671000241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59912415369779951122667309 22467155763667481671000241)
          ·
            refine ⟨16850366822750611253250181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22467155763667481671000241 16850366822750611253250181)
            ·
              refine ⟨3159443779265739609984409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16850366822750611253250181 3159443779265739609984409)
              ·
                refine ⟨2369582834449304707488307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159443779265739609984409 2369582834449304707488307)
                ·
                  refine ⟨3554374251673957061232461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369582834449304707488307 3554374251673957061232461)
                  ·
                    refine ⟨1332890344377733897962173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554374251673957061232461 1332890344377733897962173)
                    ·
                      refine ⟨499833879141650211735815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1332890344377733897962173 499833879141650211735815)
                      ·
                        rfl

theorem cell23_973423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_973423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973423 prefixEnd_973423 := by exact prefixLift 973423
  have htrace : WordTrace (prefixWord ++ tailWord_973423) baseStart_973423 baseEnd_973423 := by
    simpa [prefixWord, tailWord_973423, baseEnd_973423] using wordTrace_append hprefix tailTrace_973423
  have hstable : (prefixWord ++ tailWord_973423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973423).length < 2 ^ (prefixWord ++ tailWord_973423).sum := by decide
  have hdescent : baseEnd_973423 < baseStart_973423 := by decide
  rcases family_descends (prefixWord ++ tailWord_973423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973424 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 1, 1, 4]
def baseStart_973424 : Nat := 118140960795 + 973424 * 2 ^ 59
def prefixEnd_973424 : Nat := 4983230072969 + 3 ^ 40 * 973424 * 2
def baseEnd_973424 : Nat := 499834392622304707823311

theorem tailTrace_973424 : CollatzResearch.WordTrace tailWord_973424 prefixEnd_973424 499834392622304707823311 := by
  unfold tailWord_973424
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751845012729285214331663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23669126683639046952442217 17751845012729285214331663)
  ·
    refine ⟨26627767519093927821497495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17751845012729285214331663 26627767519093927821497495)
    ·
      refine ⟨39941651278640891732246243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26627767519093927821497495 39941651278640891732246243)
      ·
        refine ⟨59912476917961337598369365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39941651278640891732246243 59912476917961337598369365)
        ·
          refine ⟨702099338882359424980891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 59912476917961337598369365 702099338882359424980891)
          ·
            refine ⟨1053149008323539137471337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702099338882359424980891 1053149008323539137471337)
            ·
              refine ⟨789861756242654353103503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053149008323539137471337 789861756242654353103503)
              ·
                refine ⟨1184792634363981529655255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789861756242654353103503 1184792634363981529655255)
                ·
                  refine ⟨1777188951545972294482883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184792634363981529655255 1777188951545972294482883)
                  ·
                    refine ⟨2665783427318958441724325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1777188951545972294482883 2665783427318958441724325)
                    ·
                      refine ⟨499834392622304707823311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2665783427318958441724325 499834392622304707823311)
                      ·
                        rfl

theorem cell23_973424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 1, 4].length) (baseStart_973424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973424 prefixEnd_973424 := by exact prefixLift 973424
  have htrace : WordTrace (prefixWord ++ tailWord_973424) baseStart_973424 baseEnd_973424 := by
    simpa [prefixWord, tailWord_973424, baseEnd_973424] using wordTrace_append hprefix tailTrace_973424
  have hstable : (prefixWord ++ tailWord_973424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973424).length < 2 ^ (prefixWord ++ tailWord_973424).sum := by decide
  have hdescent : baseEnd_973424 < baseStart_973424 := by decide
  rcases family_descends (prefixWord ++ tailWord_973424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973440 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 4, 1, 3]
def baseStart_973440 : Nat := 118140960795 + 973440 * 2 ^ 59
def prefixEnd_973440 : Nat := 4983230072969 + 3 ^ 40 * 973440 * 2
def baseEnd_973440 : Nat := 499842608312776645223237

theorem tailTrace_973440 : CollatzResearch.WordTrace tailWord_973440 prefixEnd_973440 499842608312776645223237 := by
  unfold tailWord_973440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17752136796700302580622887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23669515728933736774163849 17752136796700302580622887)
  ·
    refine ⟨26628205195050453870934331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17752136796700302580622887 26628205195050453870934331)
    ·
      refine ⟨39942307792575680806401497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26628205195050453870934331 39942307792575680806401497)
      ·
        refine ⟨29956730844431760604801123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39942307792575680806401497 29956730844431760604801123)
        ·
          refine ⟨44935096266647640907201685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29956730844431760604801123 44935096266647640907201685)
          ·
            refine ⟨2106332637499108167525079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44935096266647640907201685 2106332637499108167525079)
            ·
              refine ⟨3159498956248662251287619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106332637499108167525079 3159498956248662251287619)
              ·
                refine ⟨4739248434372993376931429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159498956248662251287619 4739248434372993376931429)
                ·
                  refine ⟨888609081444936258174643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4739248434372993376931429 888609081444936258174643)
                  ·
                    refine ⟨1332913622167404387261965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888609081444936258174643 1332913622167404387261965)
                    ·
                      refine ⟨499842608312776645223237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1332913622167404387261965 499842608312776645223237)
                      ·
                        rfl

theorem cell23_973440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_973440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973440 prefixEnd_973440 := by exact prefixLift 973440
  have htrace : WordTrace (prefixWord ++ tailWord_973440) baseStart_973440 baseEnd_973440 := by
    simpa [prefixWord, tailWord_973440, baseEnd_973440] using wordTrace_append hprefix tailTrace_973440
  have hstable : (prefixWord ++ tailWord_973440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973440).length < 2 ^ (prefixWord ++ tailWord_973440).sum := by decide
  have hdescent : baseEnd_973440 < baseStart_973440 := by decide
  rcases family_descends (prefixWord ++ tailWord_973440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973497 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 2, 2, 2]
def baseStart_973497 : Nat := 118140960795 + 973497 * 2 ^ 59
def prefixEnd_973497 : Nat := 4983230072969 + 3 ^ 40 * 973497 * 2
def baseEnd_973497 : Nat := 499871876710082922210475

theorem tailTrace_973497 : CollatzResearch.WordTrace tailWord_973497 prefixEnd_973497 499871876710082922210475 := by
  unfold tailWord_973497
  simp only [CollatzResearch.WordTrace]
  refine ⟨35506352554194103896070745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23670901702796069264047163 35506352554194103896070745)
  ·
    refine ⟨26629764415645577922053059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35506352554194103896070745 26629764415645577922053059)
    ·
      refine ⟨39944646623468366883079589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26629764415645577922053059 39944646623468366883079589)
      ·
        refine ⟨7489621241900318790577423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39944646623468366883079589 7489621241900318790577423)
        ·
          refine ⟨11234431862850478185866135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489621241900318790577423 11234431862850478185866135)
          ·
            refine ⟨16851647794275717278799203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234431862850478185866135 16851647794275717278799203)
            ·
              refine ⟨25277471691413575918198805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851647794275717278799203 25277471691413575918198805)
              ·
                refine ⟨1184881485535011371165569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25277471691413575918198805 1184881485535011371165569)
                ·
                  refine ⟨888661114151258528374177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184881485535011371165569 888661114151258528374177)
                  ·
                    refine ⟨666495835613443896280633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 888661114151258528374177 666495835613443896280633)
                    ·
                      refine ⟨499871876710082922210475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666495835613443896280633 499871876710082922210475)
                      ·
                        rfl

theorem cell23_973497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_973497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973497 prefixEnd_973497 := by exact prefixLift 973497
  have htrace : WordTrace (prefixWord ++ tailWord_973497) baseStart_973497 baseEnd_973497 := by
    simpa [prefixWord, tailWord_973497, baseEnd_973497] using wordTrace_append hprefix tailTrace_973497
  have hstable : (prefixWord ++ tailWord_973497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973497).length < 2 ^ (prefixWord ++ tailWord_973497).sum := by decide
  have hdescent : baseEnd_973497 < baseStart_973497 := by decide
  rcases family_descends (prefixWord ++ tailWord_973497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973503 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 7]
def baseStart_973503 : Nat := 118140960795 + 973503 * 2 ^ 59
def prefixEnd_973503 : Nat := 4983230072969 + 3 ^ 40 * 973503 * 2
def baseEnd_973503 : Nat := 55541661954889988748383

theorem tailTrace_973503 : CollatzResearch.WordTrace tailWord_973503 prefixEnd_973503 55541661954889988748383 := by
  unfold tailWord_973503
  simp only [CollatzResearch.WordTrace]
  refine ⟨35506571392172366920789163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23671047594781577947192775 35506571392172366920789163)
  ·
    refine ⟨53259857088258550381183745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35506571392172366920789163 53259857088258550381183745)
    ·
      refine ⟨39944892816193912785887809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53259857088258550381183745 39944892816193912785887809)
      ·
        refine ⟨29958669612145434589415857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39944892816193912785887809 29958669612145434589415857)
        ·
          refine ⟨22469002209109075942061893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29958669612145434589415857 22469002209109075942061893)
          ·
            refine ⟨4212937914207951739136605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22469002209109075942061893 4212937914207951739136605)
            ·
              refine ⟨1579851717827981902176227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4212937914207951739136605 1579851717827981902176227)
              ·
                refine ⟨2369777576741972853264341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579851717827981902176227 2369777576741972853264341)
                ·
                  refine ⟨55541661954889988748383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2369777576741972853264341 55541661954889988748383)
                  ·
                    rfl

theorem cell23_973503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 7].length) (baseStart_973503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973503 prefixEnd_973503 := by exact prefixLift 973503
  have htrace : WordTrace (prefixWord ++ tailWord_973503) baseStart_973503 baseEnd_973503 := by
    simpa [prefixWord, tailWord_973503, baseEnd_973503] using wordTrace_append hprefix tailTrace_973503
  have hstable : (prefixWord ++ tailWord_973503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973503).length < 2 ^ (prefixWord ++ tailWord_973503).sum := by decide
  have hdescent : baseEnd_973503 < baseStart_973503 := by decide
  rcases family_descends (prefixWord ++ tailWord_973503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973514 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_973514 : Nat := 118140960795 + 973514 * 2 ^ 59
def prefixEnd_973514 : Nat := 4983230072969 + 3 ^ 40 * 973514 * 2
def baseEnd_973514 : Nat := 499880605881209355697897

theorem tailTrace_973514 : CollatzResearch.WordTrace tailWord_973514 prefixEnd_973514 499880605881209355697897 := by
  unfold tailWord_973514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8876743148783128949859899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23671315063421677199626397 8876743148783128949859899)
  ·
    refine ⟨13315114723174693424789849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8876743148783128949859899 13315114723174693424789849)
    ·
      refine ⟨9986336042381020068592387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13315114723174693424789849 9986336042381020068592387)
      ·
        refine ⟨14979504063571530102888581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9986336042381020068592387 14979504063571530102888581)
        ·
          refine ⟨2808657011919661894291609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14979504063571530102888581 2808657011919661894291609)
          ·
            refine ⟨2106492758939746420718707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2808657011919661894291609 2106492758939746420718707)
            ·
              refine ⟨3159739138409619631078061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106492758939746420718707 3159739138409619631078061)
              ·
                refine ⟨1184902176903607361654273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3159739138409619631078061 1184902176903607361654273)
                ·
                  refine ⟨888676632677705521240705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184902176903607361654273 888676632677705521240705)
                  ·
                    refine ⟨666507474508279140930529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 888676632677705521240705 666507474508279140930529)
                    ·
                      refine ⟨499880605881209355697897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666507474508279140930529 499880605881209355697897)
                      ·
                        rfl

theorem cell23_973514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_973514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973514 prefixEnd_973514 := by exact prefixLift 973514
  have htrace : WordTrace (prefixWord ++ tailWord_973514) baseStart_973514 baseEnd_973514 := by
    simpa [prefixWord, tailWord_973514, baseEnd_973514] using wordTrace_append hprefix tailTrace_973514
  have hstable : (prefixWord ++ tailWord_973514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973514).length < 2 ^ (prefixWord ++ tailWord_973514).sum := by decide
  have hdescent : baseEnd_973514 < baseStart_973514 := by decide
  rcases family_descends (prefixWord ++ tailWord_973514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973550 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_973550 : Nat := 118140960795 + 973550 * 2 ^ 59
def prefixEnd_973550 : Nat := 4983230072969 + 3 ^ 40 * 973550 * 2
def baseEnd_973550 : Nat := 166633030394923738282577

theorem tailTrace_973550 : CollatzResearch.WordTrace tailWord_973550 prefixEnd_973550 166633030394923738282577 := by
  unfold tailWord_973550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4438535702875261743468763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23672190415334729298500069 4438535702875261743468763)
  ·
    refine ⟨6657803554312892615203145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4438535702875261743468763 6657803554312892615203145)
    ·
      refine ⟨4993352665734669461402359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6657803554312892615203145 4993352665734669461402359)
      ·
        refine ⟨7490028998602004192103539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4993352665734669461402359 7490028998602004192103539)
        ·
          refine ⟨11235043497903006288155309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490028998602004192103539 11235043497903006288155309)
          ·
            refine ⟨4213141311713627358058241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11235043497903006288155309 4213141311713627358058241)
            ·
              refine ⟨3159855983785220518543681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213141311713627358058241 3159855983785220518543681)
              ·
                refine ⟨2369891987838915388907761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159855983785220518543681 2369891987838915388907761)
                ·
                  refine ⟨1777418990879186541680821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369891987838915388907761 1777418990879186541680821)
                  ·
                    refine ⟨166633030394923738282577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1777418990879186541680821 166633030394923738282577)
                    ·
                      rfl

theorem cell23_973550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_973550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973550 prefixEnd_973550 := by exact prefixLift 973550
  have htrace : WordTrace (prefixWord ++ tailWord_973550) baseStart_973550 baseEnd_973550 := by
    simpa [prefixWord, tailWord_973550, baseEnd_973550] using wordTrace_append hprefix tailTrace_973550
  have hstable : (prefixWord ++ tailWord_973550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973550).length < 2 ^ (prefixWord ++ tailWord_973550).sum := by decide
  have hdescent : baseEnd_973550 < baseStart_973550 := by decide
  rcases family_descends (prefixWord ++ tailWord_973550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973554 : List Nat := [3, 2, 1, 3, 1, 4, 2, 2, 5]
def baseStart_973554 : Nat := 118140960795 + 973554 * 2 ^ 59
def prefixEnd_973554 : Nat := 4983230072969 + 3 ^ 40 * 973554 * 2
def baseEnd_973554 : Nat := 55544571678598799910857

theorem tailTrace_973554 : CollatzResearch.WordTrace tailWord_973554 prefixEnd_973554 55544571678598799910857 := by
  unfold tailWord_973554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877107878746900657723929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23672287676658401753930477 8877107878746900657723929)
  ·
    refine ⟨6657830909060175493292947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8877107878746900657723929 6657830909060175493292947)
    ·
      refine ⟨9986746363590263239939421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6657830909060175493292947 9986746363590263239939421)
      ·
        refine ⟨3745029886346348714977283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9986746363590263239939421 3745029886346348714977283)
        ·
          refine ⟨5617544829519523072465925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745029886346348714977283 5617544829519523072465925)
          ·
            refine ⟨1053289655534910576087361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5617544829519523072465925 1053289655534910576087361)
            ·
              refine ⟨789967241651182932065521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053289655534910576087361 789967241651182932065521)
              ·
                refine ⟨592475431238387199049141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789967241651182932065521 592475431238387199049141)
                ·
                  refine ⟨55544571678598799910857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 592475431238387199049141 55544571678598799910857)
                  ·
                    rfl

theorem cell23_973554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_973554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973554 prefixEnd_973554 := by exact prefixLift 973554
  have htrace : WordTrace (prefixWord ++ tailWord_973554) baseStart_973554 baseEnd_973554 := by
    simpa [prefixWord, tailWord_973554, baseEnd_973554] using wordTrace_append hprefix tailTrace_973554
  have hstable : (prefixWord ++ tailWord_973554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973554).length < 2 ^ (prefixWord ++ tailWord_973554).sum := by decide
  have hdescent : baseEnd_973554 < baseStart_973554 := by decide
  rcases family_descends (prefixWord ++ tailWord_973554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973614 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_973614 : Nat := 118140960795 + 973614 * 2 ^ 59
def prefixEnd_973614 : Nat := 4983230072969 + 3 ^ 40 * 973614 * 2
def baseEnd_973614 : Nat := 166643984648886321482479

theorem tailTrace_973614 : CollatzResearch.WordTrace tailWord_973614 prefixEnd_973614 166643984648886321482479 := by
  unfold tailWord_973614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4438827486846279109759987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23673746596513488585386597 4438827486846279109759987)
  ·
    refine ⟨6658241230269418664639981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4438827486846279109759987 6658241230269418664639981)
    ·
      refine ⟨2496840461351031999239993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6658241230269418664639981 2496840461351031999239993)
      ·
        refine ⟨1872630346013273999429995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2496840461351031999239993 1872630346013273999429995)
        ·
          refine ⟨2808945519019910999144993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872630346013273999429995 2808945519019910999144993)
          ·
            refine ⟨2106709139264933249358745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2808945519019910999144993 2106709139264933249358745)
            ·
              refine ⟨1580031854448699937019059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106709139264933249358745 1580031854448699937019059)
              ·
                refine ⟨2370047781673049905528589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580031854448699937019059 2370047781673049905528589)
                ·
                  refine ⟨888767918127393714573221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2370047781673049905528589 888767918127393714573221)
                  ·
                    refine ⟨166643984648886321482479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888767918127393714573221 166643984648886321482479)
                    ·
                      rfl

theorem cell23_973614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_973614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973614 prefixEnd_973614 := by exact prefixLift 973614
  have htrace : WordTrace (prefixWord ++ tailWord_973614) baseStart_973614 baseEnd_973614 := by
    simpa [prefixWord, tailWord_973614, baseEnd_973614] using wordTrace_append hprefix tailTrace_973614
  have hstable : (prefixWord ++ tailWord_973614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973614).length < 2 ^ (prefixWord ++ tailWord_973614).sum := by decide
  have hdescent : baseEnd_973614 < baseStart_973614 := by decide
  rcases family_descends (prefixWord ++ tailWord_973614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973643 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4]
def baseStart_973643 : Nat := 118140960795 + 973643 * 2 ^ 59
def prefixEnd_973643 : Nat := 4983230072969 + 3 ^ 40 * 973643 * 2
def baseEnd_973643 : Nat := 499946844885639350984803

theorem tailTrace_973643 : CollatzResearch.WordTrace tailWord_973643 prefixEnd_973643 499946844885639350984803 := by
  unfold tailWord_973643
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511677611665170830885583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23674451741110113887257055 35511677611665170830885583)
  ·
    refine ⟨53267516417497756246328375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35511677611665170830885583 53267516417497756246328375)
    ·
      refine ⟨79901274626246634369492563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53267516417497756246328375 79901274626246634369492563)
      ·
        refine ⟨119851911939369951554238845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79901274626246634369492563 119851911939369951554238845)
        ·
          refine ⟨44944466977263731832839567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119851911939369951554238845 44944466977263731832839567)
          ·
            refine ⟨67416700465895597749259351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44944466977263731832839567 67416700465895597749259351)
            ·
              refine ⟨101125050698843396623889027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67416700465895597749259351 101125050698843396623889027)
              ·
                refine ⟨151687576048265094935833541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101125050698843396623889027 151687576048265094935833541)
                ·
                  refine ⟨28441420509049705300468789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151687576048265094935833541 28441420509049705300468789)
                  ·
                    refine ⟨2666383172723409871918949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28441420509049705300468789 2666383172723409871918949)
                    ·
                      refine ⟨499946844885639350984803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2666383172723409871918949 499946844885639350984803)
                      ·
                        rfl

theorem cell23_973643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_973643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973643 prefixEnd_973643 := by exact prefixLift 973643
  have htrace : WordTrace (prefixWord ++ tailWord_973643) baseStart_973643 baseEnd_973643 := by
    simpa [prefixWord, tailWord_973643, baseEnd_973643] using wordTrace_append hprefix tailTrace_973643
  have hstable : (prefixWord ++ tailWord_973643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973643).length < 2 ^ (prefixWord ++ tailWord_973643).sum := by decide
  have hdescent : baseEnd_973643 < baseStart_973643 := by decide
  rcases family_descends (prefixWord ++ tailWord_973643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973680 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_973680 : Nat := 118140960795 + 973680 * 2 ^ 59
def prefixEnd_973680 : Nat := 4983230072969 + 3 ^ 40 * 973680 * 2
def baseEnd_973680 : Nat := 499965843669855706222133

theorem tailTrace_973680 : CollatzResearch.WordTrace tailWord_973680 prefixEnd_973680 499965843669855706222133 := by
  unfold tailWord_973680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17756513556265563074991247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23675351408354084099988329 17756513556265563074991247)
  ·
    refine ⟨26634770334398344612486871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17756513556265563074991247 26634770334398344612486871)
    ·
      refine ⟨39952155501597516918730307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26634770334398344612486871 39952155501597516918730307)
      ·
        refine ⟨59928233252396275378095461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39952155501597516918730307 59928233252396275378095461)
        ·
          refine ⟨11236543734824301633392899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59928233252396275378095461 11236543734824301633392899)
          ·
            refine ⟨16854815602236452450089349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11236543734824301633392899 16854815602236452450089349)
            ·
              refine ⟨3160277925419334834391753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16854815602236452450089349 3160277925419334834391753)
              ·
                refine ⟨2370208444064501125793815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160277925419334834391753 2370208444064501125793815)
                ·
                  refine ⟨3555312666096751688690723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370208444064501125793815 3555312666096751688690723)
                  ·
                    refine ⟨5332968999145127533036085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3555312666096751688690723 5332968999145127533036085)
                    ·
                      refine ⟨499965843669855706222133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5332968999145127533036085 499965843669855706222133)
                      ·
                        rfl

theorem cell23_973680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_973680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973680 prefixEnd_973680 := by exact prefixLift 973680
  have htrace : WordTrace (prefixWord ++ tailWord_973680) baseStart_973680 baseEnd_973680 := by
    simpa [prefixWord, tailWord_973680, baseEnd_973680] using wordTrace_append hprefix tailTrace_973680
  have hstable : (prefixWord ++ tailWord_973680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973680).length < 2 ^ (prefixWord ++ tailWord_973680).sum := by decide
  have hdescent : baseEnd_973680 < baseStart_973680 := by decide
  rcases family_descends (prefixWord ++ tailWord_973680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973683 : List Nat := [1, 1, 1, 2, 2, 1, 5, 10]
def baseStart_973683 : Nat := 118140960795 + 973683 * 2 ^ 59
def prefixEnd_973683 : Nat := 4983230072969 + 3 ^ 40 * 973683 * 2
def baseEnd_973683 : Nat := 18517310522659970166097

theorem tailTrace_973683 : CollatzResearch.WordTrace tailWord_973683 prefixEnd_973683 18517310522659970166097 := by
  unfold tailWord_973683
  simp only [CollatzResearch.WordTrace]
  refine ⟨35513136531520257662341703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23675424354346838441561135 35513136531520257662341703)
  ·
    refine ⟨53269704797280386493512555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35513136531520257662341703 53269704797280386493512555)
    ·
      refine ⟨79904557195920579740268833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53269704797280386493512555 79904557195920579740268833)
      ·
        refine ⟨59928417896940434805201625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79904557195920579740268833 59928417896940434805201625)
        ·
          refine ⟨44946313422705326103901219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59928417896940434805201625 44946313422705326103901219)
          ·
            refine ⟨67419470134057989155851829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44946313422705326103901219 67419470134057989155851829)
            ·
              refine ⟨6320575325067936483361109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67419470134057989155851829 6320575325067936483361109)
              ·
                refine ⟨18517310522659970166097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6320575325067936483361109 18517310522659970166097)
                ·
                  rfl

theorem cell23_973683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 10].length) (baseStart_973683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973683 prefixEnd_973683 := by exact prefixLift 973683
  have htrace : WordTrace (prefixWord ++ tailWord_973683) baseStart_973683 baseEnd_973683 := by
    simpa [prefixWord, tailWord_973683, baseEnd_973683] using wordTrace_append hprefix tailTrace_973683
  have hstable : (prefixWord ++ tailWord_973683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973683).length < 2 ^ (prefixWord ++ tailWord_973683).sum := by decide
  have hdescent : baseEnd_973683 < baseStart_973683 := by decide
  rcases family_descends (prefixWord ++ tailWord_973683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973690 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_973690 : Nat := 118140960795 + 973690 * 2 ^ 59
def prefixEnd_973690 : Nat := 4983230072969 + 3 ^ 40 * 973690 * 2
def baseEnd_973690 : Nat := 499970978476400667097087

theorem tailTrace_973690 : CollatzResearch.WordTrace tailWord_973690 prefixEnd_973690 499970978476400667097087 := by
  unfold tailWord_973690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878347960623724464461631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23675594561663265238564349 8878347960623724464461631)
  ·
    refine ⟨13317521940935586696692447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8878347960623724464461631 13317521940935586696692447)
    ·
      refine ⟨19976282911403380045038671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13317521940935586696692447 19976282911403380045038671)
      ·
        refine ⟨29964424367105070067558007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19976282911403380045038671 29964424367105070067558007)
        ·
          refine ⟨44946636550657605101337011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29964424367105070067558007 44946636550657605101337011)
          ·
            refine ⟨67419954825986407652005517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44946636550657605101337011 67419954825986407652005517)
            ·
              refine ⟨25282483059744902869502069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67419954825986407652005517 25282483059744902869502069)
              ·
                refine ⟨2370232786851084644015819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25282483059744902869502069 2370232786851084644015819)
                ·
                  refine ⟨3555349180276626966023729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370232786851084644015819 3555349180276626966023729)
                  ·
                    refine ⟨2666511885207470224517797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3555349180276626966023729 2666511885207470224517797)
                    ·
                      refine ⟨499970978476400667097087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2666511885207470224517797 499970978476400667097087)
                      ·
                        rfl

theorem cell23_973690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_973690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973690 prefixEnd_973690 := by exact prefixLift 973690
  have htrace : WordTrace (prefixWord ++ tailWord_973690) baseStart_973690 baseEnd_973690 := by
    simpa [prefixWord, tailWord_973690, baseEnd_973690] using wordTrace_append hprefix tailTrace_973690
  have hstable : (prefixWord ++ tailWord_973690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973690).length < 2 ^ (prefixWord ++ tailWord_973690).sum := by decide
  have hdescent : baseEnd_973690 < baseStart_973690 := by decide
  rcases family_descends (prefixWord ++ tailWord_973690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973728 : List Nat := [2, 1, 1, 4, 1, 1, 6, 2, 1, 2, 2]
def baseStart_973728 : Nat := 118140960795 + 973728 * 2 ^ 59
def prefixEnd_973728 : Nat := 4983230072969 + 3 ^ 40 * 973728 * 2
def baseEnd_973728 : Nat := 499990490741271518421913

theorem tailTrace_973728 : CollatzResearch.WordTrace tailWord_973728 prefixEnd_973728 499990490741271518421913 := by
  unfold tailWord_973728
  simp only [CollatzResearch.WordTrace]
  refine ⟨17757388908178615173864919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23676518544238153565153225 17757388908178615173864919)
  ·
    refine ⟨26636083362267922760797379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17757388908178615173864919 26636083362267922760797379)
    ·
      refine ⟨39954125043401884141196069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26636083362267922760797379 39954125043401884141196069)
      ·
        refine ⟨7491398445637853276474263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39954125043401884141196069 7491398445637853276474263)
        ·
          refine ⟨11237097668456779914711395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7491398445637853276474263 11237097668456779914711395)
          ·
            refine ⟨16855646502685169872067093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237097668456779914711395 16855646502685169872067093)
            ·
              refine ⟨790108429813367337753145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16855646502685169872067093 790108429813367337753145)
              ·
                refine ⟨592581322360025503314859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790108429813367337753145 592581322360025503314859)
                ·
                  refine ⟨888871983540038254972289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592581322360025503314859 888871983540038254972289)
                  ·
                    refine ⟨666653987655028691229217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 888871983540038254972289 666653987655028691229217)
                    ·
                      refine ⟨499990490741271518421913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666653987655028691229217 499990490741271518421913)
                      ·
                        rfl

theorem cell23_973728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_973728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973728 prefixEnd_973728 := by exact prefixLift 973728
  have htrace : WordTrace (prefixWord ++ tailWord_973728) baseStart_973728 baseEnd_973728 := by
    simpa [prefixWord, tailWord_973728, baseEnd_973728] using wordTrace_append hprefix tailTrace_973728
  have hstable : (prefixWord ++ tailWord_973728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973728).length < 2 ^ (prefixWord ++ tailWord_973728).sum := by decide
  have hdescent : baseEnd_973728 < baseStart_973728 := by decide
  rcases family_descends (prefixWord ++ tailWord_973728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973737 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 5, 3, 2]
def baseStart_973737 : Nat := 118140960795 + 973737 * 2 ^ 59
def prefixEnd_973737 : Nat := 4983230072969 + 3 ^ 40 * 973737 * 2
def baseEnd_973737 : Nat := 499995112067161983209371

theorem tailTrace_973737 : CollatzResearch.WordTrace tailWord_973737 prefixEnd_973737 499995112067161983209371 := by
  unfold tailWord_973737
  simp only [CollatzResearch.WordTrace]
  refine ⟨35515106073324624884807465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23676737382216416589871643 35515106073324624884807465)
  ·
    refine ⟨26636329554993468663605599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35515106073324624884807465 26636329554993468663605599)
    ·
      refine ⟨39954494332490202995408399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26636329554993468663605599 39954494332490202995408399)
      ·
        refine ⟨59931741498735304493112599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39954494332490202995408399 59931741498735304493112599)
        ·
          refine ⟨89897612248102956739668899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59931741498735304493112599 89897612248102956739668899)
          ·
            refine ⟨134846418372154435109503349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89897612248102956739668899 134846418372154435109503349)
            ·
              refine ⟨12641851722389478291515939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134846418372154435109503349 12641851722389478291515939)
              ·
                refine ⟨18962777583584217437273909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12641851722389478291515939 18962777583584217437273909)
                ·
                  refine ⟨1777760398461020384744429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18962777583584217437273909 1777760398461020384744429)
                  ·
                    refine ⟨666660149422882644279161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777760398461020384744429 666660149422882644279161)
                    ·
                      refine ⟨499995112067161983209371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666660149422882644279161 499995112067161983209371)
                      ·
                        rfl

theorem cell23_973737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 3, 2].length) (baseStart_973737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973737 prefixEnd_973737 := by exact prefixLift 973737
  have htrace : WordTrace (prefixWord ++ tailWord_973737) baseStart_973737 baseEnd_973737 := by
    simpa [prefixWord, tailWord_973737, baseEnd_973737] using wordTrace_append hprefix tailTrace_973737
  have hstable : (prefixWord ++ tailWord_973737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973737).length < 2 ^ (prefixWord ++ tailWord_973737).sum := by decide
  have hdescent : baseEnd_973737 < baseStart_973737 := by decide
  rcases family_descends (prefixWord ++ tailWord_973737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973741 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_973741 : Nat := 118140960795 + 973741 * 2 ^ 59
def prefixEnd_973741 : Nat := 4983230072969 + 3 ^ 40 * 973741 * 2
def baseEnd_973741 : Nat := 499997165989779967559353

theorem tailTrace_973741 : CollatzResearch.WordTrace tailWord_973741 prefixEnd_973741 499997165989779967559353 := by
  unfold tailWord_973741
  simp only [CollatzResearch.WordTrace]
  refine ⟨35515251965310133567953077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23676834643540089045302051 35515251965310133567953077)
  ·
    refine ⟨3329554871747825021995601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35515251965310133567953077 3329554871747825021995601)
    ·
      refine ⟨2497166153810868766496701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3329554871747825021995601 2497166153810868766496701)
      ·
        refine ⟨936437307679075787436263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2497166153810868766496701 936437307679075787436263)
        ·
          refine ⟨1404655961518613681154395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936437307679075787436263 1404655961518613681154395)
          ·
            refine ⟨2106983942277920521731593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404655961518613681154395 2106983942277920521731593)
            ·
              refine ⟨1580237956708440391298695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106983942277920521731593 1580237956708440391298695)
              ·
                refine ⟨2370356935062660586948043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580237956708440391298695 2370356935062660586948043)
                ·
                  refine ⟨3555535402593990880422065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370356935062660586948043 3555535402593990880422065)
                  ·
                    refine ⟨2666651551945493160316549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3555535402593990880422065 2666651551945493160316549)
                    ·
                      refine ⟨499997165989779967559353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2666651551945493160316549 499997165989779967559353)
                      ·
                        rfl

theorem cell23_973741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_973741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973741 prefixEnd_973741 := by exact prefixLift 973741
  have htrace : WordTrace (prefixWord ++ tailWord_973741) baseStart_973741 baseEnd_973741 := by
    simpa [prefixWord, tailWord_973741, baseEnd_973741] using wordTrace_append hprefix tailTrace_973741
  have hstable : (prefixWord ++ tailWord_973741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973741).length < 2 ^ (prefixWord ++ tailWord_973741).sum := by decide
  have hdescent : baseEnd_973741 < baseStart_973741 := by decide
  rcases family_descends (prefixWord ++ tailWord_973741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973754 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2]
def baseStart_973754 : Nat := 118140960795 + 973754 * 2 ^ 59
def prefixEnd_973754 : Nat := 4983230072969 + 3 ^ 40 * 973754 * 2
def baseEnd_973754 : Nat := 500003841238288416696793

theorem tailTrace_973754 : CollatzResearch.WordTrace tailWord_973754 prefixEnd_973754 500003841238288416696793 := by
  unfold tailWord_973754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878931528565759197044079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23677150742842024525450877 8878931528565759197044079)
  ·
    refine ⟨13318397292848638795566119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8878931528565759197044079 13318397292848638795566119)
    ·
      refine ⟨19977595939272958193349179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13318397292848638795566119 19977595939272958193349179)
      ·
        refine ⟨29966393908909437290023769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19977595939272958193349179 29966393908909437290023769)
        ·
          refine ⟨22474795431682077967517827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29966393908909437290023769 22474795431682077967517827)
          ·
            refine ⟨33712193147523116951276741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22474795431682077967517827 33712193147523116951276741)
            ·
              refine ⟨6321036215160584428364389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33712193147523116951276741 6321036215160584428364389)
              ·
                refine ⟨1185194290342609580318323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6321036215160584428364389 1185194290342609580318323)
                ·
                  refine ⟨1777791435513914370477485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185194290342609580318323 1777791435513914370477485)
                  ·
                    refine ⟨666671788317717888929057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777791435513914370477485 666671788317717888929057)
                    ·
                      refine ⟨500003841238288416696793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666671788317717888929057 500003841238288416696793)
                      ·
                        rfl

theorem cell23_973754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_973754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973754 prefixEnd_973754 := by exact prefixLift 973754
  have htrace : WordTrace (prefixWord ++ tailWord_973754) baseStart_973754 baseEnd_973754 := by
    simpa [prefixWord, tailWord_973754, baseEnd_973754] using wordTrace_append hprefix tailTrace_973754
  have hstable : (prefixWord ++ tailWord_973754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973754).length < 2 ^ (prefixWord ++ tailWord_973754).sum := by decide
  have hdescent : baseEnd_973754 < baseStart_973754 := by decide
  rcases family_descends (prefixWord ++ tailWord_973754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973770 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_973770 : Nat := 118140960795 + 973770 * 2 ^ 59
def prefixEnd_973770 : Nat := 4983230072969 + 3 ^ 40 * 973770 * 2
def baseEnd_973770 : Nat := 500012056928760354096719

theorem tailTrace_973770 : CollatzResearch.WordTrace tailWord_973770 prefixEnd_973770 500012056928760354096719 := by
  unfold tailWord_973770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8879077420551267880189691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23677539788136714347172509 8879077420551267880189691)
  ·
    refine ⟨13318616130826901820284537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8879077420551267880189691 13318616130826901820284537)
    ·
      refine ⟨9988962098120176365213403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13318616130826901820284537 9988962098120176365213403)
      ·
        refine ⟨14983443147180264547820105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988962098120176365213403 14983443147180264547820105)
        ·
          refine ⟨11237582360385198410865079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14983443147180264547820105 11237582360385198410865079)
          ·
            refine ⟨16856373540577797616297619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237582360385198410865079 16856373540577797616297619)
            ·
              refine ⟨25284560310866696424446429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16856373540577797616297619 25284560310866696424446429)
              ·
                refine ⟨9481710116575011159167411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25284560310866696424446429 9481710116575011159167411)
                ·
                  refine ⟨14222565174862516738751117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9481710116575011159167411 14222565174862516738751117)
                  ·
                    refine ⟨5333461940573443777031669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14222565174862516738751117 5333461940573443777031669)
                    ·
                      refine ⟨500012056928760354096719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5333461940573443777031669 500012056928760354096719)
                      ·
                        rfl

theorem cell23_973770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_973770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973770 prefixEnd_973770 := by exact prefixLift 973770
  have htrace : WordTrace (prefixWord ++ tailWord_973770) baseStart_973770 baseEnd_973770 := by
    simpa [prefixWord, tailWord_973770, baseEnd_973770] using wordTrace_append hprefix tailTrace_973770
  have hstable : (prefixWord ++ tailWord_973770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973770).length < 2 ^ (prefixWord ++ tailWord_973770).sum := by decide
  have hdescent : baseEnd_973770 < baseStart_973770 := by decide
  rcases family_descends (prefixWord ++ tailWord_973770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973771 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 1, 3, 2]
def baseStart_973771 : Nat := 118140960795 + 973771 * 2 ^ 59
def prefixEnd_973771 : Nat := 4983230072969 + 3 ^ 40 * 973771 * 2
def baseEnd_973771 : Nat := 500012570409414850184215

theorem tailTrace_973771 : CollatzResearch.WordTrace tailWord_973771 prefixEnd_973771 500012570409414850184215 := by
  unfold tailWord_973771
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516346155201448691545167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23677564103467632461030111 35516346155201448691545167)
  ·
    refine ⟨53274519232802173037317751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35516346155201448691545167 53274519232802173037317751)
    ·
      refine ⟨79911778849203259555976627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53274519232802173037317751 79911778849203259555976627)
      ·
        refine ⟨119867668273804889333964941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79911778849203259555976627 119867668273804889333964941)
        ·
          refine ⟨44950375602676833500236853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119867668273804889333964941 44950375602676833500236853)
          ·
            refine ⟨4214097712750953140647205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44950375602676833500236853 4214097712750953140647205)
            ·
              refine ⟨790143321140803713871351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4214097712750953140647205 790143321140803713871351)
              ·
                refine ⟨1185214981711205570807027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790143321140803713871351 1185214981711205570807027)
                ·
                  refine ⟨1777822472566808356210541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185214981711205570807027 1777822472566808356210541)
                  ·
                    refine ⟨666683427212553133578953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1777822472566808356210541 666683427212553133578953)
                    ·
                      refine ⟨500012570409414850184215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666683427212553133578953 500012570409414850184215)
                      ·
                        rfl

theorem cell23_973771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 3, 2].length) (baseStart_973771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973771 prefixEnd_973771 := by exact prefixLift 973771
  have htrace : WordTrace (prefixWord ++ tailWord_973771) baseStart_973771 baseEnd_973771 := by
    simpa [prefixWord, tailWord_973771, baseEnd_973771] using wordTrace_append hprefix tailTrace_973771
  have hstable : (prefixWord ++ tailWord_973771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973771).length < 2 ^ (prefixWord ++ tailWord_973771).sum := by decide
  have hdescent : baseEnd_973771 < baseStart_973771 := by decide
  rcases family_descends (prefixWord ++ tailWord_973771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973778 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_973778 : Nat := 118140960795 + 973778 * 2 ^ 59
def prefixEnd_973778 : Nat := 4983230072969 + 3 ^ 40 * 973778 * 2
def baseEnd_973778 : Nat := 500016164773996322796683

theorem tailTrace_973778 : CollatzResearch.WordTrace tailWord_973778 prefixEnd_973778 500016164773996322796683 := by
  unfold tailWord_973778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8879150366544022221762497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23677734310784059258033325 8879150366544022221762497)
  ·
    refine ⟨6659362774908016666321873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8879150366544022221762497 6659362774908016666321873)
    ·
      refine ⟨4994522081181012499741405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6659362774908016666321873 4994522081181012499741405)
      ·
        refine ⟨1872945780442879687403027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4994522081181012499741405 1872945780442879687403027)
        ·
          refine ⟨2809418670664319531104541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872945780442879687403027 2809418670664319531104541)
          ·
            refine ⟨1053532001499119824164203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2809418670664319531104541 1053532001499119824164203)
            ·
              refine ⟨1580298002248679736246305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053532001499119824164203 1580298002248679736246305)
              ·
                refine ⟨1185223501686509802184729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580298002248679736246305 1185223501686509802184729)
                ·
                  refine ⟨888917626264882351638547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185223501686509802184729 888917626264882351638547)
                  ·
                    refine ⟨1333376439397323527457821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 888917626264882351638547 1333376439397323527457821)
                    ·
                      refine ⟨500016164773996322796683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1333376439397323527457821 500016164773996322796683)
                      ·
                        rfl

theorem cell23_973778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_973778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973778 prefixEnd_973778 := by exact prefixLift 973778
  have htrace : WordTrace (prefixWord ++ tailWord_973778) baseStart_973778 baseEnd_973778 := by
    simpa [prefixWord, tailWord_973778, baseEnd_973778] using wordTrace_append hprefix tailTrace_973778
  have hstable : (prefixWord ++ tailWord_973778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973778).length < 2 ^ (prefixWord ++ tailWord_973778).sum := by decide
  have hdescent : baseEnd_973778 < baseStart_973778 := by decide
  rcases family_descends (prefixWord ++ tailWord_973778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973794 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_973794 : Nat := 118140960795 + 973794 * 2 ^ 59
def prefixEnd_973794 : Nat := 4983230072969 + 3 ^ 40 * 973794 * 2
def baseEnd_973794 : Nat := 166674793488156086732203

theorem tailTrace_973794 : CollatzResearch.WordTrace tailWord_973794 prefixEnd_973794 166674793488156086732203 := by
  unfold tailWord_973794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8879296258529530904908109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23678123356078749079754957 8879296258529530904908109)
  ·
    refine ⟨3329736096948574089340541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8879296258529530904908109 3329736096948574089340541)
    ·
      refine ⟨1248651036355715283502703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3329736096948574089340541 1248651036355715283502703)
      ·
        refine ⟨1872976554533572925254055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248651036355715283502703 1872976554533572925254055)
        ·
          refine ⟨2809464831800359387881083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872976554533572925254055 2809464831800359387881083)
          ·
            refine ⟨4214197247700539081821625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809464831800359387881083 4214197247700539081821625)
            ·
              refine ⟨3160647935775404311366219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214197247700539081821625 3160647935775404311366219)
              ·
                refine ⟨4740971903663106467049329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160647935775404311366219 4740971903663106467049329)
                ·
                  refine ⟨3555728927747329850286997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4740971903663106467049329 3555728927747329850286997)
                  ·
                    refine ⟨166674793488156086732203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3555728927747329850286997 166674793488156086732203)
                    ·
                      rfl

theorem cell23_973794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_973794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973794 prefixEnd_973794 := by exact prefixLift 973794
  have htrace : WordTrace (prefixWord ++ tailWord_973794) baseStart_973794 baseEnd_973794 := by
    simpa [prefixWord, tailWord_973794, baseEnd_973794] using wordTrace_append hprefix tailTrace_973794
  have hstable : (prefixWord ++ tailWord_973794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973794).length < 2 ^ (prefixWord ++ tailWord_973794).sum := by decide
  have hdescent : baseEnd_973794 < baseStart_973794 := by decide
  rcases family_descends (prefixWord ++ tailWord_973794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973827 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 7, 2]
def baseStart_973827 : Nat := 118140960795 + 973827 * 2 ^ 59
def prefixEnd_973827 : Nat := 4983230072969 + 3 ^ 40 * 973827 * 2
def baseEnd_973827 : Nat := 500041325326066631083957

theorem tailTrace_973827 : CollatzResearch.WordTrace tailWord_973827 prefixEnd_973827 500041325326066631083957 := by
  unfold tailWord_973827
  simp only [CollatzResearch.WordTrace]
  refine ⟨35518388642998570255583735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23678925761999046837055823 35518388642998570255583735)
  ·
    refine ⟨53277582964497855383375603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35518388642998570255583735 53277582964497855383375603)
    ·
      refine ⟨79916374446746783075063405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53277582964497855383375603 79916374446746783075063405)
      ·
        refine ⟨29968640417530043653148777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79916374446746783075063405 29968640417530043653148777)
        ·
          refine ⟨22476480313147532739861583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29968640417530043653148777 22476480313147532739861583)
          ·
            refine ⟨33714720469721299109792375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22476480313147532739861583 33714720469721299109792375)
            ·
              refine ⟨50572080704581948664688563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33714720469721299109792375 50572080704581948664688563)
              ·
                refine ⟨75858121056872922997032845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50572080704581948664688563 75858121056872922997032845)
                ·
                  refine ⟨28446795396327346123887317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75858121056872922997032845 28446795396327346123887317)
                  ·
                    refine ⟨666721767101422174778609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28446795396327346123887317 666721767101422174778609)
                    ·
                      refine ⟨500041325326066631083957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666721767101422174778609 500041325326066631083957)
                      ·
                        rfl

theorem cell23_973827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_973827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973827 prefixEnd_973827 := by exact prefixLift 973827
  have htrace : WordTrace (prefixWord ++ tailWord_973827) baseStart_973827 baseEnd_973827 := by
    simpa [prefixWord, tailWord_973827, baseEnd_973827] using wordTrace_append hprefix tailTrace_973827
  have hstable : (prefixWord ++ tailWord_973827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973827).length < 2 ^ (prefixWord ++ tailWord_973827).sum := by decide
  have hdescent : baseEnd_973827 < baseStart_973827 := by decide
  rcases family_descends (prefixWord ++ tailWord_973827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973847 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_973847 : Nat := 118140960795 + 973847 * 2 ^ 59
def prefixEnd_973847 : Nat := 4983230072969 + 3 ^ 40 * 973847 * 2
def baseEnd_973847 : Nat := 500051594939156552833865

theorem tailTrace_973847 : CollatzResearch.WordTrace tailWord_973847 prefixEnd_973847 500051594939156552833865 := by
  unfold tailWord_973847
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519118102926113671311795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23679412068617409114207863 35519118102926113671311795)
  ·
    refine ⟨53278677154389170506967693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35519118102926113671311795 53278677154389170506967693)
    ·
      refine ⟨19979503932895938940112885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53278677154389170506967693 19979503932895938940112885)
      ·
        refine ⟨1873078493708994275635583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19979503932895938940112885 1873078493708994275635583)
        ·
          refine ⟨2809617740563491413453375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873078493708994275635583 2809617740563491413453375)
          ·
            refine ⟨4214426610845237120180063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809617740563491413453375 4214426610845237120180063)
            ·
              refine ⟨6321639916267855680270095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214426610845237120180063 6321639916267855680270095)
              ·
                refine ⟨9482459874401783520405143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321639916267855680270095 9482459874401783520405143)
                ·
                  refine ⟨14223689811602675280607715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9482459874401783520405143 14223689811602675280607715)
                  ·
                    refine ⟨21335534717404012920911573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14223689811602675280607715 21335534717404012920911573)
                    ·
                      refine ⟨500051594939156552833865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21335534717404012920911573 500051594939156552833865)
                      ·
                        rfl

theorem cell23_973847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_973847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973847 prefixEnd_973847 := by exact prefixLift 973847
  have htrace : WordTrace (prefixWord ++ tailWord_973847) baseStart_973847 baseEnd_973847 := by
    simpa [prefixWord, tailWord_973847, baseEnd_973847] using wordTrace_append hprefix tailTrace_973847
  have hstable : (prefixWord ++ tailWord_973847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973847).length < 2 ^ (prefixWord ++ tailWord_973847).sum := by decide
  have hdescent : baseEnd_973847 < baseStart_973847 := by decide
  rcases family_descends (prefixWord ++ tailWord_973847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973852 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_973852 : Nat := 118140960795 + 973852 * 2 ^ 59
def prefixEnd_973852 : Nat := 4983230072969 + 3 ^ 40 * 973852 * 2
def baseEnd_973852 : Nat := 500054162342429033271343

theorem tailTrace_973852 : CollatzResearch.WordTrace tailWord_973852 prefixEnd_973852 500054162342429033271343 := by
  unfold tailWord_973852
  simp only [CollatzResearch.WordTrace]
  refine ⟨17759650233953999762621905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23679533645271999683495873 17759650233953999762621905)
  ·
    refine ⟨13319737675465499821966429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17759650233953999762621905 13319737675465499821966429)
    ·
      refine ⟨4994901628299562433237411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13319737675465499821966429 4994901628299562433237411)
      ·
        refine ⟨7492352442449343649856117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994901628299562433237411 7492352442449343649856117)
        ·
          refine ⟨702408041479625967174011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7492352442449343649856117 702408041479625967174011)
          ·
            refine ⟨1053612062219438950761017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702408041479625967174011 1053612062219438950761017)
            ·
              refine ⟨790209046664579213070763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053612062219438950761017 790209046664579213070763)
              ·
                refine ⟨1185313569996868819606145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790209046664579213070763 1185313569996868819606145)
                ·
                  refine ⟨888985177497651614704609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185313569996868819606145 888985177497651614704609)
                  ·
                    refine ⟨666738883123238711028457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 888985177497651614704609 666738883123238711028457)
                    ·
                      refine ⟨500054162342429033271343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666738883123238711028457 500054162342429033271343)
                      ·
                        rfl

theorem cell23_973852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_973852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973852 prefixEnd_973852 := by exact prefixLift 973852
  have htrace : WordTrace (prefixWord ++ tailWord_973852) baseStart_973852 baseEnd_973852 := by
    simpa [prefixWord, tailWord_973852, baseEnd_973852] using wordTrace_append hprefix tailTrace_973852
  have hstable : (prefixWord ++ tailWord_973852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973852).length < 2 ^ (prefixWord ++ tailWord_973852).sum := by decide
  have hdescent : baseEnd_973852 < baseStart_973852 := by decide
  rcases family_descends (prefixWord ++ tailWord_973852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973867 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 5, 4]
def baseStart_973867 : Nat := 118140960795 + 973867 * 2 ^ 59
def prefixEnd_973867 : Nat := 4983230072969 + 3 ^ 40 * 973867 * 2
def baseEnd_973867 : Nat := 166687288184082158194591

theorem tailTrace_973867 : CollatzResearch.WordTrace tailWord_973867 prefixEnd_973867 166687288184082158194591 := by
  unfold tailWord_973867
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519847562853657087039855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23679898375235771391359903 35519847562853657087039855)
  ·
    refine ⟨53279771344280485630559783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35519847562853657087039855 53279771344280485630559783)
    ·
      refine ⟨79919657016420728445839675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53279771344280485630559783 79919657016420728445839675)
      ·
        refine ⟨119879485524631092668759513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79919657016420728445839675 119879485524631092668759513)
        ·
          refine ⟨89909614143473319501569635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119879485524631092668759513 89909614143473319501569635)
          ·
            refine ⟨134864421215209979252354453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89909614143473319501569635 134864421215209979252354453)
            ·
              refine ⟨6321769744462967777454115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134864421215209979252354453 6321769744462967777454115)
              ·
                refine ⟨9482654616694451666181173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321769744462967777454115 9482654616694451666181173)
                ·
                  refine ⟨888998870315104843704485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9482654616694451666181173 888998870315104843704485)
                  ·
                    refine ⟨166687288184082158194591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888998870315104843704485 166687288184082158194591)
                    ·
                      rfl

theorem cell23_973867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 4].length) (baseStart_973867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973867 prefixEnd_973867 := by exact prefixLift 973867
  have htrace : WordTrace (prefixWord ++ tailWord_973867) baseStart_973867 baseEnd_973867 := by
    simpa [prefixWord, tailWord_973867, baseEnd_973867] using wordTrace_append hprefix tailTrace_973867
  have hstable : (prefixWord ++ tailWord_973867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973867).length < 2 ^ (prefixWord ++ tailWord_973867).sum := by decide
  have hdescent : baseEnd_973867 < baseStart_973867 := by decide
  rcases family_descends (prefixWord ++ tailWord_973867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973874 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_973874 : Nat := 118140960795 + 973874 * 2 ^ 59
def prefixEnd_973874 : Nat := 4983230072969 + 3 ^ 40 * 973874 * 2
def baseEnd_973874 : Nat := 500065458916827947196241

theorem tailTrace_973874 : CollatzResearch.WordTrace tailWord_973874 prefixEnd_973874 500065458916827947196241 := by
  unfold tailWord_973874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880025718457074320636169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23680068582552198188363117 8880025718457074320636169)
  ·
    refine ⟨6660019288842805740477127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8880025718457074320636169 6660019288842805740477127)
    ·
      refine ⟨9990028933264208610715691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660019288842805740477127 9990028933264208610715691)
      ·
        refine ⟨14985043399896312916073537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990028933264208610715691 14985043399896312916073537)
        ·
          refine ⟨11238782549922234687055153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14985043399896312916073537 11238782549922234687055153)
          ·
            refine ⟨8429086912441676015291365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11238782549922234687055153 8429086912441676015291365)
            ·
              refine ⟨1580453796082814252867131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8429086912441676015291365 1580453796082814252867131)
              ·
                refine ⟨2370680694124221379300697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580453796082814252867131 2370680694124221379300697)
                ·
                  refine ⟨1778010520593166034475523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2370680694124221379300697 1778010520593166034475523)
                  ·
                    refine ⟨2667015780889749051713285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1778010520593166034475523 2667015780889749051713285)
                    ·
                      refine ⟨500065458916827947196241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2667015780889749051713285 500065458916827947196241)
                      ·
                        rfl

theorem cell23_973874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_973874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973874 prefixEnd_973874 := by exact prefixLift 973874
  have htrace : WordTrace (prefixWord ++ tailWord_973874) baseStart_973874 baseEnd_973874 := by
    simpa [prefixWord, tailWord_973874, baseEnd_973874] using wordTrace_append hprefix tailTrace_973874
  have hstable : (prefixWord ++ tailWord_973874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973874).length < 2 ^ (prefixWord ++ tailWord_973874).sum := by decide
  have hdescent : baseEnd_973874 < baseStart_973874 := by decide
  rcases family_descends (prefixWord ++ tailWord_973874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973918 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_973918 : Nat := 118140960795 + 973918 * 2 ^ 59
def prefixEnd_973918 : Nat := 4983230072969 + 3 ^ 40 * 973918 * 2
def baseEnd_973918 : Nat := 166696017355208591682013

theorem tailTrace_973918 : CollatzResearch.WordTrace tailWord_973918 prefixEnd_973918 166696017355208591682013 := by
  unfold tailWord_973918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440213460708611599643301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23681138457112595198097605 4440213460708611599643301)
  ·
    refine ⟨832540023882864674933119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4440213460708611599643301 832540023882864674933119)
    ·
      refine ⟨1248810035824297012399679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832540023882864674933119 1248810035824297012399679)
      ·
        refine ⟨1873215053736445518599519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248810035824297012399679 1873215053736445518599519)
        ·
          refine ⟨2809822580604668277899279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873215053736445518599519 2809822580604668277899279)
          ·
            refine ⟨4214733870907002416848919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809822580604668277899279 4214733870907002416848919)
            ·
              refine ⟨6322100806360503625273379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214733870907002416848919 6322100806360503625273379)
              ·
                refine ⟨9483151209540755437910069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6322100806360503625273379 9483151209540755437910069)
                ·
                  refine ⟨889045425894445822304069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9483151209540755437910069 889045425894445822304069)
                  ·
                    refine ⟨166696017355208591682013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889045425894445822304069 166696017355208591682013)
                    ·
                      rfl

theorem cell23_973918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_973918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973918 prefixEnd_973918 := by exact prefixLift 973918
  have htrace : WordTrace (prefixWord ++ tailWord_973918) baseStart_973918 baseEnd_973918 := by
    simpa [prefixWord, tailWord_973918, baseEnd_973918] using wordTrace_append hprefix tailTrace_973918
  have hstable : (prefixWord ++ tailWord_973918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973918).length < 2 ^ (prefixWord ++ tailWord_973918).sum := by decide
  have hdescent : baseEnd_973918 < baseStart_973918 := by decide
  rcases family_descends (prefixWord ++ tailWord_973918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973981 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_973981 : Nat := 118140960795 + 973981 * 2 ^ 59
def prefixEnd_973981 : Nat := 4983230072969 + 3 ^ 40 * 973981 * 2
def baseEnd_973981 : Nat := 500120401346859028558249

theorem tailTrace_973981 : CollatzResearch.WordTrace tailWord_973981 prefixEnd_973981 500120401346859028558249 := by
  unfold tailWord_973981
  simp only [CollatzResearch.WordTrace]
  refine ⟨35524005484440654556689797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23682670322960436371126531 35524005484440654556689797)
  ·
    refine ⟨6660751028332622729379337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35524005484440654556689797 6660751028332622729379337)
    ·
      refine ⟨4995563271249467047034503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6660751028332622729379337 4995563271249467047034503)
      ·
        refine ⟨7493344906874200570551755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4995563271249467047034503 7493344906874200570551755)
        ·
          refine ⟨11240017360311300855827633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7493344906874200570551755 11240017360311300855827633)
          ·
            refine ⟨8430013020233475641870725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11240017360311300855827633 8430013020233475641870725)
            ·
              refine ⟨1580627441293776682850761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8430013020233475641870725 1580627441293776682850761)
              ·
                refine ⟨1185470580970332512138071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580627441293776682850761 1185470580970332512138071)
                ·
                  refine ⟨1778205871455498768207107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185470580970332512138071 1778205871455498768207107)
                  ·
                    refine ⟨2667308807183248152310661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1778205871455498768207107 2667308807183248152310661)
                    ·
                      refine ⟨500120401346859028558249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2667308807183248152310661 500120401346859028558249)
                      ·
                        rfl

theorem cell23_973981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_973981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973981 prefixEnd_973981 := by exact prefixLift 973981
  have htrace : WordTrace (prefixWord ++ tailWord_973981) baseStart_973981 baseEnd_973981 := by
    simpa [prefixWord, tailWord_973981, baseEnd_973981] using wordTrace_append hprefix tailTrace_973981
  have hstable : (prefixWord ++ tailWord_973981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973981).length < 2 ^ (prefixWord ++ tailWord_973981).sum := by decide
  have hdescent : baseEnd_973981 < baseStart_973981 := by decide
  rcases family_descends (prefixWord ++ tailWord_973981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973991 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 4, 4]
def baseStart_973991 : Nat := 118140960795 + 973991 * 2 ^ 59
def prefixEnd_973991 : Nat := 4983230072969 + 3 ^ 40 * 973991 * 2
def baseEnd_973991 : Nat := 166708512051134663144401

theorem tailTrace_973991 : CollatzResearch.WordTrace tailWord_973991 prefixEnd_973991 166708512051134663144401 := by
  unfold tailWord_973991
  simp only [CollatzResearch.WordTrace]
  refine ⟨35524370214404426264553827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23682913476269617509702551 35524370214404426264553827)
  ·
    refine ⟨53286555321606639396830741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35524370214404426264553827 53286555321606639396830741)
    ·
      refine ⟨2497807280700311221726441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53286555321606639396830741 2497807280700311221726441)
      ·
        refine ⟨1873355460525233416294831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2497807280700311221726441 1873355460525233416294831)
        ·
          refine ⟨2810033190787850124442247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873355460525233416294831 2810033190787850124442247)
          ·
            refine ⟨4215049786181775186663371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810033190787850124442247 4215049786181775186663371)
            ·
              refine ⟨6322574679272662779995057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4215049786181775186663371 6322574679272662779995057)
              ·
                refine ⟨4741931009454497084996293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6322574679272662779995057 4741931009454497084996293)
                ·
                  refine ⟨889112064272718203436805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4741931009454497084996293 889112064272718203436805)
                  ·
                    refine ⟨166708512051134663144401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889112064272718203436805 166708512051134663144401)
                    ·
                      rfl

theorem cell23_973991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_973991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_973991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_973991 prefixEnd_973991 := by exact prefixLift 973991
  have htrace : WordTrace (prefixWord ++ tailWord_973991) baseStart_973991 baseEnd_973991 := by
    simpa [prefixWord, tailWord_973991, baseEnd_973991] using wordTrace_append hprefix tailTrace_973991
  have hstable : (prefixWord ++ tailWord_973991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973991).length < 2 ^ (prefixWord ++ tailWord_973991).sum := by decide
  have hdescent : baseEnd_973991 < baseStart_973991 := by decide
  rcases family_descends (prefixWord ++ tailWord_973991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974001 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_974001 : Nat := 118140960795 + 974001 * 2 ^ 59
def prefixEnd_974001 : Nat := 4983230072969 + 3 ^ 40 * 974001 * 2
def baseEnd_974001 : Nat := 500130670959948950308157

theorem tailTrace_974001 : CollatzResearch.WordTrace tailWord_974001 prefixEnd_974001 500130670959948950308157 := by
  unfold tailWord_974001
  simp only [CollatzResearch.WordTrace]
  refine ⟨35524734944368197972417857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23683156629578798648278571 35524734944368197972417857)
  ·
    refine ⟨26643551208276148479313393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35524734944368197972417857 26643551208276148479313393)
    ·
      refine ⟨19982663406207111359485045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26643551208276148479313393 19982663406207111359485045)
      ·
        refine ⟨1873374694331916689951723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19982663406207111359485045 1873374694331916689951723)
        ·
          refine ⟨2810062041497875034927585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873374694331916689951723 2810062041497875034927585)
          ·
            refine ⟨2107546531123406276195689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2810062041497875034927585 2107546531123406276195689)
            ·
              refine ⟨1580659898342554707146767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107546531123406276195689 1580659898342554707146767)
              ·
                refine ⟨2370989847513832060720151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580659898342554707146767 2370989847513832060720151)
                ·
                  refine ⟨3556484771270748091080227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370989847513832060720151 3556484771270748091080227)
                  ·
                    refine ⟨5334727156906122136620341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3556484771270748091080227 5334727156906122136620341)
                    ·
                      refine ⟨500130670959948950308157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5334727156906122136620341 500130670959948950308157)
                      ·
                        rfl

theorem cell23_974001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_974001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974001 prefixEnd_974001 := by exact prefixLift 974001
  have htrace : WordTrace (prefixWord ++ tailWord_974001) baseStart_974001 baseEnd_974001 := by
    simpa [prefixWord, tailWord_974001, baseEnd_974001] using wordTrace_append hprefix tailTrace_974001
  have hstable : (prefixWord ++ tailWord_974001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974001).length < 2 ^ (prefixWord ++ tailWord_974001).sum := by decide
  have hdescent : baseEnd_974001 < baseStart_974001 := by decide
  rcases family_descends (prefixWord ++ tailWord_974001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974027 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5]
def baseStart_974027 : Nat := 118140960795 + 974027 * 2 ^ 59
def prefixEnd_974027 : Nat := 4983230072969 + 3 ^ 40 * 974027 * 2
def baseEnd_974027 : Nat := 500144021456965848583037

theorem tailTrace_974027 : CollatzResearch.WordTrace tailWord_974027 prefixEnd_974027 500144021456965848583037 := by
  unfold tailWord_974027
  simp only [CollatzResearch.WordTrace]
  refine ⟨35525683242274004412864335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23683788828182669608576223 35525683242274004412864335)
  ·
    refine ⟨53288524863411006619296503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35525683242274004412864335 53288524863411006619296503)
    ·
      refine ⟨79932787295116509928944755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53288524863411006619296503 79932787295116509928944755)
      ·
        refine ⟨119899180942674764893417133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79932787295116509928944755 119899180942674764893417133)
        ·
          refine ⟨44962192853503036835031425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119899180942674764893417133 44962192853503036835031425)
          ·
            refine ⟨33721644640127277626273569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44962192853503036835031425 33721644640127277626273569)
            ·
              refine ⟨25291233480095458219705177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33721644640127277626273569 25291233480095458219705177)
              ·
                refine ⟨18968425110071593664778883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25291233480095458219705177 18968425110071593664778883)
                ·
                  refine ⟨28452637665107390497168325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18968425110071593664778883 28452637665107390497168325)
                  ·
                    refine ⟨5334869562207635718219061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28452637665107390497168325 5334869562207635718219061)
                    ·
                      refine ⟨500144021456965848583037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5334869562207635718219061 500144021456965848583037)
                      ·
                        rfl

theorem cell23_974027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_974027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974027 prefixEnd_974027 := by exact prefixLift 974027
  have htrace : WordTrace (prefixWord ++ tailWord_974027) baseStart_974027 baseEnd_974027 := by
    simpa [prefixWord, tailWord_974027, baseEnd_974027] using wordTrace_append hprefix tailTrace_974027
  have hstable : (prefixWord ++ tailWord_974027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974027).length < 2 ^ (prefixWord ++ tailWord_974027).sum := by decide
  have hdescent : baseEnd_974027 < baseStart_974027 := by decide
  rcases family_descends (prefixWord ++ tailWord_974027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974066 : List Nat := [3, 2, 1, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_974066 : Nat := 118140960795 + 974066 * 2 ^ 59
def prefixEnd_974066 : Nat := 4983230072969 + 3 ^ 40 * 974066 * 2
def baseEnd_974066 : Nat := 500164047202491195995359

theorem tailTrace_974066 : CollatzResearch.WordTrace tailWord_974066 prefixEnd_974066 500164047202491195995359 := by
  unfold tailWord_974066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881776422283178518383513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23684737126088476049022701 8881776422283178518383513)
  ·
    refine ⟨6661332316712383888787635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8881776422283178518383513 6661332316712383888787635)
    ·
      refine ⟨9991998475068575833181453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661332316712383888787635 9991998475068575833181453)
      ·
        refine ⟨3746999428150715937443045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9991998475068575833181453 3746999428150715937443045)
        ·
          refine ⟨702562392778259238270571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3746999428150715937443045 702562392778259238270571)
          ·
            refine ⟨1053843589167388857405857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702562392778259238270571 1053843589167388857405857)
            ·
              refine ⟨790382691875541643054393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053843589167388857405857 790382691875541643054393)
              ·
                refine ⟨592787018906656232290795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790382691875541643054393 592787018906656232290795)
                ·
                  refine ⟨889180528359984348436193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592787018906656232290795 889180528359984348436193)
                  ·
                    refine ⟨666885396269988261327145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 889180528359984348436193 666885396269988261327145)
                    ·
                      refine ⟨500164047202491195995359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666885396269988261327145 500164047202491195995359)
                      ·
                        rfl

theorem cell23_974066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_974066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974066 prefixEnd_974066 := by exact prefixLift 974066
  have htrace : WordTrace (prefixWord ++ tailWord_974066) baseStart_974066 baseEnd_974066 := by
    simpa [prefixWord, tailWord_974066, baseEnd_974066] using wordTrace_append hprefix tailTrace_974066
  have hstable : (prefixWord ++ tailWord_974066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974066).length < 2 ^ (prefixWord ++ tailWord_974066).sum := by decide
  have hdescent : baseEnd_974066 < baseStart_974066 := by decide
  rcases family_descends (prefixWord ++ tailWord_974066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974074 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_974074 : Nat := 118140960795 + 974074 * 2 ^ 59
def prefixEnd_974074 : Nat := 4983230072969 + 3 ^ 40 * 974074 * 2
def baseEnd_974074 : Nat := 500168155047727164695321

theorem tailTrace_974074 : CollatzResearch.WordTrace tailWord_974074 prefixEnd_974074 500168155047727164695321 := by
  unfold tailWord_974074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881849368275932859956319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23684931648735820959883517 8881849368275932859956319)
  ·
    refine ⟨13322774052413899289934479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8881849368275932859956319 13322774052413899289934479)
    ·
      refine ⟨19984161078620848934901719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13322774052413899289934479 19984161078620848934901719)
      ·
        refine ⟨29976241617931273402352579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19984161078620848934901719 29976241617931273402352579)
        ·
          refine ⟨44964362426896910103528869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29976241617931273402352579 44964362426896910103528869)
          ·
            refine ⟨8430817955043170644411663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44964362426896910103528869 8430817955043170644411663)
            ·
              refine ⟨12646226932564755966617495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8430817955043170644411663 12646226932564755966617495)
              ·
                refine ⟨18969340398847133949926243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12646226932564755966617495 18969340398847133949926243)
                ·
                  refine ⟨28454010598270700924889365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18969340398847133949926243 28454010598270700924889365)
                  ·
                    refine ⟨1333781746793939105854189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28454010598270700924889365 1333781746793939105854189)
                    ·
                      refine ⟨500168155047727164695321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1333781746793939105854189 500168155047727164695321)
                      ·
                        rfl

theorem cell23_974074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_974074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974074 prefixEnd_974074 := by exact prefixLift 974074
  have htrace : WordTrace (prefixWord ++ tailWord_974074) baseStart_974074 baseEnd_974074 := by
    simpa [prefixWord, tailWord_974074, baseEnd_974074] using wordTrace_append hprefix tailTrace_974074
  have hstable : (prefixWord ++ tailWord_974074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974074).length < 2 ^ (prefixWord ++ tailWord_974074).sum := by decide
  have hdescent : baseEnd_974074 < baseStart_974074 := by decide
  rcases family_descends (prefixWord ++ tailWord_974074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974094 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_974094 : Nat := 118140960795 + 974094 * 2 ^ 59
def prefixEnd_974094 : Nat := 4983230072969 + 3 ^ 40 * 974094 * 2
def baseEnd_974094 : Nat := 55575380517868565160581

theorem tailTrace_974094 : CollatzResearch.WordTrace tailWord_974094 prefixEnd_974094 55575380517868565160581 := by
  unfold tailWord_974094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441015866628909356944167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23685417955354183237035557 4441015866628909356944167)
  ·
    refine ⟨6661523799943364035416251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4441015866628909356944167 6661523799943364035416251)
    ·
      refine ⟨9992285699915046053124377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661523799943364035416251 9992285699915046053124377)
      ·
        refine ⟨7494214274936284539843283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9992285699915046053124377 7494214274936284539843283)
        ·
          refine ⟨11241321412404426809764925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7494214274936284539843283 11241321412404426809764925)
          ·
            refine ⟨4215495529651660053661847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11241321412404426809764925 4215495529651660053661847)
            ·
              refine ⟨6323243294477490080492771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4215495529651660053661847 6323243294477490080492771)
              ·
                refine ⟨9484864941716235120739157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323243294477490080492771 9484864941716235120739157)
                ·
                  refine ⟨55575380517868565160581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9484864941716235120739157 55575380517868565160581)
                  ·
                    rfl

theorem cell23_974094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_974094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974094 prefixEnd_974094 := by exact prefixLift 974094
  have htrace : WordTrace (prefixWord ++ tailWord_974094) baseStart_974094 baseEnd_974094 := by
    simpa [prefixWord, tailWord_974094, baseEnd_974094] using wordTrace_append hprefix tailTrace_974094
  have hstable : (prefixWord ++ tailWord_974094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974094).length < 2 ^ (prefixWord ++ tailWord_974094).sum := by decide
  have hdescent : baseEnd_974094 < baseStart_974094 := by decide
  rcases family_descends (prefixWord ++ tailWord_974094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974122 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_974122 : Nat := 118140960795 + 974122 * 2 ^ 59
def prefixEnd_974122 : Nat := 4983230072969 + 3 ^ 40 * 974122 * 2
def baseEnd_974122 : Nat := 500192802119142976895101

theorem tailTrace_974122 : CollatzResearch.WordTrace tailWord_974122 prefixEnd_974122 500192802119142976895101 := by
  unfold tailWord_974122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882287044232458909393155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23686098784619890425048413 8882287044232458909393155)
  ·
    refine ⟨13323430566348688364089733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8882287044232458909393155 13323430566348688364089733)
    ·
      refine ⟨2498143231190379068266825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13323430566348688364089733 2498143231190379068266825)
      ·
        refine ⟨1873607423392784301200119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2498143231190379068266825 1873607423392784301200119)
        ·
          refine ⟨2810411135089176451800179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873607423392784301200119 2810411135089176451800179)
          ·
            refine ⟨4215616702633764677700269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810411135089176451800179 4215616702633764677700269)
            ·
              refine ⟨1580856263487661754137601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4215616702633764677700269 1580856263487661754137601)
              ·
                refine ⟨1185642197615746315603201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580856263487661754137601 1185642197615746315603201)
                ·
                  refine ⟨889231648211809736702401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185642197615746315603201 889231648211809736702401)
                  ·
                    refine ⟨666923736158857302526801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 889231648211809736702401 666923736158857302526801)
                    ·
                      refine ⟨500192802119142976895101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 666923736158857302526801 500192802119142976895101)
                      ·
                        rfl

theorem cell23_974122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_974122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974122 prefixEnd_974122 := by exact prefixLift 974122
  have htrace : WordTrace (prefixWord ++ tailWord_974122) baseStart_974122 baseEnd_974122 := by
    simpa [prefixWord, tailWord_974122, baseEnd_974122] using wordTrace_append hprefix tailTrace_974122
  have hstable : (prefixWord ++ tailWord_974122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974122).length < 2 ^ (prefixWord ++ tailWord_974122).sum := by decide
  have hdescent : baseEnd_974122 < baseStart_974122 := by decide
  rcases family_descends (prefixWord ++ tailWord_974122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974124 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_974124 : Nat := 118140960795 + 974124 * 2 ^ 59
def prefixEnd_974124 : Nat := 4983230072969 + 3 ^ 40 * 974124 * 2
def baseEnd_974124 : Nat := 166731276360150656356697

theorem tailTrace_974124 : CollatzResearch.WordTrace tailWord_974124 prefixEnd_974124 166731276360150656356697 := by
  unfold tailWord_974124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764610561461294989572713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23686147415281726652763617 17764610561461294989572713)
  ·
    refine ⟨13323457921095971242179535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17764610561461294989572713 13323457921095971242179535)
    ·
      refine ⟨19985186881643956863269303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13323457921095971242179535 19985186881643956863269303)
      ·
        refine ⟨29977780322465935294903955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19985186881643956863269303 29977780322465935294903955)
        ·
          refine ⟨44966670483698902942355933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29977780322465935294903955 44966670483698902942355933)
          ·
            refine ⟨16862501431387088603383475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44966670483698902942355933 16862501431387088603383475)
            ·
              refine ⟨25293752147080632905075213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16862501431387088603383475 25293752147080632905075213)
              ·
                refine ⟨9485157055155237339403205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25293752147080632905075213 9485157055155237339403205)
                ·
                  refine ⟨1778466947841607001138101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9485157055155237339403205 1778466947841607001138101)
                  ·
                    refine ⟨166731276360150656356697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1778466947841607001138101 166731276360150656356697)
                    ·
                      rfl

theorem cell23_974124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_974124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974124 prefixEnd_974124 := by exact prefixLift 974124
  have htrace : WordTrace (prefixWord ++ tailWord_974124) baseStart_974124 baseEnd_974124 := by
    simpa [prefixWord, tailWord_974124, baseEnd_974124] using wordTrace_append hprefix tailTrace_974124
  have hstable : (prefixWord ++ tailWord_974124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974124).length < 2 ^ (prefixWord ++ tailWord_974124).sum := by decide
  have hdescent : baseEnd_974124 < baseStart_974124 := by decide
  rcases family_descends (prefixWord ++ tailWord_974124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974144 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_974144 : Nat := 118140960795 + 974144 * 2 ^ 59
def prefixEnd_974144 : Nat := 4983230072969 + 3 ^ 40 * 974144 * 2
def baseEnd_974144 : Nat := 500204098693541890819999

theorem tailTrace_974144 : CollatzResearch.WordTrace tailWord_974144 prefixEnd_974144 500204098693541890819999 := by
  unfold tailWord_974144
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764975291425066697436743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23686633721900088929915657 17764975291425066697436743)
  ·
    refine ⟨26647462937137600046155115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17764975291425066697436743 26647462937137600046155115)
    ·
      refine ⟨39971194405706400069232673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26647462937137600046155115 39971194405706400069232673)
      ·
        refine ⟨29978395804279800051924505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39971194405706400069232673 29978395804279800051924505)
        ·
          refine ⟨22483796853209850038943379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29978395804279800051924505 22483796853209850038943379)
          ·
            refine ⟨33725695279814775058415069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22483796853209850038943379 33725695279814775058415069)
            ·
              refine ⟨12647135729930540646905651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33725695279814775058415069 12647135729930540646905651)
              ·
                refine ⟨18970703594895810970358477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12647135729930540646905651 18970703594895810970358477)
                ·
                  refine ⟨7114013848085929113884429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18970703594895810970358477 7114013848085929113884429)
                  ·
                    refine ⟨2667755193032223417706661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7114013848085929113884429 2667755193032223417706661)
                    ·
                      refine ⟨500204098693541890819999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2667755193032223417706661 500204098693541890819999)
                      ·
                        rfl

theorem cell23_974144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_974144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974144 prefixEnd_974144 := by exact prefixLift 974144
  have htrace : WordTrace (prefixWord ++ tailWord_974144) baseStart_974144 baseEnd_974144 := by
    simpa [prefixWord, tailWord_974144, baseEnd_974144] using wordTrace_append hprefix tailTrace_974144
  have hstable : (prefixWord ++ tailWord_974144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974144).length < 2 ^ (prefixWord ++ tailWord_974144).sum := by decide
  have hdescent : baseEnd_974144 < baseStart_974144 := by decide
  rcases family_descends (prefixWord ++ tailWord_974144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974161 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_974161 : Nat := 118140960795 + 974161 * 2 ^ 59
def prefixEnd_974161 : Nat := 4983230072969 + 3 ^ 40 * 974161 * 2
def baseEnd_974161 : Nat := 500212827864668324307421

theorem tailTrace_974161 : CollatzResearch.WordTrace tailWord_974161 prefixEnd_974161 500212827864668324307421 := by
  unfold tailWord_974161
  simp only [CollatzResearch.WordTrace]
  refine ⟨35530570623788545298242337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23687047082525696865494891 35530570623788545298242337)
  ·
    refine ⟨26647927967841408973681753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35530570623788545298242337 26647927967841408973681753)
    ·
      refine ⟨19985945975881056730261315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26647927967841408973681753 19985945975881056730261315)
      ·
        refine ⟨29978918963821585095391973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19985945975881056730261315 29978918963821585095391973)
        ·
          refine ⟨5621047305716547205385995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29978918963821585095391973 5621047305716547205385995)
          ·
            refine ⟨8431570958574820808078993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621047305716547205385995 8431570958574820808078993)
            ·
              refine ⟨6323678218931115606059245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8431570958574820808078993 6323678218931115606059245)
              ·
                refine ⟨2371379332099168352272217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6323678218931115606059245 2371379332099168352272217)
                ·
                  refine ⟨1778534499074376264204163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2371379332099168352272217 1778534499074376264204163)
                  ·
                    refine ⟨2667801748611564396306245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1778534499074376264204163 2667801748611564396306245)
                    ·
                      refine ⟨500212827864668324307421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2667801748611564396306245 500212827864668324307421)
                      ·
                        rfl

theorem cell23_974161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_974161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974161 prefixEnd_974161 := by exact prefixLift 974161
  have htrace : WordTrace (prefixWord ++ tailWord_974161) baseStart_974161 baseEnd_974161 := by
    simpa [prefixWord, tailWord_974161, baseEnd_974161] using wordTrace_append hprefix tailTrace_974161
  have hstable : (prefixWord ++ tailWord_974161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974161).length < 2 ^ (prefixWord ++ tailWord_974161).sum := by decide
  have hdescent : baseEnd_974161 < baseStart_974161 := by decide
  rcases family_descends (prefixWord ++ tailWord_974161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974178 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_974178 : Nat := 118140960795 + 974178 * 2 ^ 59
def prefixEnd_974178 : Nat := 4983230072969 + 3 ^ 40 * 974178 * 2
def baseEnd_974178 : Nat := 500221557035794757794843

theorem tailTrace_974178 : CollatzResearch.WordTrace tailWord_974178 prefixEnd_974178 500221557035794757794843 := by
  unfold tailWord_974178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882797666181739300402797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23687460443151304801074125 8882797666181739300402797)
  ·
    refine ⟨3331049124818152237651049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8882797666181739300402797 3331049124818152237651049)
    ·
      refine ⟨2498286843613614178238287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3331049124818152237651049 2498286843613614178238287)
      ·
        refine ⟨3747430265420421267357431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498286843613614178238287 3747430265420421267357431)
        ·
          refine ⟨5621145398130631901036147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747430265420421267357431 5621145398130631901036147)
          ·
            refine ⟨8431718097195947851554221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621145398130631901036147 8431718097195947851554221)
            ·
              refine ⟨3161894286448480444332833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8431718097195947851554221 3161894286448480444332833)
              ·
                refine ⟨2371420714836360333249625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161894286448480444332833 2371420714836360333249625)
                ·
                  refine ⟨1778565536127270249937219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2371420714836360333249625 1778565536127270249937219)
                  ·
                    refine ⟨2667848304190905374905829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1778565536127270249937219 2667848304190905374905829)
                    ·
                      refine ⟨500221557035794757794843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2667848304190905374905829 500221557035794757794843)
                      ·
                        rfl

theorem cell23_974178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_974178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974178 prefixEnd_974178 := by exact prefixLift 974178
  have htrace : WordTrace (prefixWord ++ tailWord_974178) baseStart_974178 baseEnd_974178 := by
    simpa [prefixWord, tailWord_974178, baseEnd_974178] using wordTrace_append hprefix tailTrace_974178
  have hstable : (prefixWord ++ tailWord_974178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974178).length < 2 ^ (prefixWord ++ tailWord_974178).sum := by decide
  have hdescent : baseEnd_974178 < baseStart_974178 := by decide
  rcases family_descends (prefixWord ++ tailWord_974178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974188 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_974188 : Nat := 118140960795 + 974188 * 2 ^ 59
def prefixEnd_974188 : Nat := 4983230072969 + 3 ^ 40 * 974188 * 2
def baseEnd_974188 : Nat := 166742230614113239556599

theorem tailTrace_974188 : CollatzResearch.WordTrace tailWord_974188 prefixEnd_974188 166742230614113239556599 := by
  unfold tailWord_974188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17765777697345364454737609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23687703596460485939650145 17765777697345364454737609)
  ·
    refine ⟨13324333273009023341053207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17765777697345364454737609 13324333273009023341053207)
    ·
      refine ⟨19986499909513535011579811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13324333273009023341053207 19986499909513535011579811)
      ·
        refine ⟨29979749864270302517369717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19986499909513535011579811 29979749864270302517369717)
        ·
          refine ⟨2810601549775340861003411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29979749864270302517369717 2810601549775340861003411)
          ·
            refine ⟨4215902324663011291505117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810601549775340861003411 4215902324663011291505117)
            ·
              refine ⟨1580963371748629234314419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4215902324663011291505117 1580963371748629234314419)
              ·
                refine ⟨2371445057622943851471629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580963371748629234314419 2371445057622943851471629)
                ·
                  refine ⟨889291896608603944301861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2371445057622943851471629 889291896608603944301861)
                  ·
                    refine ⟨166742230614113239556599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889291896608603944301861 166742230614113239556599)
                    ·
                      rfl

theorem cell23_974188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_974188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974188 prefixEnd_974188 := by exact prefixLift 974188
  have htrace : WordTrace (prefixWord ++ tailWord_974188) baseStart_974188 baseEnd_974188 := by
    simpa [prefixWord, tailWord_974188, baseEnd_974188] using wordTrace_append hprefix tailTrace_974188
  have hstable : (prefixWord ++ tailWord_974188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974188).length < 2 ^ (prefixWord ++ tailWord_974188).sum := by decide
  have hdescent : baseEnd_974188 < baseStart_974188 := by decide
  rcases family_descends (prefixWord ++ tailWord_974188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974288 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3]
def baseStart_974288 : Nat := 118140960795 + 974288 * 2 ^ 59
def prefixEnd_974288 : Nat := 4983230072969 + 3 ^ 40 * 974288 * 2
def baseEnd_974288 : Nat := 500278039907789327419337

theorem tailTrace_974288 : CollatzResearch.WordTrace tailWord_974288 prefixEnd_974288 500278039907789327419337 := by
  unfold tailWord_974288
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767601347164222994057759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23690135129552297325410345 17767601347164222994057759)
  ·
    refine ⟨26651402020746334491086639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17767601347164222994057759 26651402020746334491086639)
    ·
      refine ⟨39977103031119501736629959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26651402020746334491086639 39977103031119501736629959)
      ·
        refine ⟨59965654546679252604944939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39977103031119501736629959 59965654546679252604944939)
        ·
          refine ⟨89948481820018878907417409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59965654546679252604944939 89948481820018878907417409)
          ·
            refine ⟨67461361365014159180563057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89948481820018878907417409 67461361365014159180563057)
            ·
              refine ⟨50596021023760619385422293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67461361365014159180563057 50596021023760619385422293)
              ·
                refine ⟨1185844242744389516845835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50596021023760619385422293 1185844242744389516845835)
                ·
                  refine ⟨1778766364116584275268753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185844242744389516845835 1778766364116584275268753)
                  ·
                    refine ⟨1334074773087438206451565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1778766364116584275268753 1334074773087438206451565)
                    ·
                      refine ⟨500278039907789327419337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1334074773087438206451565 500278039907789327419337)
                      ·
                        rfl

theorem cell23_974288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_974288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974288 prefixEnd_974288 := by exact prefixLift 974288
  have htrace : WordTrace (prefixWord ++ tailWord_974288) baseStart_974288 baseEnd_974288 := by
    simpa [prefixWord, tailWord_974288, baseEnd_974288] using wordTrace_append hprefix tailTrace_974288
  have hstable : (prefixWord ++ tailWord_974288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974288).length < 2 ^ (prefixWord ++ tailWord_974288).sum := by decide
  have hdescent : baseEnd_974288 < baseStart_974288 := by decide
  rcases family_descends (prefixWord ++ tailWord_974288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974322 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_974322 : Nat := 118140960795 + 974322 * 2 ^ 59
def prefixEnd_974322 : Nat := 4983230072969 + 3 ^ 40 * 974322 * 2
def baseEnd_974322 : Nat := 500295498250042194394181

theorem tailTrace_974322 : CollatzResearch.WordTrace tailWord_974322 prefixEnd_974322 500295498250042194394181 := by
  unfold tailWord_974322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8884110694051317448713305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23690961850803513196568813 8884110694051317448713305)
  ·
    refine ⟨6663083020538488086534979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8884110694051317448713305 6663083020538488086534979)
    ·
      refine ⟨9994624530807732129802469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6663083020538488086534979 9994624530807732129802469)
      ·
        refine ⟨1873992099526449774337963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9994624530807732129802469 1873992099526449774337963)
        ·
          refine ⟨2810988149289674661506945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873992099526449774337963 2810988149289674661506945)
          ·
            refine ⟨2108241111967255996130209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2810988149289674661506945 2108241111967255996130209)
            ·
              refine ⟨1581180833975441997097657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108241111967255996130209 1581180833975441997097657)
              ·
                refine ⟨1185885625481581497823243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581180833975441997097657 1185885625481581497823243)
                ·
                  refine ⟨1778828438222372246734865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185885625481581497823243 1778828438222372246734865)
                  ·
                    refine ⟨1334121328666779185051149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1778828438222372246734865 1334121328666779185051149)
                    ·
                      refine ⟨500295498250042194394181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1334121328666779185051149 500295498250042194394181)
                      ·
                        rfl

theorem cell23_974322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_974322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974322 prefixEnd_974322 := by exact prefixLift 974322
  have htrace : WordTrace (prefixWord ++ tailWord_974322) baseStart_974322 baseEnd_974322 := by
    simpa [prefixWord, tailWord_974322, baseEnd_974322] using wordTrace_append hprefix tailTrace_974322
  have hstable : (prefixWord ++ tailWord_974322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974322).length < 2 ^ (prefixWord ++ tailWord_974322).sum := by decide
  have hdescent : baseEnd_974322 < baseStart_974322 := by decide
  rcases family_descends (prefixWord ++ tailWord_974322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974325 : List Nat := [1, 3, 5, 1, 1, 1, 4, 7]
def baseStart_974325 : Nat := 118140960795 + 974325 * 2 ^ 59
def prefixEnd_974325 : Nat := 4983230072969 + 3 ^ 40 * 974325 * 2
def baseEnd_974325 : Nat := 18529519951555766024321

theorem tailTrace_974325 : CollatzResearch.WordTrace tailWord_974325 prefixEnd_974325 18529519951555766024321 := by
  unfold tailWord_974325
  simp only [CollatzResearch.WordTrace]
  refine ⟨35536552195194401307212429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23691034796796267538141619 35536552195194401307212429)
  ·
    refine ⟨13326207073197900490204661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35536552195194401307212429 13326207073197900490204661)
    ·
      refine ⟨1249331913112303170956687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13326207073197900490204661 1249331913112303170956687)
      ·
        refine ⟨1873997869668454756435031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249331913112303170956687 1873997869668454756435031)
        ·
          refine ⟨2810996804502682134652547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873997869668454756435031 2810996804502682134652547)
          ·
            refine ⟨4216495206754023201978821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810996804502682134652547 4216495206754023201978821)
            ·
              refine ⟨790592851266379350371029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4216495206754023201978821 790592851266379350371029)
              ·
                refine ⟨18529519951555766024321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 790592851266379350371029 18529519951555766024321)
                ·
                  rfl

theorem cell23_974325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 7].length) (baseStart_974325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974325 prefixEnd_974325 := by exact prefixLift 974325
  have htrace : WordTrace (prefixWord ++ tailWord_974325) baseStart_974325 baseEnd_974325 := by
    simpa [prefixWord, tailWord_974325, baseEnd_974325] using wordTrace_append hprefix tailTrace_974325
  have hstable : (prefixWord ++ tailWord_974325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974325).length < 2 ^ (prefixWord ++ tailWord_974325).sum := by decide
  have hdescent : baseEnd_974325 < baseStart_974325 := by decide
  rcases family_descends (prefixWord ++ tailWord_974325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974341 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_974341 : Nat := 118140960795 + 974341 * 2 ^ 59
def prefixEnd_974341 : Nat := 4983230072969 + 3 ^ 40 * 974341 * 2
def baseEnd_974341 : Nat := 500305254382477620056593

theorem tailTrace_974341 : CollatzResearch.WordTrace tailWord_974341 prefixEnd_974341 500305254382477620056593 := by
  unfold tailWord_974341
  simp only [CollatzResearch.WordTrace]
  refine ⟨35537135763136436039794877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23691423842090957359863251 35537135763136436039794877)
  ·
    refine ⟨13326425911176163514923079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35537135763136436039794877 13326425911176163514923079)
    ·
      refine ⟨19989638866764245272384619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13326425911176163514923079 19989638866764245272384619)
      ·
        refine ⟨29984458300146367908576929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19989638866764245272384619 29984458300146367908576929)
        ·
          refine ⟨22488343725109775931432697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29984458300146367908576929 22488343725109775931432697)
          ·
            refine ⟨16866257793832331948574523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22488343725109775931432697 16866257793832331948574523)
            ·
              refine ⟨25299386690748497922861785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16866257793832331948574523 25299386690748497922861785)
              ·
                refine ⟨18974540018061373442146339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25299386690748497922861785 18974540018061373442146339)
                ·
                  refine ⟨28461810027092060163219509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18974540018061373442146339 28461810027092060163219509)
                  ·
                    refine ⟨2668294690039880640301829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28461810027092060163219509 2668294690039880640301829)
                    ·
                      refine ⟨500305254382477620056593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2668294690039880640301829 500305254382477620056593)
                      ·
                        rfl

theorem cell23_974341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_974341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974341 prefixEnd_974341 := by exact prefixLift 974341
  have htrace : WordTrace (prefixWord ++ tailWord_974341) baseStart_974341 baseEnd_974341 := by
    simpa [prefixWord, tailWord_974341, baseEnd_974341] using wordTrace_append hprefix tailTrace_974341
  have hstable : (prefixWord ++ tailWord_974341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974341).length < 2 ^ (prefixWord ++ tailWord_974341).sum := by decide
  have hdescent : baseEnd_974341 < baseStart_974341 := by decide
  rcases family_descends (prefixWord ++ tailWord_974341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974345 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 1, 3, 2]
def baseStart_974345 : Nat := 118140960795 + 974345 * 2 ^ 59
def prefixEnd_974345 : Nat := 4983230072969 + 3 ^ 40 * 974345 * 2
def baseEnd_974345 : Nat := 500307308305095604406575

theorem tailTrace_974345 : CollatzResearch.WordTrace tailWord_974345 prefixEnd_974345 500307308305095604406575 := by
  unfold tailWord_974345
  simp only [CollatzResearch.WordTrace]
  refine ⟨35537281655121944722940489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23691521103414629815293659 35537281655121944722940489)
  ·
    refine ⟨26652961241341458542205367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35537281655121944722940489 26652961241341458542205367)
    ·
      refine ⟨39979441862012187813308051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26652961241341458542205367 39979441862012187813308051)
      ·
        refine ⟨59969162793018281719962077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39979441862012187813308051 59969162793018281719962077)
        ·
          refine ⟨22488436047381855644985779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59969162793018281719962077 22488436047381855644985779)
          ·
            refine ⟨33732654071072783467478669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22488436047381855644985779 33732654071072783467478669)
            ·
              refine ⟨12649745276652293800304501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33732654071072783467478669 12649745276652293800304501)
              ·
                refine ⟨1185913619686152543778547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12649745276652293800304501 1185913619686152543778547)
                ·
                  refine ⟨1778870429529228815667821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185913619686152543778547 1778870429529228815667821)
                  ·
                    refine ⟨667076411073460805875433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778870429529228815667821 667076411073460805875433)
                    ·
                      refine ⟨500307308305095604406575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667076411073460805875433 500307308305095604406575)
                      ·
                        rfl

theorem cell23_974345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 3, 2].length) (baseStart_974345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974345 prefixEnd_974345 := by exact prefixLift 974345
  have htrace : WordTrace (prefixWord ++ tailWord_974345) baseStart_974345 baseEnd_974345 := by
    simpa [prefixWord, tailWord_974345, baseEnd_974345] using wordTrace_append hprefix tailTrace_974345
  have hstable : (prefixWord ++ tailWord_974345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974345).length < 2 ^ (prefixWord ++ tailWord_974345).sum := by decide
  have hdescent : baseEnd_974345 < baseStart_974345 := by decide
  rcases family_descends (prefixWord ++ tailWord_974345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974361 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_974361 : Nat := 118140960795 + 974361 * 2 ^ 59
def prefixEnd_974361 : Nat := 4983230072969 + 3 ^ 40 * 974361 * 2
def baseEnd_974361 : Nat := 500315523995567541806501

theorem tailTrace_974361 : CollatzResearch.WordTrace tailWord_974361 prefixEnd_974361 500315523995567541806501 := by
  unfold tailWord_974361
  simp only [CollatzResearch.WordTrace]
  refine ⟨35537865223063979455522937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23691910148709319637015291 35537865223063979455522937)
  ·
    refine ⟨26653398917297984591642203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35537865223063979455522937 26653398917297984591642203)
    ·
      refine ⟨39980098375946976887463305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26653398917297984591642203 39980098375946976887463305)
      ·
        refine ⟨29985073781960232665597479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39980098375946976887463305 29985073781960232665597479)
        ·
          refine ⟨44977610672940348998396219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29985073781960232665597479 44977610672940348998396219)
          ·
            refine ⟨67466416009410523497594329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44977610672940348998396219 67466416009410523497594329)
            ·
              refine ⟨50599812007057892623195747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67466416009410523497594329 50599812007057892623195747)
              ·
                refine ⟨75899718010586838934793621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50599812007057892623195747 75899718010586838934793621)
                ·
                  refine ⟨3557799281746258075068451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75899718010586838934793621 3557799281746258075068451)
                  ·
                    refine ⟨5336698922619387112602677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3557799281746258075068451 5336698922619387112602677)
                    ·
                      refine ⟨500315523995567541806501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5336698922619387112602677 500315523995567541806501)
                      ·
                        rfl

theorem cell23_974361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_974361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974361 prefixEnd_974361 := by exact prefixLift 974361
  have htrace : WordTrace (prefixWord ++ tailWord_974361) baseStart_974361 baseEnd_974361 := by
    simpa [prefixWord, tailWord_974361, baseEnd_974361] using wordTrace_append hprefix tailTrace_974361
  have hstable : (prefixWord ++ tailWord_974361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974361).length < 2 ^ (prefixWord ++ tailWord_974361).sum := by decide
  have hdescent : baseEnd_974361 < baseStart_974361 := by decide
  rcases family_descends (prefixWord ++ tailWord_974361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974369 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_974369 : Nat := 118140960795 + 974369 * 2 ^ 59
def prefixEnd_974369 : Nat := 4983230072969 + 3 ^ 40 * 974369 * 2
def baseEnd_974369 : Nat := 500319631840803510506465

theorem tailTrace_974369 : CollatzResearch.WordTrace tailWord_974369 prefixEnd_974369 500319631840803510506465 := by
  unfold tailWord_974369
  simp only [CollatzResearch.WordTrace]
  refine ⟨35538157007034996821814161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23692104671356664547876107 35538157007034996821814161)
  ·
    refine ⟨26653617755276247616360621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35538157007034996821814161 26653617755276247616360621)
    ·
      refine ⟨9995106658228592856135233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26653617755276247616360621 9995106658228592856135233)
      ·
        refine ⟨7496329993671444642101425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9995106658228592856135233 7496329993671444642101425)
        ·
          refine ⟨5622247495253583481576069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7496329993671444642101425 5622247495253583481576069)
          ·
            refine ⟨1054171405360046902795513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5622247495253583481576069 1054171405360046902795513)
            ·
              refine ⟨790628554020035177096635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054171405360046902795513 790628554020035177096635)
              ·
                refine ⟨1185942831030052765644953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790628554020035177096635 1185942831030052765644953)
                ·
                  refine ⟨889457123272539574233715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185942831030052765644953 889457123272539574233715)
                  ·
                    refine ⟨1334185684908809361350573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 889457123272539574233715 1334185684908809361350573)
                    ·
                      refine ⟨500319631840803510506465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1334185684908809361350573 500319631840803510506465)
                      ·
                        rfl

theorem cell23_974369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_974369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974369 prefixEnd_974369 := by exact prefixLift 974369
  have htrace : WordTrace (prefixWord ++ tailWord_974369) baseStart_974369 baseEnd_974369 := by
    simpa [prefixWord, tailWord_974369, baseEnd_974369] using wordTrace_append hprefix tailTrace_974369
  have hstable : (prefixWord ++ tailWord_974369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974369).length < 2 ^ (prefixWord ++ tailWord_974369).sum := by decide
  have hdescent : baseEnd_974369 < baseStart_974369 := by decide
  rcases family_descends (prefixWord ++ tailWord_974369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974378 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_974378 : Nat := 118140960795 + 974378 * 2 ^ 59
def prefixEnd_974378 : Nat := 4983230072969 + 3 ^ 40 * 974378 * 2
def baseEnd_974378 : Nat := 500324253166693975293923

theorem tailTrace_974378 : CollatzResearch.WordTrace tailWord_974378 prefixEnd_974378 500324253166693975293923 := by
  unfold tailWord_974378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8884621316000597839722947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23692323509334927572594525 8884621316000597839722947)
  ·
    refine ⟨13326931974000896759584421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8884621316000597839722947 13326931974000896759584421)
    ·
      refine ⟨2498799745125168142422079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13326931974000896759584421 2498799745125168142422079)
      ·
        refine ⟨3748199617687752213633119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498799745125168142422079 3748199617687752213633119)
        ·
          refine ⟨5622299426531628320449679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748199617687752213633119 5622299426531628320449679)
          ·
            refine ⟨8433449139797442480674519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622299426531628320449679 8433449139797442480674519)
            ·
              refine ⟨12650173709696163721011779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433449139797442480674519 12650173709696163721011779)
              ·
                refine ⟨18975260564544245581517669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12650173709696163721011779 18975260564544245581517669)
                ·
                  refine ⟨3557861355852046046534563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18975260564544245581517669 3557861355852046046534563)
                  ·
                    refine ⟨5336792033778069069801845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3557861355852046046534563 5336792033778069069801845)
                    ·
                      refine ⟨500324253166693975293923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5336792033778069069801845 500324253166693975293923)
                      ·
                        rfl

theorem cell23_974378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_974378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974378 prefixEnd_974378 := by exact prefixLift 974378
  have htrace : WordTrace (prefixWord ++ tailWord_974378) baseStart_974378 baseEnd_974378 := by
    simpa [prefixWord, tailWord_974378, baseEnd_974378] using wordTrace_append hprefix tailTrace_974378
  have hstable : (prefixWord ++ tailWord_974378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974378).length < 2 ^ (prefixWord ++ tailWord_974378).sum := by decide
  have hdescent : baseEnd_974378 < baseStart_974378 := by decide
  rcases family_descends (prefixWord ++ tailWord_974378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974411 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 3, 7]
def baseStart_974411 : Nat := 118140960795 + 974411 * 2 ^ 59
def prefixEnd_974411 : Nat := 4983230072969 + 3 ^ 40 * 974411 * 2
def baseEnd_974411 : Nat := 166780399342764115393757

theorem tailTrace_974411 : CollatzResearch.WordTrace tailWord_974411 prefixEnd_974411 166780399342764115393757 := by
  unfold tailWord_974411
  simp only [CollatzResearch.WordTrace]
  refine ⟨35539688872882837994843087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23693125915255225329895391 35539688872882837994843087)
  ·
    refine ⟨53309533309324256992264631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35539688872882837994843087 53309533309324256992264631)
    ·
      refine ⟨79964299963986385488396947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53309533309324256992264631 79964299963986385488396947)
      ·
        refine ⟨119946449945979578232595421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79964299963986385488396947 119946449945979578232595421)
        ·
          refine ⟨44979918729742341837223283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119946449945979578232595421 44979918729742341837223283)
          ·
            refine ⟨67469878094613512755834925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44979918729742341837223283 67469878094613512755834925)
            ·
              refine ⟨25301204285480067283438097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67469878094613512755834925 25301204285480067283438097)
              ·
                refine ⟨18975903214110050462578573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25301204285480067283438097 18975903214110050462578573)
                ·
                  refine ⟨7115963705291268923466965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18975903214110050462578573 7115963705291268923466965)
                  ·
                    refine ⟨166780399342764115393757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7115963705291268923466965 166780399342764115393757)
                    ·
                      rfl

theorem cell23_974411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_974411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974411 prefixEnd_974411 := by exact prefixLift 974411
  have htrace : WordTrace (prefixWord ++ tailWord_974411) baseStart_974411 baseEnd_974411 := by
    simpa [prefixWord, tailWord_974411, baseEnd_974411] using wordTrace_append hprefix tailTrace_974411
  have hstable : (prefixWord ++ tailWord_974411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974411).length < 2 ^ (prefixWord ++ tailWord_974411).sum := by decide
  have hdescent : baseEnd_974411 < baseStart_974411 := by decide
  rcases family_descends (prefixWord ++ tailWord_974411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974445 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_974445 : Nat := 118140960795 + 974445 * 2 ^ 59
def prefixEnd_974445 : Nat := 4983230072969 + 3 ^ 40 * 974445 * 2
def baseEnd_974445 : Nat := 166786218790181737718705

theorem tailTrace_974445 : CollatzResearch.WordTrace tailWord_974445 prefixEnd_974445 166786218790181737718705 := by
  unfold tailWord_974445
  simp only [CollatzResearch.WordTrace]
  refine ⟨35540928954759661801580789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23693952636506441201053859 35540928954759661801580789)
  ·
    refine ⟨3331962089508718293898199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35540928954759661801580789 3331962089508718293898199)
    ·
      refine ⟨4997943134263077440847299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331962089508718293898199 4997943134263077440847299)
      ·
        refine ⟨7496914701394616161270949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4997943134263077440847299 7496914701394616161270949)
        ·
          refine ⟨1405671506511490530238303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7496914701394616161270949 1405671506511490530238303)
          ·
            refine ⟨2108507259767235795357455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405671506511490530238303 2108507259767235795357455)
            ·
              refine ⟨3162760889650853693036183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108507259767235795357455 3162760889650853693036183)
              ·
                refine ⟨4744141334476280539554275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162760889650853693036183 4744141334476280539554275)
                ·
                  refine ⟨7116212001714420809331413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744141334476280539554275 7116212001714420809331413)
                  ·
                    refine ⟨166786218790181737718705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7116212001714420809331413 166786218790181737718705)
                    ·
                      rfl

theorem cell23_974445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_974445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974445 prefixEnd_974445 := by exact prefixLift 974445
  have htrace : WordTrace (prefixWord ++ tailWord_974445) baseStart_974445 baseEnd_974445 := by
    simpa [prefixWord, tailWord_974445, baseEnd_974445] using wordTrace_append hprefix tailTrace_974445
  have hstable : (prefixWord ++ tailWord_974445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974445).length < 2 ^ (prefixWord ++ tailWord_974445).sum := by decide
  have hdescent : baseEnd_974445 < baseStart_974445 := by decide
  rcases family_descends (prefixWord ++ tailWord_974445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974475 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 3, 4]
def baseStart_974475 : Nat := 118140960795 + 974475 * 2 ^ 59
def prefixEnd_974475 : Nat := 4983230072969 + 3 ^ 40 * 974475 * 2
def baseEnd_974475 : Nat := 166791353596726698593659

theorem tailTrace_974475 : CollatzResearch.WordTrace tailWord_974475 prefixEnd_974475 166791353596726698593659 := by
  unfold tailWord_974475
  simp only [CollatzResearch.WordTrace]
  refine ⟨35542023144650976925172879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23694682096433984616781919 35542023144650976925172879)
  ·
    refine ⟨53313034716976465387759319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35542023144650976925172879 53313034716976465387759319)
    ·
      refine ⟨79969552075464698081638979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53313034716976465387759319 79969552075464698081638979)
      ·
        refine ⟨119954328113197047122458469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79969552075464698081638979 119954328113197047122458469)
        ·
          refine ⟨22491436521224446335460963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119954328113197047122458469 22491436521224446335460963)
          ·
            refine ⟨33737154781836669503191445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22491436521224446335460963 33737154781836669503191445)
            ·
              refine ⟨1581429130398593882962099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33737154781836669503191445 1581429130398593882962099)
              ·
                refine ⟨2372143695597890824443149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581429130398593882962099 2372143695597890824443149)
                ·
                  refine ⟨889553885849209059166181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2372143695597890824443149 889553885849209059166181)
                  ·
                    refine ⟨166791353596726698593659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889553885849209059166181 166791353596726698593659)
                    ·
                      rfl

theorem cell23_974475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 4].length) (baseStart_974475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974475 prefixEnd_974475 := by exact prefixLift 974475
  have htrace : WordTrace (prefixWord ++ tailWord_974475) baseStart_974475 baseEnd_974475 := by
    simpa [prefixWord, tailWord_974475, baseEnd_974475] using wordTrace_append hprefix tailTrace_974475
  have hstable : (prefixWord ++ tailWord_974475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974475).length < 2 ^ (prefixWord ++ tailWord_974475).sum := by decide
  have hdescent : baseEnd_974475 < baseStart_974475 := by decide
  rcases family_descends (prefixWord ++ tailWord_974475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974526 : List Nat := [4, 2, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_974526 : Nat := 118140960795 + 974526 * 2 ^ 59
def prefixEnd_974526 : Nat := 4983230072969 + 3 ^ 40 * 974526 * 2
def baseEnd_974526 : Nat := 166800082767853132081081

theorem tailTrace_974526 : CollatzResearch.WordTrace tailWord_974526 prefixEnd_974526 166800082767853132081081 := by
  unfold tailWord_974526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442985408433276579409929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23695922178310808423519621 4442985408433276579409929)
  ·
    refine ⟨3332239056324957434557447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4442985408433276579409929 3332239056324957434557447)
    ·
      refine ⟨4998358584487436151836171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332239056324957434557447 4998358584487436151836171)
      ·
        refine ⟨7497537876731154227754257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998358584487436151836171 7497537876731154227754257)
        ·
          refine ⟨5623153407548365670815693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497537876731154227754257 5623153407548365670815693)
          ·
            refine ⟨2108682527830637126555885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5623153407548365670815693 2108682527830637126555885)
            ·
              refine ⟨790755947936488922458457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2108682527830637126555885 790755947936488922458457)
              ·
                refine ⟨593066960952366691843843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790755947936488922458457 593066960952366691843843)
                ·
                  refine ⟨889600441428550037765765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593066960952366691843843 889600441428550037765765)
                  ·
                    refine ⟨166800082767853132081081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889600441428550037765765 166800082767853132081081)
                    ·
                      rfl

theorem cell23_974526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_974526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974526 prefixEnd_974526 := by exact prefixLift 974526
  have htrace : WordTrace (prefixWord ++ tailWord_974526) baseStart_974526 baseEnd_974526 := by
    simpa [prefixWord, tailWord_974526, baseEnd_974526] using wordTrace_append hprefix tailTrace_974526
  have hstable : (prefixWord ++ tailWord_974526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974526).length < 2 ^ (prefixWord ++ tailWord_974526).sum := by decide
  have hdescent : baseEnd_974526 < baseStart_974526 := by decide
  rcases family_descends (prefixWord ++ tailWord_974526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974542 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_974542 : Nat := 118140960795 + 974542 * 2 ^ 59
def prefixEnd_974542 : Nat := 4983230072969 + 3 ^ 40 * 974542 * 2
def baseEnd_974542 : Nat := 500408463994031333643169

theorem tailTrace_974542 : CollatzResearch.WordTrace tailWord_974542 prefixEnd_974542 500408463994031333643169 := by
  unfold tailWord_974542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443058354426030920982735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23696311223605498245241253 4443058354426030920982735)
  ·
    refine ⟨6664587531639046381474103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4443058354426030920982735 6664587531639046381474103)
    ·
      refine ⟨9996881297458569572211155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664587531639046381474103 9996881297458569572211155)
      ·
        refine ⟨14995321946187854358316733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9996881297458569572211155 14995321946187854358316733)
        ·
          refine ⟨5623245729820445384368775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14995321946187854358316733 5623245729820445384368775)
          ·
            refine ⟨8434868594730668076553163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623245729820445384368775 8434868594730668076553163)
            ·
              refine ⟨12652302892096002114829745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434868594730668076553163 12652302892096002114829745)
              ·
                refine ⟨9489227169072001586122309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12652302892096002114829745 9489227169072001586122309)
                ·
                  refine ⟨1779230094201000297397933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9489227169072001586122309 1779230094201000297397933)
                  ·
                    refine ⟨667211285325375111524225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779230094201000297397933 667211285325375111524225)
                    ·
                      refine ⟨500408463994031333643169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667211285325375111524225 500408463994031333643169)
                      ·
                        rfl

theorem cell23_974542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_974542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974542 prefixEnd_974542 := by exact prefixLift 974542
  have htrace : WordTrace (prefixWord ++ tailWord_974542) baseStart_974542 baseEnd_974542 := by
    simpa [prefixWord, tailWord_974542, baseEnd_974542] using wordTrace_append hprefix tailTrace_974542
  have hstable : (prefixWord ++ tailWord_974542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974542).length < 2 ^ (prefixWord ++ tailWord_974542).sum := by decide
  have hdescent : baseEnd_974542 < baseStart_974542 := by decide
  rcases family_descends (prefixWord ++ tailWord_974542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974565 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_974565 : Nat := 118140960795 + 974565 * 2 ^ 59
def prefixEnd_974565 : Nat := 4983230072969 + 3 ^ 40 * 974565 * 2
def baseEnd_974565 : Nat := 166806758016361581218521

theorem tailTrace_974565 : CollatzResearch.WordTrace tailWord_974565 prefixEnd_974565 166806758016361581218521 := by
  unfold tailWord_974565
  simp only [CollatzResearch.WordTrace]
  refine ⟨35545305714324922295949149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23696870476216614863966099 35545305714324922295949149)
  ·
    refine ⟨13329489642871845860980931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35545305714324922295949149 13329489642871845860980931)
    ·
      refine ⟨19994234464307768791471397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13329489642871845860980931 19994234464307768791471397)
      ·
        refine ⟨3748918962057706648400887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19994234464307768791471397 3748918962057706648400887)
        ·
          refine ⟨5623378443086559972601331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748918962057706648400887 5623378443086559972601331)
          ·
            refine ⟨8435067664629839958901997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623378443086559972601331 8435067664629839958901997)
            ·
              refine ⟨3163150374236189984588249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8435067664629839958901997 3163150374236189984588249)
              ·
                refine ⟨2372362780677142488441187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163150374236189984588249 2372362780677142488441187)
                ·
                  refine ⟨3558544171015713732661781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372362780677142488441187 3558544171015713732661781)
                  ·
                    refine ⟨166806758016361581218521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3558544171015713732661781 166806758016361581218521)
                    ·
                      rfl

theorem cell23_974565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_974565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974565 prefixEnd_974565 := by exact prefixLift 974565
  have htrace : WordTrace (prefixWord ++ tailWord_974565) baseStart_974565 baseEnd_974565 := by
    simpa [prefixWord, tailWord_974565, baseEnd_974565] using wordTrace_append hprefix tailTrace_974565
  have hstable : (prefixWord ++ tailWord_974565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974565).length < 2 ^ (prefixWord ++ tailWord_974565).sum := by decide
  have hdescent : baseEnd_974565 < baseStart_974565 := by decide
  rcases family_descends (prefixWord ++ tailWord_974565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974602 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_974602 : Nat := 118140960795 + 974602 * 2 ^ 59
def prefixEnd_974602 : Nat := 4983230072969 + 3 ^ 40 * 974602 * 2
def baseEnd_974602 : Nat := 500439272833301098892893

theorem tailTrace_974602 : CollatzResearch.WordTrace tailWord_974602 prefixEnd_974602 500439272833301098892893 := by
  unfold tailWord_974602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8886663803797719403761515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23697770143460585076697373 8886663803797719403761515)
  ·
    refine ⟨13329995705696579105642273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8886663803797719403761515 13329995705696579105642273)
    ·
      refine ⟨9997496779272434329231705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13329995705696579105642273 9997496779272434329231705)
      ·
        refine ⟨7498122584454325746923779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9997496779272434329231705 7498122584454325746923779)
        ·
          refine ⟨11247183876681488620385669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7498122584454325746923779 11247183876681488620385669)
          ·
            refine ⟨2108846976877779116322313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11247183876681488620385669 2108846976877779116322313)
            ·
              refine ⟨1581635232658334337241735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108846976877779116322313 1581635232658334337241735)
              ·
                refine ⟨2372452848987501505862603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581635232658334337241735 2372452848987501505862603)
                ·
                  refine ⟨3558679273481252258793905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372452848987501505862603 3558679273481252258793905)
                  ·
                    refine ⟨2669009455110939194095429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3558679273481252258793905 2669009455110939194095429)
                    ·
                      refine ⟨500439272833301098892893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2669009455110939194095429 500439272833301098892893)
                      ·
                        rfl

theorem cell23_974602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_974602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974602 prefixEnd_974602 := by exact prefixLift 974602
  have htrace : WordTrace (prefixWord ++ tailWord_974602) baseStart_974602 baseEnd_974602 := by
    simpa [prefixWord, tailWord_974602, baseEnd_974602] using wordTrace_append hprefix tailTrace_974602
  have hstable : (prefixWord ++ tailWord_974602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974602).length < 2 ^ (prefixWord ++ tailWord_974602).sum := by decide
  have hdescent : baseEnd_974602 < baseStart_974602 := by decide
  rcases family_descends (prefixWord ++ tailWord_974602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974665 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_974665 : Nat := 118140960795 + 974665 * 2 ^ 59
def prefixEnd_974665 : Nat := 4983230072969 + 3 ^ 40 * 974665 * 2
def baseEnd_974665 : Nat := 500471622114534352405103

theorem tailTrace_974665 : CollatzResearch.WordTrace tailWord_974665 prefixEnd_974665 500471622114534352405103 := by
  unfold tailWord_974665
  simp only [CollatzResearch.WordTrace]
  refine ⟨35548953013962639374589449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23699302009308426249726299 35548953013962639374589449)
  ·
    refine ⟨26661714760471979530942087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35548953013962639374589449 26661714760471979530942087)
    ·
      refine ⟨39992572140707969296413131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26661714760471979530942087 39992572140707969296413131)
      ·
        refine ⟨59988858211061953944619697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39992572140707969296413131 59988858211061953944619697)
        ·
          refine ⟨44991643658296465458464773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59988858211061953944619697 44991643658296465458464773)
          ·
            refine ⟨8435933185930587273462145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44991643658296465458464773 8435933185930587273462145)
            ·
              refine ⟨6326949889447940455096609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435933185930587273462145 6326949889447940455096609)
              ·
                refine ⟨4745212417085955341322457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326949889447940455096609 4745212417085955341322457)
                ·
                  refine ⟨3558909312814466505991843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745212417085955341322457 3558909312814466505991843)
                  ·
                    refine ⟨5338363969221699758987765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558909312814466505991843 5338363969221699758987765)
                    ·
                      refine ⟨500471622114534352405103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5338363969221699758987765 500471622114534352405103)
                      ·
                        rfl

theorem cell23_974665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_974665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974665 prefixEnd_974665 := by exact prefixLift 974665
  have htrace : WordTrace (prefixWord ++ tailWord_974665) baseStart_974665 baseEnd_974665 := by
    simpa [prefixWord, tailWord_974665, baseEnd_974665] using wordTrace_append hprefix tailTrace_974665
  have hstable : (prefixWord ++ tailWord_974665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974665).length < 2 ^ (prefixWord ++ tailWord_974665).sum := by decide
  have hdescent : baseEnd_974665 < baseStart_974665 := by decide
  rcases family_descends (prefixWord ++ tailWord_974665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974695 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_974695 : Nat := 118140960795 + 974695 * 2 ^ 59
def prefixEnd_974695 : Nat := 4983230072969 + 3 ^ 40 * 974695 * 2
def baseEnd_974695 : Nat := 500487026534169235029965

theorem tailTrace_974695 : CollatzResearch.WordTrace tailWord_974695 prefixEnd_974695 500487026534169235029965 := by
  unfold tailWord_974695
  simp only [CollatzResearch.WordTrace]
  refine ⟨35550047203853954498181539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23700031469235969665454359 35550047203853954498181539)
  ·
    refine ⟨53325070805780931747272309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35550047203853954498181539 53325070805780931747272309)
    ·
      refine ⟨4999225388041962351306779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53325070805780931747272309 4999225388041962351306779)
      ·
        refine ⟨7498838082062943526960169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999225388041962351306779 7498838082062943526960169)
        ·
          refine ⟨5624128561547207645220127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7498838082062943526960169 5624128561547207645220127)
          ·
            refine ⟨8436192842320811467830191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624128561547207645220127 8436192842320811467830191)
            ·
              refine ⟨12654289263481217201745287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436192842320811467830191 12654289263481217201745287)
              ·
                refine ⟨18981433895221825802617931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12654289263481217201745287 18981433895221825802617931)
                ·
                  refine ⟨28472150842832738703926897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18981433895221825802617931 28472150842832738703926897)
                  ·
                    refine ⟨21354113132124554027945173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28472150842832738703926897 21354113132124554027945173)
                    ·
                      refine ⟨500487026534169235029965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21354113132124554027945173 500487026534169235029965)
                      ·
                        rfl

theorem cell23_974695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_974695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974695 prefixEnd_974695 := by exact prefixLift 974695
  have htrace : WordTrace (prefixWord ++ tailWord_974695) baseStart_974695 baseEnd_974695 := by
    simpa [prefixWord, tailWord_974695, baseEnd_974695] using wordTrace_append hprefix tailTrace_974695
  have hstable : (prefixWord ++ tailWord_974695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974695).length < 2 ^ (prefixWord ++ tailWord_974695).sum := by decide
  have hdescent : baseEnd_974695 < baseStart_974695 := by decide
  rcases family_descends (prefixWord ++ tailWord_974695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974696 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_974696 : Nat := 118140960795 + 974696 * 2 ^ 59
def prefixEnd_974696 : Nat := 4983230072969 + 3 ^ 40 * 974696 * 2
def baseEnd_974696 : Nat := 500487540014823731117461

theorem tailTrace_974696 : CollatzResearch.WordTrace tailWord_974696 prefixEnd_974696 500487540014823731117461 := by
  unfold tailWord_974696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775041838425165834483971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23700055784566887779311961 17775041838425165834483971)
  ·
    refine ⟨26662562757637748751725957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17775041838425165834483971 26662562757637748751725957)
    ·
      refine ⟨4999230517057077890948617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26662562757637748751725957 4999230517057077890948617)
      ·
        refine ⟨3749422887792808418211463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4999230517057077890948617 3749422887792808418211463)
        ·
          refine ⟨5624134331689212627317195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749422887792808418211463 5624134331689212627317195)
          ·
            refine ⟨8436201497533818940975793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624134331689212627317195 8436201497533818940975793)
            ·
              refine ⟨6327151123150364205731845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8436201497533818940975793 6327151123150364205731845)
              ·
                refine ⟨1186340835590693288574721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6327151123150364205731845 1186340835590693288574721)
                ·
                  refine ⟨889755626693019966431041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1186340835590693288574721 889755626693019966431041)
                  ·
                    refine ⟨667316720019764974823281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 889755626693019966431041 667316720019764974823281)
                    ·
                      refine ⟨500487540014823731117461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667316720019764974823281 500487540014823731117461)
                      ·
                        rfl

theorem cell23_974696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_974696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974696 prefixEnd_974696 := by exact prefixLift 974696
  have htrace : WordTrace (prefixWord ++ tailWord_974696) baseStart_974696 baseEnd_974696 := by
    simpa [prefixWord, tailWord_974696, baseEnd_974696] using wordTrace_append hprefix tailTrace_974696
  have hstable : (prefixWord ++ tailWord_974696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974696).length < 2 ^ (prefixWord ++ tailWord_974696).sum := by decide
  have hdescent : baseEnd_974696 < baseStart_974696 := by decide
  rcases family_descends (prefixWord ++ tailWord_974696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974715 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 6, 5]
def baseStart_974715 : Nat := 118140960795 + 974715 * 2 ^ 59
def prefixEnd_974715 : Nat := 4983230072969 + 3 ^ 40 * 974715 * 2
def baseEnd_974715 : Nat := 166832432049086385593291

theorem tailTrace_974715 : CollatzResearch.WordTrace tailWord_974715 prefixEnd_974715 166832432049086385593291 := by
  unfold tailWord_974715
  simp only [CollatzResearch.WordTrace]
  refine ⟨35550776663781497913909599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23700517775854331942606399 35550776663781497913909599)
  ·
    refine ⟨53326164995672246870864399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35550776663781497913909599 53326164995672246870864399)
    ·
      refine ⟨79989247493508370306296599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53326164995672246870864399 79989247493508370306296599)
      ·
        refine ⟨119983871240262555459444899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79989247493508370306296599 119983871240262555459444899)
        ·
          refine ⟨179975806860393833189167349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119983871240262555459444899 179975806860393833189167349)
          ·
            refine ⟨16872731893161921861484439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179975806860393833189167349 16872731893161921861484439)
            ·
              refine ⟨25309097839742882792226659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16872731893161921861484439 25309097839742882792226659)
              ·
                refine ⟨37963646759614324188339989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25309097839742882792226659 37963646759614324188339989)
                ·
                  refine ⟨1779545941856921446328437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37963646759614324188339989 1779545941856921446328437)
                  ·
                    refine ⟨166832432049086385593291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1779545941856921446328437 166832432049086385593291)
                    ·
                      rfl

theorem cell23_974715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 5].length) (baseStart_974715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974715 prefixEnd_974715 := by exact prefixLift 974715
  have htrace : WordTrace (prefixWord ++ tailWord_974715) baseStart_974715 baseEnd_974715 := by
    simpa [prefixWord, tailWord_974715, baseEnd_974715] using wordTrace_append hprefix tailTrace_974715
  have hstable : (prefixWord ++ tailWord_974715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974715).length < 2 ^ (prefixWord ++ tailWord_974715).sum := by decide
  have hdescent : baseEnd_974715 < baseStart_974715 := by decide
  rcases family_descends (prefixWord ++ tailWord_974715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974725 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_974725 : Nat := 118140960795 + 974725 * 2 ^ 59
def prefixEnd_974725 : Nat := 4983230072969 + 3 ^ 40 * 974725 * 2
def baseEnd_974725 : Nat := 500502430953804117654827

theorem tailTrace_974725 : CollatzResearch.WordTrace tailWord_974725 prefixEnd_974725 500502430953804117654827 := by
  unfold tailWord_974725
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551141393745269621773629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23700760929163513081182419 35551141393745269621773629)
  ·
    refine ⟨13331678022654476108165111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35551141393745269621773629 13331678022654476108165111)
    ·
      refine ⟨19997517033981714162247667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13331678022654476108165111 19997517033981714162247667)
      ·
        refine ⟨29996275550972571243371501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19997517033981714162247667 29996275550972571243371501)
        ·
          refine ⟨11248603331614714216264313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29996275550972571243371501 11248603331614714216264313)
          ·
            refine ⟨8436452498711035662198235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11248603331614714216264313 8436452498711035662198235)
            ·
              refine ⟨12654678748066553493297353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436452498711035662198235 12654678748066553493297353)
              ·
                refine ⟨9491009061049915119973015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12654678748066553493297353 9491009061049915119973015)
                ·
                  refine ⟨14236513591574872679959523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9491009061049915119973015 14236513591574872679959523)
                  ·
                    refine ⟨21354770387362309019939285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14236513591574872679959523 21354770387362309019939285)
                    ·
                      refine ⟨500502430953804117654827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21354770387362309019939285 500502430953804117654827)
                      ·
                        rfl

theorem cell23_974725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_974725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974725 prefixEnd_974725 := by exact prefixLift 974725
  have htrace : WordTrace (prefixWord ++ tailWord_974725) baseStart_974725 baseEnd_974725 := by
    simpa [prefixWord, tailWord_974725, baseEnd_974725] using wordTrace_append hprefix tailTrace_974725
  have hstable : (prefixWord ++ tailWord_974725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974725).length < 2 ^ (prefixWord ++ tailWord_974725).sum := by decide
  have hdescent : baseEnd_974725 < baseStart_974725 := by decide
  rcases family_descends (prefixWord ++ tailWord_974725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974735 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_974735 : Nat := 118140960795 + 974735 * 2 ^ 59
def prefixEnd_974735 : Nat := 4983230072969 + 3 ^ 40 * 974735 * 2
def baseEnd_974735 : Nat := 500507565760349078529781

theorem tailTrace_974735 : CollatzResearch.WordTrace tailWord_974735 prefixEnd_974735 500507565760349078529781 := by
  unfold tailWord_974735
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551506123709041329637659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23701004082472694219758439 35551506123709041329637659)
  ·
    refine ⟨53327259185563561994456489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35551506123709041329637659 53327259185563561994456489)
    ·
      refine ⟨39995444389172671495842367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53327259185563561994456489 39995444389172671495842367)
      ·
        refine ⟨59993166583759007243763551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39995444389172671495842367 59993166583759007243763551)
        ·
          refine ⟨89989749875638510865645327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59993166583759007243763551 89989749875638510865645327)
          ·
            refine ⟨134984624813457766298467991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89989749875638510865645327 134984624813457766298467991)
            ·
              refine ⟨202476937220186649447701987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134984624813457766298467991 202476937220186649447701987)
              ·
                refine ⟨303715405830279974171552981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202476937220186649447701987 303715405830279974171552981)
                ·
                  refine ⟨7118329824147186894645773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 303715405830279974171552981 7118329824147186894645773)
                  ·
                    refine ⟨2669373684055195085492165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7118329824147186894645773 2669373684055195085492165)
                    ·
                      refine ⟨500507565760349078529781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2669373684055195085492165 500507565760349078529781)
                      ·
                        rfl

theorem cell23_974735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_974735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974735 prefixEnd_974735 := by exact prefixLift 974735
  have htrace : WordTrace (prefixWord ++ tailWord_974735) baseStart_974735 baseEnd_974735 := by
    simpa [prefixWord, tailWord_974735, baseEnd_974735] using wordTrace_append hprefix tailTrace_974735
  have hstable : (prefixWord ++ tailWord_974735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974735).length < 2 ^ (prefixWord ++ tailWord_974735).sum := by decide
  have hdescent : baseEnd_974735 < baseStart_974735 := by decide
  rcases family_descends (prefixWord ++ tailWord_974735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974753 : List Nat := [1, 2, 3, 4, 2, 2, 2, 2, 5]
def baseStart_974753 : Nat := 118140960795 + 974753 * 2 ^ 59
def prefixEnd_974753 : Nat := 4983230072969 + 3 ^ 40 * 974753 * 2
def baseEnd_974753 : Nat := 55612978712458889789411

theorem tailTrace_974753 : CollatzResearch.WordTrace tailWord_974753 prefixEnd_974753 55612978712458889789411 := by
  unfold tailWord_974753
  simp only [CollatzResearch.WordTrace]
  refine ⟨35552162637643830403792913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23701441758429220269195275 35552162637643830403792913)
  ·
    refine ⟨26664121978232872802844685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35552162637643830403792913 26664121978232872802844685)
    ·
      refine ⟨9999045741837327301066757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26664121978232872802844685 9999045741837327301066757)
      ·
        refine ⟨1874821076594498868950017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9999045741837327301066757 1874821076594498868950017)
        ·
          refine ⟨1406115807445874151712513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1874821076594498868950017 1406115807445874151712513)
          ·
            refine ⟨1054586855584405613784385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406115807445874151712513 1054586855584405613784385)
            ·
              refine ⟨790940141688304210338289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054586855584405613784385 790940141688304210338289)
              ·
                refine ⟨593205106266228157753717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790940141688304210338289 593205106266228157753717)
                ·
                  refine ⟨55612978712458889789411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 593205106266228157753717 55612978712458889789411)
                  ·
                    rfl

theorem cell23_974753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 5].length) (baseStart_974753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974753 prefixEnd_974753 := by exact prefixLift 974753
  have htrace : WordTrace (prefixWord ++ tailWord_974753) baseStart_974753 baseEnd_974753 := by
    simpa [prefixWord, tailWord_974753, baseEnd_974753] using wordTrace_append hprefix tailTrace_974753
  have hstable : (prefixWord ++ tailWord_974753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974753).length < 2 ^ (prefixWord ++ tailWord_974753).sum := by decide
  have hdescent : baseEnd_974753 < baseStart_974753 := by decide
  rcases family_descends (prefixWord ++ tailWord_974753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974755 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5]
def baseStart_974755 : Nat := 118140960795 + 974755 * 2 ^ 59
def prefixEnd_974755 : Nat := 4983230072969 + 3 ^ 40 * 974755 * 2
def baseEnd_974755 : Nat := 500517835373439000279689

theorem tailTrace_974755 : CollatzResearch.WordTrace tailWord_974755 prefixEnd_974755 500517835373439000279689 := by
  unfold tailWord_974755
  simp only [CollatzResearch.WordTrace]
  refine ⟨35552235583636584745365719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23701490389091056496910479 35552235583636584745365719)
  ·
    refine ⟨53328353375454877118048579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35552235583636584745365719 53328353375454877118048579)
    ·
      refine ⟨79992530063182315677072869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53328353375454877118048579 79992530063182315677072869)
      ·
        refine ⟨14998599386846684189451163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79992530063182315677072869 14998599386846684189451163)
        ·
          refine ⟨22497899080270026284176745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14998599386846684189451163 22497899080270026284176745)
          ·
            refine ⟨16873424310202519713132559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22497899080270026284176745 16873424310202519713132559)
            ·
              refine ⟨25310136465303779569698839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16873424310202519713132559 25310136465303779569698839)
              ·
                refine ⟨37965204697955669354548259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25310136465303779569698839 37965204697955669354548259)
                ·
                  refine ⟨56947807046933504031822389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37965204697955669354548259 56947807046933504031822389)
                  ·
                    refine ⟨5338856910650016002983349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56947807046933504031822389 5338856910650016002983349)
                    ·
                      refine ⟨500517835373439000279689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5338856910650016002983349 500517835373439000279689)
                      ·
                        rfl

theorem cell23_974755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_974755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974755 prefixEnd_974755 := by exact prefixLift 974755
  have htrace : WordTrace (prefixWord ++ tailWord_974755) baseStart_974755 baseEnd_974755 := by
    simpa [prefixWord, tailWord_974755, baseEnd_974755] using wordTrace_append hprefix tailTrace_974755
  have hstable : (prefixWord ++ tailWord_974755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974755).length < 2 ^ (prefixWord ++ tailWord_974755).sum := by decide
  have hdescent : baseEnd_974755 < baseStart_974755 := by decide
  rcases family_descends (prefixWord ++ tailWord_974755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974769 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 1, 6, 2]
def baseStart_974769 : Nat := 118140960795 + 974769 * 2 ^ 59
def prefixEnd_974769 : Nat := 4983230072969 + 3 ^ 40 * 974769 * 2
def baseEnd_974769 : Nat := 500525024102601945504625

theorem tailTrace_974769 : CollatzResearch.WordTrace tailWord_974769 prefixEnd_974769 500525024102601945504625 := by
  unfold tailWord_974769
  simp only [CollatzResearch.WordTrace]
  refine ⟨35552746205585865136375361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23701830803723910090916907 35552746205585865136375361)
  ·
    refine ⟨26664559654189398852281521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35552746205585865136375361 26664559654189398852281521)
    ·
      refine ⟨19998419740642049139211141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26664559654189398852281521 19998419740642049139211141)
      ·
        refine ⟨3749703701370384213602089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19998419740642049139211141 3749703701370384213602089)
        ·
          refine ⟨2812277776027788160201567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749703701370384213602089 2812277776027788160201567)
          ·
            refine ⟨4218416664041682240302351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812277776027788160201567 4218416664041682240302351)
            ·
              refine ⟨6327624996062523360453527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218416664041682240302351 6327624996062523360453527)
              ·
                refine ⟨9491437494093785040680291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327624996062523360453527 9491437494093785040680291)
                ·
                  refine ⟨14237156241140677561020437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9491437494093785040680291 14237156241140677561020437)
                  ·
                    refine ⟨667366698803469260672833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14237156241140677561020437 667366698803469260672833)
                    ·
                      refine ⟨500525024102601945504625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667366698803469260672833 500525024102601945504625)
                      ·
                        rfl

theorem cell23_974769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_974769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974769 prefixEnd_974769 := by exact prefixLift 974769
  have htrace : WordTrace (prefixWord ++ tailWord_974769) baseStart_974769 baseEnd_974769 := by
    simpa [prefixWord, tailWord_974769, baseEnd_974769] using wordTrace_append hprefix tailTrace_974769
  have hstable : (prefixWord ++ tailWord_974769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974769).length < 2 ^ (prefixWord ++ tailWord_974769).sum := by decide
  have hdescent : baseEnd_974769 < baseStart_974769 := by decide
  rcases family_descends (prefixWord ++ tailWord_974769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974775 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 10]
def baseStart_974775 : Nat := 118140960795 + 974775 * 2 ^ 59
def prefixEnd_974775 : Nat := 4983230072969 + 3 ^ 40 * 974775 * 2
def baseEnd_974775 : Nat := 55614233887392102447733

theorem tailTrace_974775 : CollatzResearch.WordTrace tailWord_974775 prefixEnd_974775 55614233887392102447733 := by
  unfold tailWord_974775
  simp only [CollatzResearch.WordTrace]
  refine ⟨35552965043564128161093779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23701976695709418774062519 35552965043564128161093779)
  ·
    refine ⟨53329447565346192241640669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35552965043564128161093779 53329447565346192241640669)
    ·
      refine ⟨19998542837004822090615251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53329447565346192241640669 19998542837004822090615251)
      ·
        refine ⟨29997814255507233135922877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19998542837004822090615251 29997814255507233135922877)
        ·
          refine ⟨11249180345815212425971079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29997814255507233135922877 11249180345815212425971079)
          ·
            refine ⟨16873770518722818638956619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11249180345815212425971079 16873770518722818638956619)
            ·
              refine ⟨25310655778084227958434929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16873770518722818638956619 25310655778084227958434929)
              ·
                refine ⟨18982991833563170968826197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25310655778084227958434929 18982991833563170968826197)
                ·
                  refine ⟨55614233887392102447733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18982991833563170968826197 55614233887392102447733)
                  ·
                    rfl

theorem cell23_974775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 10].length) (baseStart_974775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974775 prefixEnd_974775 := by exact prefixLift 974775
  have htrace : WordTrace (prefixWord ++ tailWord_974775) baseStart_974775 baseEnd_974775 := by
    simpa [prefixWord, tailWord_974775, baseEnd_974775] using wordTrace_append hprefix tailTrace_974775
  have hstable : (prefixWord ++ tailWord_974775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974775).length < 2 ^ (prefixWord ++ tailWord_974775).sum := by decide
  have hdescent : baseEnd_974775 < baseStart_974775 := by decide
  rcases family_descends (prefixWord ++ tailWord_974775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974796 : List Nat := [2, 2, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_974796 : Nat := 118140960795 + 974796 * 2 ^ 59
def prefixEnd_974796 : Nat := 4983230072969 + 3 ^ 40 * 974796 * 2
def baseEnd_974796 : Nat := 166846296026757779955667

theorem tailTrace_974796 : CollatzResearch.WordTrace tailWord_974796 prefixEnd_974796 166846296026757779955667 := by
  unfold tailWord_974796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17776865488244024373804121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23702487317658699165072161 17776865488244024373804121)
  ·
    refine ⟨13332649116183018280353091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17776865488244024373804121 13332649116183018280353091)
    ·
      refine ⟨19998973674274527420529637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13332649116183018280353091 19998973674274527420529637)
      ·
        refine ⟨3749807563926473891349307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19998973674274527420529637 3749807563926473891349307)
        ·
          refine ⟨5624711345889710837023961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749807563926473891349307 5624711345889710837023961)
          ·
            refine ⟨4218533509417283127767971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5624711345889710837023961 4218533509417283127767971)
            ·
              refine ⟨6327800264125924691651957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218533509417283127767971 6327800264125924691651957)
              ·
                refine ⟨593231274761805439842371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6327800264125924691651957 593231274761805439842371)
                ·
                  refine ⟨889846912142708159763557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593231274761805439842371 889846912142708159763557)
                  ·
                    refine ⟨166846296026757779955667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889846912142708159763557 166846296026757779955667)
                    ·
                      rfl

theorem cell23_974796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_974796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974796 prefixEnd_974796 := by exact prefixLift 974796
  have htrace : WordTrace (prefixWord ++ tailWord_974796) baseStart_974796 baseEnd_974796 := by
    simpa [prefixWord, tailWord_974796, baseEnd_974796] using wordTrace_append hprefix tailTrace_974796
  have hstable : (prefixWord ++ tailWord_974796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974796).length < 2 ^ (prefixWord ++ tailWord_974796).sum := by decide
  have hdescent : baseEnd_974796 < baseStart_974796 := by decide
  rcases family_descends (prefixWord ++ tailWord_974796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974853 : List Nat := [1, 3, 1, 1, 2, 4, 3, 3, 1, 1, 3]
def baseStart_974853 : Nat := 118140960795 + 974853 * 2 ^ 59
def prefixEnd_974853 : Nat := 4983230072969 + 3 ^ 40 * 974853 * 2
def baseEnd_974853 : Nat := 500568156477579616854239

theorem tailTrace_974853 : CollatzResearch.WordTrace tailWord_974853 prefixEnd_974853 500568156477579616854239 := by
  unfold tailWord_974853
  simp only [CollatzResearch.WordTrace]
  refine ⟨35555809937281547482433213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23703873291521031654955475 35555809937281547482433213)
  ·
    refine ⟨13333428726480580305912455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35555809937281547482433213 13333428726480580305912455)
    ·
      refine ⟨20000143089720870458868683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333428726480580305912455 20000143089720870458868683)
      ·
        refine ⟨30000214634581305688303025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20000143089720870458868683 30000214634581305688303025)
        ·
          refine ⟨22500160975935979266227269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30000214634581305688303025 22500160975935979266227269)
          ·
            refine ⟨4218780182987996112417613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22500160975935979266227269 4218780182987996112417613)
            ·
              refine ⟨1582042568620498542156605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4218780182987996112417613 1582042568620498542156605)
              ·
                refine ⟨593265963232686953308727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582042568620498542156605 593265963232686953308727)
                ·
                  refine ⟨889898944849030429963091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593265963232686953308727 889898944849030429963091)
                  ·
                    refine ⟨1334848417273545644944637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 889898944849030429963091 1334848417273545644944637)
                    ·
                      refine ⟨500568156477579616854239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1334848417273545644944637 500568156477579616854239)
                      ·
                        rfl

theorem cell23_974853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_974853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974853 prefixEnd_974853 := by exact prefixLift 974853
  have htrace : WordTrace (prefixWord ++ tailWord_974853) baseStart_974853 baseEnd_974853 := by
    simpa [prefixWord, tailWord_974853, baseEnd_974853] using wordTrace_append hprefix tailTrace_974853
  have hstable : (prefixWord ++ tailWord_974853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974853).length < 2 ^ (prefixWord ++ tailWord_974853).sum := by decide
  have hdescent : baseEnd_974853 < baseStart_974853 := by decide
  rcases family_descends (prefixWord ++ tailWord_974853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974859 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 4]
def baseStart_974859 : Nat := 118140960795 + 974859 * 2 ^ 59
def prefixEnd_974859 : Nat := 4983230072969 + 3 ^ 40 * 974859 * 2
def baseEnd_974859 : Nat := 500571237361506593379211

theorem tailTrace_974859 : CollatzResearch.WordTrace tailWord_974859 prefixEnd_974859 500571237361506593379211 := by
  unfold tailWord_974859
  simp only [CollatzResearch.WordTrace]
  refine ⟨35556028775259810507151631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23704019183506540338101087 35556028775259810507151631)
  ·
    refine ⟨53334043162889715760727447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35556028775259810507151631 53334043162889715760727447)
    ·
      refine ⟨80001064744334573641091171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53334043162889715760727447 80001064744334573641091171)
      ·
        refine ⟨120001597116501860461636757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80001064744334573641091171 120001597116501860461636757)
        ·
          refine ⟨5625074864836024709139223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120001597116501860461636757 5625074864836024709139223)
          ·
            refine ⟨8437612297254037063708835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625074864836024709139223 8437612297254037063708835)
            ·
              refine ⟨12656418445881055595563253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8437612297254037063708835 12656418445881055595563253)
              ·
                refine ⟨1186539229301348962084055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12656418445881055595563253 1186539229301348962084055)
                ·
                  refine ⟨1779808843952023443126083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186539229301348962084055 1779808843952023443126083)
                  ·
                    refine ⟨2669713265928035164689125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1779808843952023443126083 2669713265928035164689125)
                    ·
                      refine ⟨500571237361506593379211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2669713265928035164689125 500571237361506593379211)
                      ·
                        rfl

theorem cell23_974859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 4].length) (baseStart_974859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974859 prefixEnd_974859 := by exact prefixLift 974859
  have htrace : WordTrace (prefixWord ++ tailWord_974859) baseStart_974859 baseEnd_974859 := by
    simpa [prefixWord, tailWord_974859, baseEnd_974859] using wordTrace_append hprefix tailTrace_974859
  have hstable : (prefixWord ++ tailWord_974859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974859).length < 2 ^ (prefixWord ++ tailWord_974859).sum := by decide
  have hdescent : baseEnd_974859 < baseStart_974859 := by decide
  rcases family_descends (prefixWord ++ tailWord_974859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974872 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_974872 : Nat := 118140960795 + 974872 * 2 ^ 59
def prefixEnd_974872 : Nat := 4983230072969 + 3 ^ 40 * 974872 * 2
def baseEnd_974872 : Nat := 500577912610015042516651

theorem tailTrace_974872 : CollatzResearch.WordTrace tailWord_974872 prefixEnd_974872 500577912610015042516651 := by
  unfold tailWord_974872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17778251462106356863687435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23704335282808475818249913 17778251462106356863687435)
  ·
    refine ⟨26667377193159535295531153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17778251462106356863687435 26667377193159535295531153)
    ·
      refine ⟨20000532894869651471648365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26667377193159535295531153 20000532894869651471648365)
      ·
        refine ⟨7500199835576119301868137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20000532894869651471648365 7500199835576119301868137)
        ·
          refine ⟨5625149876682089476401103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7500199835576119301868137 5625149876682089476401103)
          ·
            refine ⟨8437724815023134214601655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625149876682089476401103 8437724815023134214601655)
            ·
              refine ⟨12656587222534701321902483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8437724815023134214601655 12656587222534701321902483)
              ·
                refine ⟨18984880833802051982853725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12656587222534701321902483 18984880833802051982853725)
                ·
                  refine ⟨7119330312675769493570147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18984880833802051982853725 7119330312675769493570147)
                  ·
                    refine ⟨10678995469013654240355221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7119330312675769493570147 10678995469013654240355221)
                    ·
                      refine ⟨500577912610015042516651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10678995469013654240355221 500577912610015042516651)
                      ·
                        rfl

theorem cell23_974872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_974872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974872 prefixEnd_974872 := by exact prefixLift 974872
  have htrace : WordTrace (prefixWord ++ tailWord_974872) baseStart_974872 baseEnd_974872 := by
    simpa [prefixWord, tailWord_974872, baseEnd_974872] using wordTrace_append hprefix tailTrace_974872
  have hstable : (prefixWord ++ tailWord_974872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974872).length < 2 ^ (prefixWord ++ tailWord_974872).sum := by decide
  have hdescent : baseEnd_974872 < baseStart_974872 := by decide
  rcases family_descends (prefixWord ++ tailWord_974872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974879 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 3]
def baseStart_974879 : Nat := 118140960795 + 974879 * 2 ^ 59
def prefixEnd_974879 : Nat := 4983230072969 + 3 ^ 40 * 974879 * 2
def baseEnd_974879 : Nat := 500581506974596515129119

theorem tailTrace_974879 : CollatzResearch.WordTrace tailWord_974879 prefixEnd_974879 500581506974596515129119 := by
  unfold tailWord_974879
  simp only [CollatzResearch.WordTrace]
  refine ⟨35556758235187353922879691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23704505490124902615253127 35556758235187353922879691)
  ·
    refine ⟨53335137352781030884319537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35556758235187353922879691 53335137352781030884319537)
    ·
      refine ⟨40001353014585773163239653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53335137352781030884319537 40001353014585773163239653)
      ·
        refine ⟨7500253690234832468107435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40001353014585773163239653 7500253690234832468107435)
        ·
          refine ⟨11250380535352248702161153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500253690234832468107435 11250380535352248702161153)
          ·
            refine ⟨8437785401514186526620865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11250380535352248702161153 8437785401514186526620865)
            ·
              refine ⟨6328339051135639894965649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8437785401514186526620865 6328339051135639894965649)
              ·
                refine ⟨4746254288351729921224237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6328339051135639894965649 4746254288351729921224237)
                ·
                  refine ⟨1779845358131898720459089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4746254288351729921224237 1779845358131898720459089)
                  ·
                    refine ⟨1334884018598924040344317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1779845358131898720459089 1334884018598924040344317)
                    ·
                      refine ⟨500581506974596515129119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1334884018598924040344317 500581506974596515129119)
                      ·
                        rfl

theorem cell23_974879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_974879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974879 prefixEnd_974879 := by exact prefixLift 974879
  have htrace : WordTrace (prefixWord ++ tailWord_974879) baseStart_974879 baseEnd_974879 := by
    simpa [prefixWord, tailWord_974879, baseEnd_974879] using wordTrace_append hprefix tailTrace_974879
  have hstable : (prefixWord ++ tailWord_974879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974879).length < 2 ^ (prefixWord ++ tailWord_974879).sum := by decide
  have hdescent : baseEnd_974879 < baseStart_974879 := by decide
  rcases family_descends (prefixWord ++ tailWord_974879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974896 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3]
def baseStart_974896 : Nat := 118140960795 + 974896 * 2 ^ 59
def prefixEnd_974896 : Nat := 4983230072969 + 3 ^ 40 * 974896 * 2
def baseEnd_974896 : Nat := 500590236145722948616541

theorem tailTrace_974896 : CollatzResearch.WordTrace tailWord_974896 prefixEnd_974896 500590236145722948616541 := by
  unfold tailWord_974896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17778689138062882913124271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23704918850750510550832361 17778689138062882913124271)
  ·
    refine ⟨26668033707094324369686407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17778689138062882913124271 26668033707094324369686407)
    ·
      refine ⟨40002050560641486554529611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26668033707094324369686407 40002050560641486554529611)
      ·
        refine ⟨60003075840962229831794417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40002050560641486554529611 60003075840962229831794417)
        ·
          refine ⟨45002306880721672373845813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60003075840962229831794417 45002306880721672373845813)
          ·
            refine ⟨4218966270067656785048045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45002306880721672373845813 4218966270067656785048045)
            ·
              refine ⟨1582112351275371294393017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4218966270067656785048045 1582112351275371294393017)
              ·
                refine ⟨1186584263456528470794763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582112351275371294393017 1186584263456528470794763)
                ·
                  refine ⟨1779876395184792706192145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186584263456528470794763 1779876395184792706192145)
                  ·
                    refine ⟨1334907296388594529644109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1779876395184792706192145 1334907296388594529644109)
                    ·
                      refine ⟨500590236145722948616541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1334907296388594529644109 500590236145722948616541)
                      ·
                        rfl

theorem cell23_974896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_974896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974896 prefixEnd_974896 := by exact prefixLift 974896
  have htrace : WordTrace (prefixWord ++ tailWord_974896) baseStart_974896 baseEnd_974896 := by
    simpa [prefixWord, tailWord_974896, baseEnd_974896] using wordTrace_append hprefix tailTrace_974896
  have hstable : (prefixWord ++ tailWord_974896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974896).length < 2 ^ (prefixWord ++ tailWord_974896).sum := by decide
  have hdescent : baseEnd_974896 < baseStart_974896 := by decide
  rcases family_descends (prefixWord ++ tailWord_974896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974910 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_974910 : Nat := 118140960795 + 974910 * 2 ^ 59
def prefixEnd_974910 : Nat := 4983230072969 + 3 ^ 40 * 974910 * 2
def baseEnd_974910 : Nat := 500597424874885893841477

theorem tailTrace_974910 : CollatzResearch.WordTrace tailWord_974910 prefixEnd_974910 500597424874885893841477 := by
  unfold tailWord_974910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444736112259380777157273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23705259265383364144838789 4444736112259380777157273)
  ·
    refine ⟨3333552084194535582867955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4444736112259380777157273 3333552084194535582867955)
    ·
      refine ⟨5000328126291803374301933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3333552084194535582867955 5000328126291803374301933)
      ·
        refine ⟨1875123047359426265363225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5000328126291803374301933 1875123047359426265363225)
        ·
          refine ⟨1406342285519569699022419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875123047359426265363225 1406342285519569699022419)
          ·
            refine ⟨2109513428279354548533629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406342285519569699022419 2109513428279354548533629)
            ·
              refine ⟨791067535604757955700111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2109513428279354548533629 791067535604757955700111)
              ·
                refine ⟨1186601303407136933550167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791067535604757955700111 1186601303407136933550167)
                ·
                  refine ⟨1779901955110705400325251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186601303407136933550167 1779901955110705400325251)
                  ·
                    refine ⟨2669852932666058100487877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1779901955110705400325251 2669852932666058100487877)
                    ·
                      refine ⟨500597424874885893841477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2669852932666058100487877 500597424874885893841477)
                      ·
                        rfl

theorem cell23_974910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_974910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974910 prefixEnd_974910 := by exact prefixLift 974910
  have htrace : WordTrace (prefixWord ++ tailWord_974910) baseStart_974910 baseEnd_974910 := by
    simpa [prefixWord, tailWord_974910, baseEnd_974910] using wordTrace_append hprefix tailTrace_974910
  have hstable : (prefixWord ++ tailWord_974910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974910).length < 2 ^ (prefixWord ++ tailWord_974910).sum := by decide
  have hdescent : baseEnd_974910 < baseStart_974910 := by decide
  rcases family_descends (prefixWord ++ tailWord_974910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974936 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 3, 3, 2]
def baseStart_974936 : Nat := 118140960795 + 974936 * 2 ^ 59
def prefixEnd_974936 : Nat := 4983230072969 + 3 ^ 40 * 974936 * 2
def baseEnd_974936 : Nat := 500610775371902792116357

theorem tailTrace_974936 : CollatzResearch.WordTrace tailWord_974936 prefixEnd_974936 500610775371902792116357 := by
  unfold tailWord_974936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779418597990426328852331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23705891463987235105136441 17779418597990426328852331)
  ·
    refine ⟨26669127896985639493278497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17779418597990426328852331 26669127896985639493278497)
    ·
      refine ⟨20001845922739229619958873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26669127896985639493278497 20001845922739229619958873)
      ·
        refine ⟨15001384442054422214969155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20001845922739229619958873 15001384442054422214969155)
        ·
          refine ⟨22502076663081633322453733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15001384442054422214969155 22502076663081633322453733)
          ·
            refine ⟨4219139374327806247960075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22502076663081633322453733 4219139374327806247960075)
            ·
              refine ⟨6328709061491709371940113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219139374327806247960075 6328709061491709371940113)
              ·
                refine ⟨4746531796118782028955085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6328709061491709371940113 4746531796118782028955085)
                ·
                  refine ⟨1779949423544543260858157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4746531796118782028955085 1779949423544543260858157)
                  ·
                    refine ⟨667481033829203722821809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1779949423544543260858157 667481033829203722821809)
                    ·
                      refine ⟨500610775371902792116357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667481033829203722821809 500610775371902792116357)
                      ·
                        rfl

theorem cell23_974936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_974936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974936 prefixEnd_974936 := by exact prefixLift 974936
  have htrace : WordTrace (prefixWord ++ tailWord_974936) baseStart_974936 baseEnd_974936 := by
    simpa [prefixWord, tailWord_974936, baseEnd_974936] using wordTrace_append hprefix tailTrace_974936
  have hstable : (prefixWord ++ tailWord_974936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974936).length < 2 ^ (prefixWord ++ tailWord_974936).sum := by decide
  have hdescent : baseEnd_974936 < baseStart_974936 := by decide
  rcases family_descends (prefixWord ++ tailWord_974936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974977 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_974977 : Nat := 118140960795 + 974977 * 2 ^ 59
def prefixEnd_974977 : Nat := 4983230072969 + 3 ^ 40 * 974977 * 2
def baseEnd_974977 : Nat := 500631828078737131703669

theorem tailTrace_974977 : CollatzResearch.WordTrace tailWord_974977 prefixEnd_974977 500631828078737131703669 := by
  unfold tailWord_974977
  simp only [CollatzResearch.WordTrace]
  refine ⟨35560332588832316659947185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23706888392554877773298123 35560332588832316659947185)
  ·
    refine ⟨26670249441624237494960389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35560332588832316659947185 26670249441624237494960389)
    ·
      refine ⟨5000671770304544530305073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26670249441624237494960389 5000671770304544530305073)
      ·
        refine ⟨3750503827728408397728805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000671770304544530305073 3750503827728408397728805)
        ·
          refine ⟨703219467699076574574151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3750503827728408397728805 703219467699076574574151)
          ·
            refine ⟨1054829201548614861861227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703219467699076574574151 1054829201548614861861227)
            ·
              refine ⟨1582243802322922292791841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054829201548614861861227 1582243802322922292791841)
              ·
                refine ⟨1186682851742191719593881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582243802322922292791841 1186682851742191719593881)
                ·
                  refine ⟨890012138806643789695411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1186682851742191719593881 890012138806643789695411)
                  ·
                    refine ⟨1335018208209965684543117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 890012138806643789695411 1335018208209965684543117)
                    ·
                      refine ⟨500631828078737131703669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1335018208209965684543117 500631828078737131703669)
                      ·
                        rfl

theorem cell23_974977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_974977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974977 prefixEnd_974977 := by exact prefixLift 974977
  have htrace : WordTrace (prefixWord ++ tailWord_974977) baseStart_974977 baseEnd_974977 := by
    simpa [prefixWord, tailWord_974977, baseEnd_974977] using wordTrace_append hprefix tailTrace_974977
  have hstable : (prefixWord ++ tailWord_974977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974977).length < 2 ^ (prefixWord ++ tailWord_974977).sum := by decide
  have hdescent : baseEnd_974977 < baseStart_974977 := by decide
  rcases family_descends (prefixWord ++ tailWord_974977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974979 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4]
def baseStart_974979 : Nat := 118140960795 + 974979 * 2 ^ 59
def prefixEnd_974979 : Nat := 4983230072969 + 3 ^ 40 * 974979 * 2
def baseEnd_974979 : Nat := 500632855040046123878659

theorem tailTrace_974979 : CollatzResearch.WordTrace tailWord_974979 prefixEnd_974979 500632855040046123878659 := by
  unfold tailWord_974979
  simp only [CollatzResearch.WordTrace]
  refine ⟨35560405534825071001519991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23706937023216714001013327 35560405534825071001519991)
  ·
    refine ⟨53340608302237606502279987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35560405534825071001519991 53340608302237606502279987)
    ·
      refine ⟨80010912453356409753419981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53340608302237606502279987 80010912453356409753419981)
      ·
        refine ⟨30004092170008653657532493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80010912453356409753419981 30004092170008653657532493)
        ·
          refine ⟨11251534563753245121574685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30004092170008653657532493 11251534563753245121574685)
          ·
            refine ⟨4219325461407466920590507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11251534563753245121574685 4219325461407466920590507)
            ·
              refine ⟨6328988192111200380885761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219325461407466920590507 6328988192111200380885761)
              ·
                refine ⟨4746741144083400285664321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6328988192111200380885761 4746741144083400285664321)
                ·
                  refine ⟨3560055858062550214248241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746741144083400285664321 3560055858062550214248241)
                  ·
                    refine ⟨2670041893546912660686181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3560055858062550214248241 2670041893546912660686181)
                    ·
                      refine ⟨500632855040046123878659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2670041893546912660686181 500632855040046123878659)
                      ·
                        rfl

theorem cell23_974979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_974979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_974979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_974979 prefixEnd_974979 := by exact prefixLift 974979
  have htrace : WordTrace (prefixWord ++ tailWord_974979) baseStart_974979 baseEnd_974979 := by
    simpa [prefixWord, tailWord_974979, baseEnd_974979] using wordTrace_append hprefix tailTrace_974979
  have hstable : (prefixWord ++ tailWord_974979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974979).length < 2 ^ (prefixWord ++ tailWord_974979).sum := by decide
  have hdescent : baseEnd_974979 < baseStart_974979 := by decide
  rcases family_descends (prefixWord ++ tailWord_974979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975000 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 1, 4, 2]
def baseStart_975000 : Nat := 118140960795 + 975000 * 2 ^ 59
def prefixEnd_975000 : Nat := 4983230072969 + 3 ^ 40 * 975000 * 2
def baseEnd_975000 : Nat := 500643638133790541716063

theorem tailTrace_975000 : CollatzResearch.WordTrace tailWord_975000 prefixEnd_975000 500643638133790541716063 := by
  unfold tailWord_975000
  simp only [CollatzResearch.WordTrace]
  refine ⟨17780585733874495794017227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23707447645165994392022969 17780585733874495794017227)
  ·
    refine ⟨26670878600811743691025841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17780585733874495794017227 26670878600811743691025841)
    ·
      refine ⟨20003158950608807768269381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26670878600811743691025841 20003158950608807768269381)
      ·
        refine ⟨3750592303239151456550509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20003158950608807768269381 3750592303239151456550509)
        ·
          refine ⟨1406472113714681796206441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3750592303239151456550509 1406472113714681796206441)
          ·
            refine ⟨1054854085286011347154831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406472113714681796206441 1054854085286011347154831)
            ·
              refine ⟨1582281127929017020732247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054854085286011347154831 1582281127929017020732247)
              ·
                refine ⟨2373421691893525531098371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582281127929017020732247 2373421691893525531098371)
                ·
                  refine ⟨3560132537840288296647557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373421691893525531098371 3560132537840288296647557)
                  ·
                    refine ⟨667524850845054055621417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560132537840288296647557 667524850845054055621417)
                    ·
                      refine ⟨500643638133790541716063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667524850845054055621417 500643638133790541716063)
                      ·
                        rfl

theorem cell23_975000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_975000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975000 prefixEnd_975000 := by exact prefixLift 975000
  have htrace : WordTrace (prefixWord ++ tailWord_975000) baseStart_975000 baseEnd_975000 := by
    simpa [prefixWord, tailWord_975000, baseEnd_975000] using wordTrace_append hprefix tailTrace_975000
  have hstable : (prefixWord ++ tailWord_975000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975000).length < 2 ^ (prefixWord ++ tailWord_975000).sum := by decide
  have hdescent : baseEnd_975000 < baseStart_975000 := by decide
  rcases family_descends (prefixWord ++ tailWord_975000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975066 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_975066 : Nat := 118140960795 + 975066 * 2 ^ 59
def prefixEnd_975066 : Nat := 4983230072969 + 3 ^ 40 * 975066 * 2
def baseEnd_975066 : Nat := 166892509285662427830253

theorem tailTrace_975066 : CollatzResearch.WordTrace tailWord_975066 prefixEnd_975066 166892509285662427830253 := by
  unfold tailWord_975066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8890894671377471214984263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23709052457006589906624701 8890894671377471214984263)
  ·
    refine ⟨13336342007066206822476395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8890894671377471214984263 13336342007066206822476395)
    ·
      refine ⟨20004513010599310233714593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13336342007066206822476395 20004513010599310233714593)
      ·
        refine ⟨15003384757949482675285945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20004513010599310233714593 15003384757949482675285945)
        ·
          refine ⟨11252538568462112006464459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15003384757949482675285945 11252538568462112006464459)
          ·
            refine ⟨16878807852693168009696689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11252538568462112006464459 16878807852693168009696689)
            ·
              refine ⟨12659105889519876007272517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16878807852693168009696689 12659105889519876007272517)
              ·
                refine ⟨2373582354284976751363597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12659105889519876007272517 2373582354284976751363597)
                ·
                  refine ⟨890093382856866281761349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2373582354284976751363597 890093382856866281761349)
                  ·
                    refine ⟨166892509285662427830253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890093382856866281761349 166892509285662427830253)
                    ·
                      rfl

theorem cell23_975066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_975066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975066 prefixEnd_975066 := by exact prefixLift 975066
  have htrace : WordTrace (prefixWord ++ tailWord_975066) baseStart_975066 baseEnd_975066 := by
    simpa [prefixWord, tailWord_975066, baseEnd_975066] using wordTrace_append hprefix tailTrace_975066
  have hstable : (prefixWord ++ tailWord_975066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975066).length < 2 ^ (prefixWord ++ tailWord_975066).sum := by decide
  have hdescent : baseEnd_975066 < baseStart_975066 := by decide
  rcases family_descends (prefixWord ++ tailWord_975066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975083 : List Nat := [1, 1, 1, 1, 2, 5, 2, 5, 1, 4]
def baseStart_975083 : Nat := 118140960795 + 975083 * 2 ^ 59
def prefixEnd_975083 : Nat := 4983230072969 + 3 ^ 40 * 975083 * 2
def baseEnd_975083 : Nat := 166895419009371238992727

theorem tailTrace_975083 : CollatzResearch.WordTrace tailWord_975083 prefixEnd_975083 166895419009371238992727 := by
  unfold tailWord_975083
  simp only [CollatzResearch.WordTrace]
  refine ⟨35564198726448296763305903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23709465817632197842203935 35564198726448296763305903)
  ·
    refine ⟨53346298089672445144958855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35564198726448296763305903 53346298089672445144958855)
    ·
      refine ⟨80019447134508667717438283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53346298089672445144958855 80019447134508667717438283)
      ·
        refine ⟨120029170701763001576157425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80019447134508667717438283 120029170701763001576157425)
        ·
          refine ⟨90021878026322251182118069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120029170701763001576157425 90021878026322251182118069)
          ·
            refine ⟨8439551064967711048323569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90021878026322251182118069 8439551064967711048323569)
            ·
              refine ⟨6329663298725783286242677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8439551064967711048323569 6329663298725783286242677)
              ·
                refine ⟨593405934255542183085251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6329663298725783286242677 593405934255542183085251)
                ·
                  refine ⟨890108901383313274627877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593405934255542183085251 890108901383313274627877)
                  ·
                    refine ⟨166895419009371238992727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890108901383313274627877 166895419009371238992727)
                    ·
                      rfl

theorem cell23_975083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 4].length) (baseStart_975083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975083 prefixEnd_975083 := by exact prefixLift 975083
  have htrace : WordTrace (prefixWord ++ tailWord_975083) baseStart_975083 baseEnd_975083 := by
    simpa [prefixWord, tailWord_975083, baseEnd_975083] using wordTrace_append hprefix tailTrace_975083
  have hstable : (prefixWord ++ tailWord_975083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975083).length < 2 ^ (prefixWord ++ tailWord_975083).sum := by decide
  have hdescent : baseEnd_975083 < baseStart_975083 := by decide
  rcases family_descends (prefixWord ++ tailWord_975083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975100 : List Nat := [2, 2, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_975100 : Nat := 118140960795 + 975100 * 2 ^ 59
def prefixEnd_975100 : Nat := 4983230072969 + 3 ^ 40 * 975100 * 2
def baseEnd_975100 : Nat := 166898328733080050155201

theorem tailTrace_975100 : CollatzResearch.WordTrace tailWord_975100 prefixEnd_975100 166898328733080050155201 := by
  unfold tailWord_975100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17782409383693354333337377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23709879178257805777783169 17782409383693354333337377)
  ·
    refine ⟨13336807037770015750003033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17782409383693354333337377 13336807037770015750003033)
    ·
      refine ⟨10002605278327511812502275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13336807037770015750003033 10002605278327511812502275)
      ·
        refine ⟨15003907917491267718753413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10002605278327511812502275 15003907917491267718753413)
        ·
          refine ⟨2813232734529612697266265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15003907917491267718753413 2813232734529612697266265)
          ·
            refine ⟨2109924550897209522949699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2813232734529612697266265 2109924550897209522949699)
            ·
              refine ⟨3164886826345814284424549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109924550897209522949699 3164886826345814284424549)
              ·
                refine ⟨593416279939840178329603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3164886826345814284424549 593416279939840178329603)
                ·
                  refine ⟨890124419909760267494405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593416279939840178329603 890124419909760267494405)
                  ·
                    refine ⟨166898328733080050155201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890124419909760267494405 166898328733080050155201)
                    ·
                      rfl

theorem cell23_975100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_975100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975100 prefixEnd_975100 := by exact prefixLift 975100
  have htrace : WordTrace (prefixWord ++ tailWord_975100) baseStart_975100 baseEnd_975100 := by
    simpa [prefixWord, tailWord_975100, baseEnd_975100] using wordTrace_append hprefix tailTrace_975100
  have hstable : (prefixWord ++ tailWord_975100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975100).length < 2 ^ (prefixWord ++ tailWord_975100).sum := by decide
  have hdescent : baseEnd_975100 < baseStart_975100 := by decide
  rcases family_descends (prefixWord ++ tailWord_975100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975134 : List Nat := [4, 3, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_975134 : Nat := 118140960795 + 975134 * 2 ^ 59
def prefixEnd_975134 : Nat := 4983230072969 + 3 ^ 40 * 975134 * 2
def baseEnd_975134 : Nat := 166904148180497672480149

theorem tailTrace_975134 : CollatzResearch.WordTrace tailWord_975134 prefixEnd_975134 166904148180497672480149 := by
  unfold tailWord_975134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445757356157941559176557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23710705899509021648941637 4445757356157941559176557)
  ·
    refine ⟨1667159008559228084691209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4445757356157941559176557 1667159008559228084691209)
    ·
      refine ⟨1250369256419421063518407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1667159008559228084691209 1250369256419421063518407)
      ·
        refine ⟨1875553884629131595277611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250369256419421063518407 1875553884629131595277611)
        ·
          refine ⟨2813330826943697392916417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875553884629131595277611 2813330826943697392916417)
          ·
            refine ⟨2109998120207773044687313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2813330826943697392916417 2109998120207773044687313)
            ·
              refine ⟨1582498590155829783515485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109998120207773044687313 1582498590155829783515485)
              ·
                refine ⟨593436971308436168818307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582498590155829783515485 593436971308436168818307)
                ·
                  refine ⟨890155456962654253227461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593436971308436168818307 890155456962654253227461)
                  ·
                    refine ⟨166904148180497672480149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890155456962654253227461 166904148180497672480149)
                    ·
                      rfl

theorem cell23_975134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_975134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975134 prefixEnd_975134 := by exact prefixLift 975134
  have htrace : WordTrace (prefixWord ++ tailWord_975134) baseStart_975134 baseEnd_975134 := by
    simpa [prefixWord, tailWord_975134, baseEnd_975134] using wordTrace_append hprefix tailTrace_975134
  have hstable : (prefixWord ++ tailWord_975134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975134).length < 2 ^ (prefixWord ++ tailWord_975134).sum := by decide
  have hdescent : baseEnd_975134 < baseStart_975134 := by decide
  rcases family_descends (prefixWord ++ tailWord_975134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975180 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 3, 2, 2]
def baseStart_975180 : Nat := 118140960795 + 975180 * 2 ^ 59
def prefixEnd_975180 : Nat := 4983230072969 + 3 ^ 40 * 975180 * 2
def baseEnd_975180 : Nat := 500736064651599837465235

theorem tailTrace_975180 : CollatzResearch.WordTrace tailWord_975180 prefixEnd_975180 500736064651599837465235 := by
  unfold tailWord_975180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783868303548441164793497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23711824404731254886391329 17783868303548441164793497)
  ·
    refine ⟨13337901227661330873595123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17783868303548441164793497 13337901227661330873595123)
    ·
      refine ⟨20006851841491996310392685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13337901227661330873595123 20006851841491996310392685)
      ·
        refine ⟨7502569440559498616397257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20006851841491996310392685 7502569440559498616397257)
        ·
          refine ⟨5626927080419623962297943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7502569440559498616397257 5626927080419623962297943)
          ·
            refine ⟨8440390620629435943446915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626927080419623962297943 8440390620629435943446915)
            ·
              refine ⟨12660585930944153915170373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8440390620629435943446915 12660585930944153915170373)
              ·
                refine ⟨2373859862052028859094445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12660585930944153915170373 2373859862052028859094445)
                ·
                  refine ⟨890197448269510822160417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2373859862052028859094445 890197448269510822160417)
                  ·
                    refine ⟨667648086202133116620313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 890197448269510822160417 667648086202133116620313)
                    ·
                      refine ⟨500736064651599837465235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667648086202133116620313 500736064651599837465235)
                      ·
                        rfl

theorem cell23_975180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_975180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975180 prefixEnd_975180 := by exact prefixLift 975180
  have htrace : WordTrace (prefixWord ++ tailWord_975180) baseStart_975180 baseEnd_975180 := by
    simpa [prefixWord, tailWord_975180, baseEnd_975180] using wordTrace_append hprefix tailTrace_975180
  have hstable : (prefixWord ++ tailWord_975180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975180).length < 2 ^ (prefixWord ++ tailWord_975180).sum := by decide
  have hdescent : baseEnd_975180 < baseStart_975180 := by decide
  rcases family_descends (prefixWord ++ tailWord_975180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975240 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_975240 : Nat := 118140960795 + 975240 * 2 ^ 59
def prefixEnd_975240 : Nat := 4983230072969 + 3 ^ 40 * 975240 * 2
def baseEnd_975240 : Nat := 500766873490869602714959

theorem tailTrace_975240 : CollatzResearch.WordTrace tailWord_975240 prefixEnd_975240 500766873490869602714959 := by
  unfold tailWord_975240
  simp only [CollatzResearch.WordTrace]
  refine ⟨17784962493439756288385587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23713283324586341717847449 17784962493439756288385587)
  ·
    refine ⟨26677443740159634432578381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17784962493439756288385587 26677443740159634432578381)
    ·
      refine ⟨10004041402559862912216893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26677443740159634432578381 10004041402559862912216893)
      ·
        refine ⟨3751515525959948592081335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10004041402559862912216893 3751515525959948592081335)
        ·
          refine ⟨5627273288939922888122003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751515525959948592081335 5627273288939922888122003)
          ·
            refine ⟨8440909933409884332183005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627273288939922888122003 8440909933409884332183005)
            ·
              refine ⟨3165341225028706624568627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8440909933409884332183005 3165341225028706624568627)
              ·
                refine ⟨4748011837543059936852941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165341225028706624568627 4748011837543059936852941)
                ·
                  refine ⟨1780504439078647476319853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4748011837543059936852941 1780504439078647476319853)
                  ·
                    refine ⟨667689164654492803619945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1780504439078647476319853 667689164654492803619945)
                    ·
                      refine ⟨500766873490869602714959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667689164654492803619945 500766873490869602714959)
                      ·
                        rfl

theorem cell23_975240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_975240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975240 prefixEnd_975240 := by exact prefixLift 975240
  have htrace : WordTrace (prefixWord ++ tailWord_975240) baseStart_975240 baseEnd_975240 := by
    simpa [prefixWord, tailWord_975240, baseEnd_975240] using wordTrace_append hprefix tailTrace_975240
  have hstable : (prefixWord ++ tailWord_975240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975240).length < 2 ^ (prefixWord ++ tailWord_975240).sum := by decide
  have hdescent : baseEnd_975240 < baseStart_975240 := by decide
  rcases family_descends (prefixWord ++ tailWord_975240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975257 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 1, 3, 2]
def baseStart_975257 : Nat := 118140960795 + 975257 * 2 ^ 59
def prefixEnd_975257 : Nat := 4983230072969 + 3 ^ 40 * 975257 * 2
def baseEnd_975257 : Nat := 500775602661996036202381

theorem tailTrace_975257 : CollatzResearch.WordTrace tailWord_975257 prefixEnd_975257 500775602661996036202381 := by
  unfold tailWord_975257
  simp only [CollatzResearch.WordTrace]
  refine ⟨35570545027817924480140025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23713696685211949653426683 35570545027817924480140025)
  ·
    refine ⟨26677908770863443360105019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35570545027817924480140025 26677908770863443360105019)
    ·
      refine ⟨40016863156295165040157529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26677908770863443360105019 40016863156295165040157529)
      ·
        refine ⟨30012647367221373780118147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40016863156295165040157529 30012647367221373780118147)
        ·
          refine ⟨45018971050832060670177221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30012647367221373780118147 45018971050832060670177221)
          ·
            refine ⟨8441057072031011375658229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45018971050832060670177221 8441057072031011375658229)
            ·
              refine ⟨791349100502907316467959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8441057072031011375658229 791349100502907316467959)
              ·
                refine ⟨1187023650754360974701939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791349100502907316467959 1187023650754360974701939)
                ·
                  refine ⟨1780535476131541462052909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187023650754360974701939 1780535476131541462052909)
                  ·
                    refine ⟨667700803549328048269841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1780535476131541462052909 667700803549328048269841)
                    ·
                      refine ⟨500775602661996036202381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667700803549328048269841 500775602661996036202381)
                      ·
                        rfl

theorem cell23_975257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_975257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975257 prefixEnd_975257 := by exact prefixLift 975257
  have htrace : WordTrace (prefixWord ++ tailWord_975257) baseStart_975257 baseEnd_975257 := by
    simpa [prefixWord, tailWord_975257, baseEnd_975257] using wordTrace_append hprefix tailTrace_975257
  have hstable : (prefixWord ++ tailWord_975257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975257).length < 2 ^ (prefixWord ++ tailWord_975257).sum := by decide
  have hdescent : baseEnd_975257 < baseStart_975257 := by decide
  rcases family_descends (prefixWord ++ tailWord_975257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975265 : List Nat := [1, 2, 3, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_975265 : Nat := 118140960795 + 975265 * 2 ^ 59
def prefixEnd_975265 : Nat := 4983230072969 + 3 ^ 40 * 975265 * 2
def baseEnd_975265 : Nat := 500779710507232004902345

theorem tailTrace_975265 : CollatzResearch.WordTrace tailWord_975265 prefixEnd_975265 500779710507232004902345 := by
  unfold tailWord_975265
  simp only [CollatzResearch.WordTrace]
  refine ⟨35570836811788941846431249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23713891207859294564287499 35570836811788941846431249)
  ·
    refine ⟨26678127608841706384823437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35570836811788941846431249 26678127608841706384823437)
    ·
      refine ⟨10004297853315639894308789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26678127608841706384823437 10004297853315639894308789)
      ·
        refine ⟨937902923748341240091449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10004297853315639894308789 937902923748341240091449)
        ·
          refine ⟨703427192811255930068587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937902923748341240091449 703427192811255930068587)
          ·
            refine ⟨1055140789216883895102881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703427192811255930068587 1055140789216883895102881)
            ·
              refine ⟨791355591912662921327161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055140789216883895102881 791355591912662921327161)
              ·
                refine ⟨593516693934497190995371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791355591912662921327161 593516693934497190995371)
                ·
                  refine ⟨890275040901745786493057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593516693934497190995371 890275040901745786493057)
                  ·
                    refine ⟨667706280676309339869793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 890275040901745786493057 667706280676309339869793)
                    ·
                      refine ⟨500779710507232004902345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667706280676309339869793 500779710507232004902345)
                      ·
                        rfl

theorem cell23_975265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_975265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975265 prefixEnd_975265 := by exact prefixLift 975265
  have htrace : WordTrace (prefixWord ++ tailWord_975265) baseStart_975265 baseEnd_975265 := by
    simpa [prefixWord, tailWord_975265, baseEnd_975265] using wordTrace_append hprefix tailTrace_975265
  have hstable : (prefixWord ++ tailWord_975265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975265).length < 2 ^ (prefixWord ++ tailWord_975265).sum := by decide
  have hdescent : baseEnd_975265 < baseStart_975265 := by decide
  rcases family_descends (prefixWord ++ tailWord_975265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975276 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 7]
def baseStart_975276 : Nat := 118140960795 + 975276 * 2 ^ 59
def prefixEnd_975276 : Nat := 4983230072969 + 3 ^ 40 * 975276 * 2
def baseEnd_975276 : Nat := 55642817643825717984977

theorem tailTrace_975276 : CollatzResearch.WordTrace tailWord_975276 prefixEnd_975276 55642817643825717984977 := by
  unfold tailWord_975276
  simp only [CollatzResearch.WordTrace]
  refine ⟨17785619007374545362540841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23714158676499393816721121 17785619007374545362540841)
  ·
    refine ⟨13339214255530909021905631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17785619007374545362540841 13339214255530909021905631)
    ·
      refine ⟨20008821383296363532858447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13339214255530909021905631 20008821383296363532858447)
      ·
        refine ⟨30013232074944545299287671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20008821383296363532858447 30013232074944545299287671)
        ·
          refine ⟨45019848112416817948931507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30013232074944545299287671 45019848112416817948931507)
          ·
            refine ⟨67529772168625226923397261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45019848112416817948931507 67529772168625226923397261)
            ·
              refine ⟨25323664563234460096273973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67529772168625226923397261 25323664563234460096273973)
              ·
                refine ⟨2374093552803230634025685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25323664563234460096273973 2374093552803230634025685)
                ·
                  refine ⟨55642817643825717984977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2374093552803230634025685 55642817643825717984977)
                  ·
                    rfl

theorem cell23_975276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_975276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975276 prefixEnd_975276 := by exact prefixLift 975276
  have htrace : WordTrace (prefixWord ++ tailWord_975276) baseStart_975276 baseEnd_975276 := by
    simpa [prefixWord, tailWord_975276, baseEnd_975276] using wordTrace_append hprefix tailTrace_975276
  have hstable : (prefixWord ++ tailWord_975276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975276).length < 2 ^ (prefixWord ++ tailWord_975276).sum := by decide
  have hdescent : baseEnd_975276 < baseStart_975276 := by decide
  rcases family_descends (prefixWord ++ tailWord_975276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975287 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 2, 2, 2]
def baseStart_975287 : Nat := 118140960795 + 975287 * 2 ^ 59
def prefixEnd_975287 : Nat := 4983230072969 + 3 ^ 40 * 975287 * 2
def baseEnd_975287 : Nat := 500791007081630918827243

theorem tailTrace_975287 : CollatzResearch.WordTrace tailWord_975287 prefixEnd_975287 500791007081630918827243 := by
  unfold tailWord_975287
  simp only [CollatzResearch.WordTrace]
  refine ⟨35571639217709239603732115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23714426145139493069154743 35571639217709239603732115)
  ·
    refine ⟨53357458826563859405598173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35571639217709239603732115 53357458826563859405598173)
    ·
      refine ⟨20009047059961447277099315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53357458826563859405598173 20009047059961447277099315)
      ·
        refine ⟨30013570589942170915648973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20009047059961447277099315 30013570589942170915648973)
        ·
          refine ⟨11255088971228314093368365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30013570589942170915648973 11255088971228314093368365)
          ·
            refine ⟨4220658364210617785013137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11255088971228314093368365 4220658364210617785013137)
            ·
              refine ⟨3165493773157963338759853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220658364210617785013137 3165493773157963338759853)
              ·
                refine ⟨1187060164934236252034945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3165493773157963338759853 1187060164934236252034945)
                ·
                  refine ⟨890295123700677189026209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187060164934236252034945 890295123700677189026209)
                  ·
                    refine ⟨667721342775507891769657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 890295123700677189026209 667721342775507891769657)
                    ·
                      refine ⟨500791007081630918827243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667721342775507891769657 500791007081630918827243)
                      ·
                        rfl

theorem cell23_975287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_975287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975287 prefixEnd_975287 := by exact prefixLift 975287
  have htrace : WordTrace (prefixWord ++ tailWord_975287) baseStart_975287 baseEnd_975287 := by
    simpa [prefixWord, tailWord_975287, baseEnd_975287] using wordTrace_append hprefix tailTrace_975287
  have hstable : (prefixWord ++ tailWord_975287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975287).length < 2 ^ (prefixWord ++ tailWord_975287).sum := by decide
  have hdescent : baseEnd_975287 < baseStart_975287 := by decide
  rcases family_descends (prefixWord ++ tailWord_975287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975293 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 7]
def baseStart_975293 : Nat := 118140960795 + 975293 * 2 ^ 59
def prefixEnd_975293 : Nat := 4983230072969 + 3 ^ 40 * 975293 * 2
def baseEnd_975293 : Nat := 55643787551728655039135

theorem tailTrace_975293 : CollatzResearch.WordTrace tailWord_975293 prefixEnd_975293 55643787551728655039135 := by
  unfold tailWord_975293
  simp only [CollatzResearch.WordTrace]
  refine ⟨35571858055687502628450533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23714572037125001752300355 35571858055687502628450533)
  ·
    refine ⟨6669723385441406742834475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35571858055687502628450533 6669723385441406742834475)
    ·
      refine ⟨10004585078162110114251713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6669723385441406742834475 10004585078162110114251713)
      ·
        refine ⟨7503438808621582585688785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10004585078162110114251713 7503438808621582585688785)
        ·
          refine ⟨5627579106466186939266589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7503438808621582585688785 5627579106466186939266589)
          ·
            refine ⟨2110342164924820102224971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5627579106466186939266589 2110342164924820102224971)
            ·
              refine ⟨3165513247387230153337457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110342164924820102224971 3165513247387230153337457)
              ·
                refine ⟨2374134935540422615003093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3165513247387230153337457 2374134935540422615003093)
                ·
                  refine ⟨55643787551728655039135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2374134935540422615003093 55643787551728655039135)
                  ·
                    rfl

theorem cell23_975293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_975293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975293 prefixEnd_975293 := by exact prefixLift 975293
  have htrace : WordTrace (prefixWord ++ tailWord_975293) baseStart_975293 baseEnd_975293 := by
    simpa [prefixWord, tailWord_975293, baseEnd_975293] using wordTrace_append hprefix tailTrace_975293
  have hstable : (prefixWord ++ tailWord_975293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975293).length < 2 ^ (prefixWord ++ tailWord_975293).sum := by decide
  have hdescent : baseEnd_975293 < baseStart_975293 := by decide
  rcases family_descends (prefixWord ++ tailWord_975293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975363 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 3]
def baseStart_975363 : Nat := 118140960795 + 975363 * 2 ^ 59
def prefixEnd_975363 : Nat := 4983230072969 + 3 ^ 40 * 975363 * 2
def baseEnd_975363 : Nat := 500830031611372621476893

theorem tailTrace_975363 : CollatzResearch.WordTrace tailWord_975363 prefixEnd_975363 500830031611372621476893 := by
  unfold tailWord_975363
  simp only [CollatzResearch.WordTrace]
  refine ⟨35574411165433904583498743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23716274110289269722332495 35574411165433904583498743)
  ·
    refine ⟨53361616748150856875248115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35574411165433904583498743 53361616748150856875248115)
    ·
      refine ⟨80042425122226285312872173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53361616748150856875248115 80042425122226285312872173)
      ·
        refine ⟨30015909420834856992327065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80042425122226285312872173 30015909420834856992327065)
        ·
          refine ⟨22511932065626142744245299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30015909420834856992327065 22511932065626142744245299)
          ·
            refine ⟨33767898098439214116367949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22511932065626142744245299 33767898098439214116367949)
            ·
              refine ⟨12662961786914705293637981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33767898098439214116367949 12662961786914705293637981)
              ·
                refine ⟨4748610670093014485114243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12662961786914705293637981 4748610670093014485114243)
                ·
                  refine ⟨7122916005139521727671365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748610670093014485114243 7122916005139521727671365)
                  ·
                    refine ⟨1335546750963660323938381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122916005139521727671365 1335546750963660323938381)
                    ·
                      refine ⟨500830031611372621476893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1335546750963660323938381 500830031611372621476893)
                      ·
                        rfl

theorem cell23_975363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_975363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975363 prefixEnd_975363 := by exact prefixLift 975363
  have htrace : WordTrace (prefixWord ++ tailWord_975363) baseStart_975363 baseEnd_975363 := by
    simpa [prefixWord, tailWord_975363, baseEnd_975363] using wordTrace_append hprefix tailTrace_975363
  have hstable : (prefixWord ++ tailWord_975363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975363).length < 2 ^ (prefixWord ++ tailWord_975363).sum := by decide
  have hdescent : baseEnd_975363 < baseStart_975363 := by decide
  rcases family_descends (prefixWord ++ tailWord_975363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975414 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_975414 : Nat := 118140960795 + 975414 * 2 ^ 59
def prefixEnd_975414 : Nat := 4983230072969 + 3 ^ 40 * 975414 * 2
def baseEnd_975414 : Nat := 500856219124751921939159

theorem tailTrace_975414 : CollatzResearch.WordTrace tailWord_975414 prefixEnd_975414 500856219124751921939159 := by
  unfold tailWord_975414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223516955515571268350331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23717514192166093529070197 2223516955515571268350331)
  ·
    refine ⟨3335275433273356902525497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2223516955515571268350331 3335275433273356902525497)
    ·
      refine ⟨2501456574955017676894123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3335275433273356902525497 2501456574955017676894123)
      ·
        refine ⟨3752184862432526515341185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501456574955017676894123 3752184862432526515341185)
        ·
          refine ⟨2814138646824394886505889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3752184862432526515341185 2814138646824394886505889)
          ·
            refine ⟨2110603985118296164879417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814138646824394886505889 2110603985118296164879417)
            ·
              refine ⟨1582952988838722123659563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110603985118296164879417 1582952988838722123659563)
              ·
                refine ⟨2374429483258083185489345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582952988838722123659563 2374429483258083185489345)
                ·
                  refine ⟨1780822112443562389117009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2374429483258083185489345 1780822112443562389117009)
                  ·
                    refine ⟨1335616584332671791837757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1780822112443562389117009 1335616584332671791837757)
                    ·
                      refine ⟨500856219124751921939159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1335616584332671791837757 500856219124751921939159)
                      ·
                        rfl

theorem cell23_975414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_975414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975414 prefixEnd_975414 := by exact prefixLift 975414
  have htrace : WordTrace (prefixWord ++ tailWord_975414) baseStart_975414 baseEnd_975414 := by
    simpa [prefixWord, tailWord_975414, baseEnd_975414] using wordTrace_append hprefix tailTrace_975414
  have hstable : (prefixWord ++ tailWord_975414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975414).length < 2 ^ (prefixWord ++ tailWord_975414).sum := by decide
  have hdescent : baseEnd_975414 < baseStart_975414 := by decide
  rcases family_descends (prefixWord ++ tailWord_975414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975450 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2]
def baseStart_975450 : Nat := 118140960795 + 975450 * 2 ^ 59
def prefixEnd_975450 : Nat := 4983230072969 + 3 ^ 40 * 975450 * 2
def baseEnd_975450 : Nat := 500874704428313781088993

theorem tailTrace_975450 : CollatzResearch.WordTrace tailWord_975450 prefixEnd_975450 500874704428313781088993 := by
  unfold tailWord_975450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894396079029679610478951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23718389544079145627943869 8894396079029679610478951)
  ·
    refine ⟨13341594118544519415718427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894396079029679610478951 13341594118544519415718427)
    ·
      refine ⟨20012391177816779123577641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13341594118544519415718427 20012391177816779123577641)
      ·
        refine ⟨15009293383362584342683231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20012391177816779123577641 15009293383362584342683231)
        ·
          refine ⟨22513940075043876514024847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15009293383362584342683231 22513940075043876514024847)
          ·
            refine ⟨33770910112565814771037271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22513940075043876514024847 33770910112565814771037271)
            ·
              refine ⟨50656365168848722156555907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33770910112565814771037271 50656365168848722156555907)
              ·
                refine ⟨75984547753273083234833861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50656365168848722156555907 75984547753273083234833861)
                ·
                  refine ⟨14247102703738703106531349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75984547753273083234833861 14247102703738703106531349)
                  ·
                    refine ⟨667832939237751708118657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14247102703738703106531349 667832939237751708118657)
                    ·
                      refine ⟨500874704428313781088993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 667832939237751708118657 500874704428313781088993)
                      ·
                        rfl

theorem cell23_975450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_975450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975450 prefixEnd_975450 := by exact prefixLift 975450
  have htrace : WordTrace (prefixWord ++ tailWord_975450) baseStart_975450 baseEnd_975450 := by
    simpa [prefixWord, tailWord_975450, baseEnd_975450] using wordTrace_append hprefix tailTrace_975450
  have hstable : (prefixWord ++ tailWord_975450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975450).length < 2 ^ (prefixWord ++ tailWord_975450).sum := by decide
  have hdescent : baseEnd_975450 < baseStart_975450 := by decide
  rcases family_descends (prefixWord ++ tailWord_975450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975460 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_975460 : Nat := 118140960795 + 975460 * 2 ^ 59
def prefixEnd_975460 : Nat := 4983230072969 + 3 ^ 40 * 975460 * 2
def baseEnd_975460 : Nat := 166959946411619580654649

theorem tailTrace_975460 : CollatzResearch.WordTrace tailWord_975460 prefixEnd_975460 166959946411619580654649 := by
  unfold tailWord_975460
  simp only [CollatzResearch.WordTrace]
  refine ⟨17788974523041245074889917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23718632697388326766519889 17788974523041245074889917)
  ·
    refine ⟨6670865446140466903083719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17788974523041245074889917 6670865446140466903083719)
    ·
      refine ⟨10006298169210700354625579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6670865446140466903083719 10006298169210700354625579)
      ·
        refine ⟨15009447253816050531938369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10006298169210700354625579 15009447253816050531938369)
        ·
          refine ⟨11257085440362037898953777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15009447253816050531938369 11257085440362037898953777)
          ·
            refine ⟨8442814080271528424215333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11257085440362037898953777 8442814080271528424215333)
            ·
              refine ⟨1583027640050911579540375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8442814080271528424215333 1583027640050911579540375)
              ·
                refine ⟨2374541460076367369310563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583027640050911579540375 2374541460076367369310563)
                ·
                  refine ⟨3561812190114551053965845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374541460076367369310563 3561812190114551053965845)
                  ·
                    refine ⟨166959946411619580654649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3561812190114551053965845 166959946411619580654649)
                    ·
                      rfl

theorem cell23_975460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_975460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975460 prefixEnd_975460 := by exact prefixLift 975460
  have htrace : WordTrace (prefixWord ++ tailWord_975460) baseStart_975460 baseEnd_975460 := by
    simpa [prefixWord, tailWord_975460, baseEnd_975460] using wordTrace_append hprefix tailTrace_975460
  have hstable : (prefixWord ++ tailWord_975460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975460).length < 2 ^ (prefixWord ++ tailWord_975460).sum := by decide
  have hdescent : baseEnd_975460 < baseStart_975460 := by decide
  rcases family_descends (prefixWord ++ tailWord_975460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975478 : List Nat := [5, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_975478 : Nat := 118140960795 + 975478 * 2 ^ 59
def prefixEnd_975478 : Nat := 4983230072969 + 3 ^ 40 * 975478 * 2
def baseEnd_975478 : Nat := 500889081886639671538865

theorem tailTrace_975478 : CollatzResearch.WordTrace tailWord_975478 prefixEnd_975478 500889081886639671538865 := by
  unfold tailWord_975478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223662847501079951495943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23719070373344852815956725 2223662847501079951495943)
  ·
    refine ⟨3335494271251619927243915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2223662847501079951495943 3335494271251619927243915)
    ·
      refine ⟨5003241406877429890865873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3335494271251619927243915 5003241406877429890865873)
      ·
        refine ⟨3752431055158072418149405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5003241406877429890865873 3752431055158072418149405)
        ·
          refine ⟨1407161645684277156806027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3752431055158072418149405 1407161645684277156806027)
          ·
            refine ⟨2110742468526415735209041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407161645684277156806027 2110742468526415735209041)
            ·
              refine ⟨1583056851394811801406781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110742468526415735209041 1583056851394811801406781)
              ·
                refine ⟨593646319273054425527543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583056851394811801406781 593646319273054425527543)
                ·
                  refine ⟨890469478909581638291315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593646319273054425527543 890469478909581638291315)
                  ·
                    refine ⟨1335704218364372457436973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 890469478909581638291315 1335704218364372457436973)
                    ·
                      refine ⟨500889081886639671538865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1335704218364372457436973 500889081886639671538865)
                      ·
                        rfl

theorem cell23_975478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_975478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975478 prefixEnd_975478 := by exact prefixLift 975478
  have htrace : WordTrace (prefixWord ++ tailWord_975478) baseStart_975478 baseEnd_975478 := by
    simpa [prefixWord, tailWord_975478, baseEnd_975478] using wordTrace_append hprefix tailTrace_975478
  have hstable : (prefixWord ++ tailWord_975478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975478).length < 2 ^ (prefixWord ++ tailWord_975478).sum := by decide
  have hdescent : baseEnd_975478 < baseStart_975478 := by decide
  rcases family_descends (prefixWord ++ tailWord_975478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975517 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_975517 : Nat := 118140960795 + 975517 * 2 ^ 59
def prefixEnd_975517 : Nat := 4983230072969 + 3 ^ 40 * 975517 * 2
def baseEnd_975517 : Nat := 500909107632165018951185

theorem tailTrace_975517 : CollatzResearch.WordTrace tailWord_975517 prefixEnd_975517 500909107632165018951185 := by
  unfold tailWord_975517
  simp only [CollatzResearch.WordTrace]
  refine ⟨35580028006875988884604805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23720018671250659256403203 35580028006875988884604805)
  ·
    refine ⟨6671255251289247915863401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35580028006875988884604805 6671255251289247915863401)
    ·
      refine ⟨5003441438466935936897551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6671255251289247915863401 5003441438466935936897551)
      ·
        refine ⟨7505162157700403905346327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5003441438466935936897551 7505162157700403905346327)
        ·
          refine ⟨11257743236550605858019491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7505162157700403905346327 11257743236550605858019491)
          ·
            refine ⟨16886614854825908787029237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257743236550605858019491 16886614854825908787029237)
            ·
              refine ⟨1583120142639928948783991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16886614854825908787029237 1583120142639928948783991)
              ·
                refine ⟨2374680213959893423175987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583120142639928948783991 2374680213959893423175987)
                ·
                  refine ⟨3562020320939840134763981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374680213959893423175987 3562020320939840134763981)
                  ·
                    refine ⟨1335757620352440050536493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3562020320939840134763981 1335757620352440050536493)
                    ·
                      refine ⟨500909107632165018951185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1335757620352440050536493 500909107632165018951185)
                      ·
                        rfl

theorem cell23_975517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_975517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975517 prefixEnd_975517 := by exact prefixLift 975517
  have htrace : WordTrace (prefixWord ++ tailWord_975517) baseStart_975517 baseEnd_975517 := by
    simpa [prefixWord, tailWord_975517, baseEnd_975517] using wordTrace_append hprefix tailTrace_975517
  have hstable : (prefixWord ++ tailWord_975517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975517).length < 2 ^ (prefixWord ++ tailWord_975517).sum := by decide
  have hdescent : baseEnd_975517 < baseStart_975517 := by decide
  rcases family_descends (prefixWord ++ tailWord_975517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975523 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8]
def baseStart_975523 : Nat := 118140960795 + 975523 * 2 ^ 59
def prefixEnd_975523 : Nat := 4983230072969 + 3 ^ 40 * 975523 * 2
def baseEnd_975523 : Nat := 500912188516091995476157

theorem tailTrace_975523 : CollatzResearch.WordTrace tailWord_975523 prefixEnd_975523 500912188516091995476157 := by
  unfold tailWord_975523
  simp only [CollatzResearch.WordTrace]
  refine ⟨35580246844854251909323223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23720164563236167939548815 35580246844854251909323223)
  ·
    refine ⟨53370370267281377863984835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35580246844854251909323223 53370370267281377863984835)
    ·
      refine ⟨80055555400922066795977253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53370370267281377863984835 80055555400922066795977253)
      ·
        refine ⟨15010416637672887524245735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80055555400922066795977253 15010416637672887524245735)
        ·
          refine ⟨22515624956509331286368603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15010416637672887524245735 22515624956509331286368603)
          ·
            refine ⟨33773437434763996929552905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22515624956509331286368603 33773437434763996929552905)
            ·
              refine ⟨25330078076072997697164679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33773437434763996929552905 25330078076072997697164679)
              ·
                refine ⟨37995117114109496545747019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25330078076072997697164679 37995117114109496545747019)
                ·
                  refine ⟨56992675671164244818620529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37995117114109496545747019 56992675671164244818620529)
                  ·
                    refine ⟨42744506753373183613965397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56992675671164244818620529 42744506753373183613965397)
                    ·
                      refine ⟨500912188516091995476157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 42744506753373183613965397 500912188516091995476157)
                      ·
                        rfl

theorem cell23_975523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_975523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975523 prefixEnd_975523 := by exact prefixLift 975523
  have htrace : WordTrace (prefixWord ++ tailWord_975523) baseStart_975523 baseEnd_975523 := by
    simpa [prefixWord, tailWord_975523, baseEnd_975523] using wordTrace_append hprefix tailTrace_975523
  have hstable : (prefixWord ++ tailWord_975523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975523).length < 2 ^ (prefixWord ++ tailWord_975523).sum := by decide
  have hdescent : baseEnd_975523 < baseStart_975523 := by decide
  rcases family_descends (prefixWord ++ tailWord_975523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975644 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_975644 : Nat := 118140960795 + 975644 * 2 ^ 59
def prefixEnd_975644 : Nat := 4983230072969 + 3 ^ 40 * 975644 * 2
def baseEnd_975644 : Nat := 166991439891762007354367

theorem tailTrace_975644 : CollatzResearch.WordTrace tailWord_975644 prefixEnd_975644 166991439891762007354367 := by
  unfold tailWord_975644
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792330038707944787238993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23723106718277259716318657 17792330038707944787238993)
  ·
    refine ⟨13344247529030958590429245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17792330038707944787238993 13344247529030958590429245)
    ·
      refine ⟨5004092823386609471410967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13344247529030958590429245 5004092823386609471410967)
      ·
        refine ⟨7506139235079914207116451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5004092823386609471410967 7506139235079914207116451)
        ·
          refine ⟨11259208852619871310674677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506139235079914207116451 11259208852619871310674677)
          ·
            refine ⟨1055550829933112935375751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11259208852619871310674677 1055550829933112935375751)
            ·
              refine ⟨1583326244899669403063627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055550829933112935375751 1583326244899669403063627)
              ·
                refine ⟨2374989367349504104595441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583326244899669403063627 2374989367349504104595441)
                ·
                  refine ⟨1781242025512128078446581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2374989367349504104595441 1781242025512128078446581)
                  ·
                    refine ⟨166991439891762007354367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1781242025512128078446581 166991439891762007354367)
                    ·
                      rfl

theorem cell23_975644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_975644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975644 prefixEnd_975644 := by exact prefixLift 975644
  have htrace : WordTrace (prefixWord ++ tailWord_975644) baseStart_975644 baseEnd_975644 := by
    simpa [prefixWord, tailWord_975644, baseEnd_975644] using wordTrace_append hprefix tailTrace_975644
  have hstable : (prefixWord ++ tailWord_975644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975644).length < 2 ^ (prefixWord ++ tailWord_975644).sum := by decide
  have hdescent : baseEnd_975644 < baseStart_975644 := by decide
  rcases family_descends (prefixWord ++ tailWord_975644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975647 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_975647 : Nat := 118140960795 + 975647 * 2 ^ 59
def prefixEnd_975647 : Nat := 4983230072969 + 3 ^ 40 * 975647 * 2
def baseEnd_975647 : Nat := 500975860117249510325587

theorem tailTrace_975647 : CollatzResearch.WordTrace tailWord_975647 prefixEnd_975647 500975860117249510325587 := by
  unfold tailWord_975647
  simp only [CollatzResearch.WordTrace]
  refine ⟨35584769496405021086837195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23723179664270014057891463 35584769496405021086837195)
  ·
    refine ⟨53377154244607531630255793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35584769496405021086837195 53377154244607531630255793)
    ·
      refine ⟨40032865683455648722691845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53377154244607531630255793 40032865683455648722691845)
      ·
        refine ⟨7506162315647934135504721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40032865683455648722691845 7506162315647934135504721)
        ·
          refine ⟨5629621736735950601628541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7506162315647934135504721 5629621736735950601628541)
          ·
            refine ⟨2111108151275981475610703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5629621736735950601628541 2111108151275981475610703)
            ·
              refine ⟨3166662226913972213416055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111108151275981475610703 3166662226913972213416055)
              ·
                refine ⟨4749993340370958320124083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166662226913972213416055 4749993340370958320124083)
                ·
                  refine ⟨7124990010556437480186125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749993340370958320124083 7124990010556437480186125)
                  ·
                    refine ⟨2671871253958664055069797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7124990010556437480186125 2671871253958664055069797)
                    ·
                      refine ⟨500975860117249510325587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2671871253958664055069797 500975860117249510325587)
                      ·
                        rfl

theorem cell23_975647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_975647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975647 prefixEnd_975647 := by exact prefixLift 975647
  have htrace : WordTrace (prefixWord ++ tailWord_975647) baseStart_975647 baseEnd_975647 := by
    simpa [prefixWord, tailWord_975647, baseEnd_975647] using wordTrace_append hprefix tailTrace_975647
  have hstable : (prefixWord ++ tailWord_975647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975647).length < 2 ^ (prefixWord ++ tailWord_975647).sum := by decide
  have hdescent : baseEnd_975647 < baseStart_975647 := by decide
  rcases family_descends (prefixWord ++ tailWord_975647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975660 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_975660 : Nat := 118140960795 + 975660 * 2 ^ 59
def prefixEnd_975660 : Nat := 4983230072969 + 3 ^ 40 * 975660 * 2
def baseEnd_975660 : Nat := 500982535365757959463027

theorem tailTrace_975660 : CollatzResearch.WordTrace tailWord_975660 prefixEnd_975660 500982535365757959463027 := by
  unfold tailWord_975660
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792621822678962153530217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23723495763571949538040289 17792621822678962153530217)
  ·
    refine ⟨13344466367009221615147663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17792621822678962153530217 13344466367009221615147663)
    ·
      refine ⟨20016699550513832422721495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13344466367009221615147663 20016699550513832422721495)
      ·
        refine ⟨30025049325770748634082243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20016699550513832422721495 30025049325770748634082243)
        ·
          refine ⟨45037573988656122951123365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30025049325770748634082243 45037573988656122951123365)
          ·
            refine ⟨8444545122873023053335631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45037573988656122951123365 8444545122873023053335631)
            ·
              refine ⟨12666817684309534580003447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444545122873023053335631 12666817684309534580003447)
              ·
                refine ⟨19000226526464301870005171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12666817684309534580003447 19000226526464301870005171)
                ·
                  refine ⟨28500339789696452805007757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19000226526464301870005171 28500339789696452805007757)
                  ·
                    refine ⟨10687627421136169801877909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28500339789696452805007757 10687627421136169801877909)
                    ·
                      refine ⟨500982535365757959463027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10687627421136169801877909 500982535365757959463027)
                      ·
                        rfl

theorem cell23_975660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_975660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975660 prefixEnd_975660 := by exact prefixLift 975660
  have htrace : WordTrace (prefixWord ++ tailWord_975660) baseStart_975660 baseEnd_975660 := by
    simpa [prefixWord, tailWord_975660, baseEnd_975660] using wordTrace_append hprefix tailTrace_975660
  have hstable : (prefixWord ++ tailWord_975660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975660).length < 2 ^ (prefixWord ++ tailWord_975660).sum := by decide
  have hdescent : baseEnd_975660 < baseStart_975660 := by decide
  rcases family_descends (prefixWord ++ tailWord_975660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975708 : List Nat := [2, 2, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_975708 : Nat := 118140960795 + 975708 * 2 ^ 59
def prefixEnd_975708 : Nat := 4983230072969 + 3 ^ 40 * 975708 * 2
def baseEnd_975708 : Nat := 167002394145724590554269

theorem tailTrace_975708 : CollatzResearch.WordTrace tailWord_975708 prefixEnd_975708 167002394145724590554269 := by
  unfold tailWord_975708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17793497174592014252403889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23724662899456019003205185 17793497174592014252403889)
  ·
    refine ⟨13345122880944010689302917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17793497174592014252403889 13345122880944010689302917)
    ·
      refine ⟨2502210540177002004244297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13345122880944010689302917 2502210540177002004244297)
      ·
        refine ⟨1876657905132751503183223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2502210540177002004244297 1876657905132751503183223)
        ·
          refine ⟨2814986857699127254774835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876657905132751503183223 2814986857699127254774835)
          ·
            refine ⟨4222480286548690882162253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814986857699127254774835 4222480286548690882162253)
            ·
              refine ⟨1583430107455759080810845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4222480286548690882162253 1583430107455759080810845)
              ·
                refine ⟨593786290295909655304067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583430107455759080810845 593786290295909655304067)
                ·
                  refine ⟨890679435443864482956101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593786290295909655304067 890679435443864482956101)
                  ·
                    refine ⟨167002394145724590554269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890679435443864482956101 167002394145724590554269)
                    ·
                      rfl

theorem cell23_975708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_975708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975708 prefixEnd_975708 := by exact prefixLift 975708
  have htrace : WordTrace (prefixWord ++ tailWord_975708) baseStart_975708 baseEnd_975708 := by
    simpa [prefixWord, tailWord_975708, baseEnd_975708] using wordTrace_append hprefix tailTrace_975708
  have hstable : (prefixWord ++ tailWord_975708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975708).length < 2 ^ (prefixWord ++ tailWord_975708).sum := by decide
  have hdescent : baseEnd_975708 < baseStart_975708 := by decide
  rcases family_descends (prefixWord ++ tailWord_975708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975731 : List Nat := [1, 1, 1, 2, 2, 1, 4, 6, 1, 1, 3]
def baseStart_975731 : Nat := 118140960795 + 975731 * 2 ^ 59
def prefixEnd_975731 : Nat := 4983230072969 + 3 ^ 40 * 975731 * 2
def baseEnd_975731 : Nat := 501018992492227181675201

theorem tailTrace_975731 : CollatzResearch.WordTrace tailWord_975731 prefixEnd_975731 501018992492227181675201 := by
  unfold tailWord_975731
  simp only [CollatzResearch.WordTrace]
  refine ⟨35587833228100703432895047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23725222152067135621930031 35587833228100703432895047)
  ·
    refine ⟨53381749842151055149342571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35587833228100703432895047 53381749842151055149342571)
    ·
      refine ⟨80072624763226582724013857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53381749842151055149342571 80072624763226582724013857)
      ·
        refine ⟨60054468572419937043010393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80072624763226582724013857 60054468572419937043010393)
        ·
          refine ⟨45040851429314952782257795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60054468572419937043010393 45040851429314952782257795)
          ·
            refine ⟨67561277143972429173386693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45040851429314952782257795 67561277143972429173386693)
            ·
              refine ⟨12667739464494830470010005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67561277143972429173386693 12667739464494830470010005)
              ·
                refine ⟨593800287398195178281719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12667739464494830470010005 593800287398195178281719)
                ·
                  refine ⟨890700431097292767422579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593800287398195178281719 890700431097292767422579)
                  ·
                    refine ⟨1336050646645939151133869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 890700431097292767422579 1336050646645939151133869)
                    ·
                      refine ⟨501018992492227181675201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1336050646645939151133869 501018992492227181675201)
                      ·
                        rfl

theorem cell23_975731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 1, 3].length) (baseStart_975731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975731 prefixEnd_975731 := by exact prefixLift 975731
  have htrace : WordTrace (prefixWord ++ tailWord_975731) baseStart_975731 baseEnd_975731 := by
    simpa [prefixWord, tailWord_975731, baseEnd_975731] using wordTrace_append hprefix tailTrace_975731
  have hstable : (prefixWord ++ tailWord_975731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975731).length < 2 ^ (prefixWord ++ tailWord_975731).sum := by decide
  have hdescent : baseEnd_975731 < baseStart_975731 := by decide
  rcases family_descends (prefixWord ++ tailWord_975731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975747 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 1, 6]
def baseStart_975747 : Nat := 118140960795 + 975747 * 2 ^ 59
def prefixEnd_975747 : Nat := 4983230072969 + 3 ^ 40 * 975747 * 2
def baseEnd_975747 : Nat := 167009069394233039691709

theorem tailTrace_975747 : CollatzResearch.WordTrace tailWord_975747 prefixEnd_975747 167009069394233039691709 := by
  unfold tailWord_975747
  simp only [CollatzResearch.WordTrace]
  refine ⟨35588416796042738165477495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23725611197361825443651663 35588416796042738165477495)
  ·
    refine ⟨53382625194064107248216243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35588416796042738165477495 53382625194064107248216243)
    ·
      refine ⟨80073937791096160872324365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53382625194064107248216243 80073937791096160872324365)
      ·
        refine ⟨30027726671661060327121637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80073937791096160872324365 30027726671661060327121637)
        ·
          refine ⟨5630198750936448811335307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30027726671661060327121637 5630198750936448811335307)
          ·
            refine ⟨8445298126404673217002961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630198750936448811335307 8445298126404673217002961)
            ·
              refine ⟨6333973594803504912752221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8445298126404673217002961 6333973594803504912752221)
              ·
                refine ⟨2375240098051314342282083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6333973594803504912752221 2375240098051314342282083)
                ·
                  refine ⟨3562860147076971513423125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375240098051314342282083 3562860147076971513423125)
                  ·
                    refine ⟨167009069394233039691709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3562860147076971513423125 167009069394233039691709)
                    ·
                      rfl

theorem cell23_975747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 6].length) (baseStart_975747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975747 prefixEnd_975747 := by exact prefixLift 975747
  have htrace : WordTrace (prefixWord ++ tailWord_975747) baseStart_975747 baseEnd_975747 := by
    simpa [prefixWord, tailWord_975747, baseEnd_975747] using wordTrace_append hprefix tailTrace_975747
  have hstable : (prefixWord ++ tailWord_975747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975747).length < 2 ^ (prefixWord ++ tailWord_975747).sum := by decide
  have hdescent : baseEnd_975747 < baseStart_975747 := by decide
  rcases family_descends (prefixWord ++ tailWord_975747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975751 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 1, 5]
def baseStart_975751 : Nat := 118140960795 + 975751 * 2 ^ 59
def prefixEnd_975751 : Nat := 4983230072969 + 3 ^ 40 * 975751 * 2
def baseEnd_975751 : Nat := 167009754035105701141703

theorem tailTrace_975751 : CollatzResearch.WordTrace tailWord_975751 prefixEnd_975751 167009754035105701141703 := by
  unfold tailWord_975751
  simp only [CollatzResearch.WordTrace]
  refine ⟨35588562688028246848623107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23725708458685497899082071 35588562688028246848623107)
  ·
    refine ⟨53382844032042370272934661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35588562688028246848623107 53382844032042370272934661)
    ·
      refine ⟨10009283256007944426175249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53382844032042370272934661 10009283256007944426175249)
      ·
        refine ⟨7506962442005958319631437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10009283256007944426175249 7506962442005958319631437)
        ·
          refine ⟨2815110915752234369861789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7506962442005958319631437 2815110915752234369861789)
          ·
            refine ⟨1055666593407087888698171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2815110915752234369861789 1055666593407087888698171)
            ·
              refine ⟨1583499890110631833047257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055666593407087888698171 1583499890110631833047257)
              ·
                refine ⟨1187624917582973874785443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583499890110631833047257 1187624917582973874785443)
                ·
                  refine ⟨1781437376374460812178165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187624917582973874785443 1781437376374460812178165)
                  ·
                    refine ⟨167009754035105701141703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1781437376374460812178165 167009754035105701141703)
                    ·
                      rfl

theorem cell23_975751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_975751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975751 prefixEnd_975751 := by exact prefixLift 975751
  have htrace : WordTrace (prefixWord ++ tailWord_975751) baseStart_975751 baseEnd_975751 := by
    simpa [prefixWord, tailWord_975751, baseEnd_975751] using wordTrace_append hprefix tailTrace_975751
  have hstable : (prefixWord ++ tailWord_975751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975751).length < 2 ^ (prefixWord ++ tailWord_975751).sum := by decide
  have hdescent : baseEnd_975751 < baseStart_975751 := by decide
  rcases family_descends (prefixWord ++ tailWord_975751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975764 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_975764 : Nat := 118140960795 + 975764 * 2 ^ 59
def prefixEnd_975764 : Nat := 4983230072969 + 3 ^ 40 * 975764 * 2
def baseEnd_975764 : Nat := 167011979117941850854183

theorem tailTrace_975764 : CollatzResearch.WordTrace tailWord_975764 prefixEnd_975764 167011979117941850854183 := by
  unfold tailWord_975764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17794518418490575034423173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23726024557987433379230897 17794518418490575034423173)
  ·
    refine ⟨3336472203466982818954345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17794518418490575034423173 3336472203466982818954345)
    ·
      refine ⟨2502354152600237114215759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3336472203466982818954345 2502354152600237114215759)
      ·
        refine ⟨3753531228900355671323639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502354152600237114215759 3753531228900355671323639)
        ·
          refine ⟨5630296843350533506985459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753531228900355671323639 5630296843350533506985459)
          ·
            refine ⟨8445445265025800260478189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630296843350533506985459 8445445265025800260478189)
            ·
              refine ⟨3167041974384675097679321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8445445265025800260478189 3167041974384675097679321)
              ·
                refine ⟨2375281480788506323259491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167041974384675097679321 2375281480788506323259491)
                ·
                  refine ⟨3562922221182759484889237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375281480788506323259491 3562922221182759484889237)
                  ·
                    refine ⟨167011979117941850854183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3562922221182759484889237 167011979117941850854183)
                    ·
                      rfl

theorem cell23_975764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_975764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975764 prefixEnd_975764 := by exact prefixLift 975764
  have htrace : WordTrace (prefixWord ++ tailWord_975764) baseStart_975764 baseEnd_975764 := by
    simpa [prefixWord, tailWord_975764, baseEnd_975764] using wordTrace_append hprefix tailTrace_975764
  have hstable : (prefixWord ++ tailWord_975764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975764).length < 2 ^ (prefixWord ++ tailWord_975764).sum := by decide
  have hdescent : baseEnd_975764 < baseStart_975764 := by decide
  rcases family_descends (prefixWord ++ tailWord_975764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975777 : List Nat := [1, 2, 3, 4, 1, 12]
def baseStart_975777 : Nat := 118140960795 + 975777 * 2 ^ 59
def prefixEnd_975777 : Nat := 4983230072969 + 3 ^ 40 * 975777 * 2
def baseEnd_975777 : Nat := 2061903755565160500823

theorem tailTrace_975777 : CollatzResearch.WordTrace tailWord_975777 prefixEnd_975777 2061903755565160500823 := by
  unfold tailWord_975777
  simp only [CollatzResearch.WordTrace]
  refine ⟨35589510985934053289069585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23726340657289368859379723 35589510985934053289069585)
  ·
    refine ⟨26692133239450539966802189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35589510985934053289069585 26692133239450539966802189)
    ·
      refine ⟨10009549964793952487550821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26692133239450539966802189 10009549964793952487550821)
      ·
        refine ⟨1876790618398866091415779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10009549964793952487550821 1876790618398866091415779)
        ·
          refine ⟨2815185927598299137123669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876790618398866091415779 2815185927598299137123669)
          ·
            refine ⟨2061903755565160500823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2815185927598299137123669 2061903755565160500823)
            ·
              rfl

theorem cell23_975777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 12].length) (baseStart_975777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975777 prefixEnd_975777 := by exact prefixLift 975777
  have htrace : WordTrace (prefixWord ++ tailWord_975777) baseStart_975777 baseEnd_975777 := by
    simpa [prefixWord, tailWord_975777, baseEnd_975777] using wordTrace_append hprefix tailTrace_975777
  have hstable : (prefixWord ++ tailWord_975777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975777).length < 2 ^ (prefixWord ++ tailWord_975777).sum := by decide
  have hdescent : baseEnd_975777 < baseStart_975777 := by decide
  rcases family_descends (prefixWord ++ tailWord_975777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975788 : List Nat := [2, 2, 1, 1, 1, 1, 2, 8, 1, 2, 2]
def baseStart_975788 : Nat := 118140960795 + 975788 * 2 ^ 59
def prefixEnd_975788 : Nat := 4983230072969 + 3 ^ 40 * 975788 * 2
def baseEnd_975788 : Nat := 501048260889533458662439

theorem tailTrace_975788 : CollatzResearch.WordTrace tailWord_975788 prefixEnd_975788 501048260889533458662439 := by
  unfold tailWord_975788
  simp only [CollatzResearch.WordTrace]
  refine ⟨17794956094447101083860009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23726608125929468111813345 17794956094447101083860009)
  ·
    refine ⟨13346217070835325812895007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17794956094447101083860009 13346217070835325812895007)
    ·
      refine ⟨20019325606252988719342511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13346217070835325812895007 20019325606252988719342511)
      ·
        refine ⟨30028988409379483079013767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20019325606252988719342511 30028988409379483079013767)
        ·
          refine ⟨45043482614069224618520651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30028988409379483079013767 45043482614069224618520651)
          ·
            refine ⟨67565223921103836927780977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45043482614069224618520651 67565223921103836927780977)
            ·
              refine ⟨50673917940827877695835733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67565223921103836927780977 50673917940827877695835733)
              ·
                refine ⟨593834975869076691748075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 50673917940827877695835733 593834975869076691748075)
                ·
                  refine ⟨890752463803615037622113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593834975869076691748075 890752463803615037622113)
                  ·
                    refine ⟨668064347852711278216585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 890752463803615037622113 668064347852711278216585)
                    ·
                      refine ⟨501048260889533458662439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668064347852711278216585 501048260889533458662439)
                      ·
                        rfl

theorem cell23_975788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_975788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975788 prefixEnd_975788 := by exact prefixLift 975788
  have htrace : WordTrace (prefixWord ++ tailWord_975788) baseStart_975788 baseEnd_975788 := by
    simpa [prefixWord, tailWord_975788, baseEnd_975788] using wordTrace_append hprefix tailTrace_975788
  have hstable : (prefixWord ++ tailWord_975788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975788).length < 2 ^ (prefixWord ++ tailWord_975788).sum := by decide
  have hdescent : baseEnd_975788 < baseStart_975788 := by decide
  rcases family_descends (prefixWord ++ tailWord_975788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975978 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_975978 : Nat := 118140960795 + 975978 * 2 ^ 59
def prefixEnd_975978 : Nat := 4983230072969 + 3 ^ 40 * 975978 * 2
def baseEnd_975978 : Nat := 167048607404629238428855

theorem tailTrace_975978 : CollatzResearch.WordTrace tailWord_975978 prefixEnd_975978 167048607404629238428855 := by
  unfold tailWord_975978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899210514551466154284147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23731228038803909744757725 8899210514551466154284147)
  ·
    refine ⟨13348815771827199231426221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8899210514551466154284147 13348815771827199231426221)
    ·
      refine ⟨5005805914435199711784833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13348815771827199231426221 5005805914435199711784833)
      ·
        refine ⟨3754354435826399783838625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5005805914435199711784833 3754354435826399783838625)
        ·
          refine ⟨2815765826869799837878969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3754354435826399783838625 2815765826869799837878969)
          ·
            refine ⟨2111824370152349878409227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2815765826869799837878969 2111824370152349878409227)
            ·
              refine ⟨3167736555228524817613841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111824370152349878409227 3167736555228524817613841)
              ·
                refine ⟨2375802416421393613210381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167736555228524817613841 2375802416421393613210381)
                ·
                  refine ⟨890925906158022604953893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2375802416421393613210381 890925906158022604953893)
                  ·
                    refine ⟨167048607404629238428855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890925906158022604953893 167048607404629238428855)
                    ·
                      rfl

theorem cell23_975978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_975978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_975978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_975978 prefixEnd_975978 := by exact prefixLift 975978
  have htrace : WordTrace (prefixWord ++ tailWord_975978) baseStart_975978 baseEnd_975978 := by
    simpa [prefixWord, tailWord_975978, baseEnd_975978] using wordTrace_append hprefix tailTrace_975978
  have hstable : (prefixWord ++ tailWord_975978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975978).length < 2 ^ (prefixWord ++ tailWord_975978).sum := by decide
  have hdescent : baseEnd_975978 < baseStart_975978 := by decide
  rcases family_descends (prefixWord ++ tailWord_975978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976028 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_976028 : Nat := 118140960795 + 976028 * 2 ^ 59
def prefixEnd_976028 : Nat := 4983230072969 + 3 ^ 40 * 976028 * 2
def baseEnd_976028 : Nat := 501171496246612519661335

theorem tailTrace_976028 : CollatzResearch.WordTrace tailWord_976028 prefixEnd_976028 501171496246612519661335 := by
  unfold tailWord_976028
  simp only [CollatzResearch.WordTrace]
  refine ⟨17799332854012361578228369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23732443805349815437637825 17799332854012361578228369)
  ·
    refine ⟨13349499640509271183671277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17799332854012361578228369 13349499640509271183671277)
    ·
      refine ⟨5006062365190976693876729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13349499640509271183671277 5006062365190976693876729)
      ·
        refine ⟨3754546773893232520407547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5006062365190976693876729 3754546773893232520407547)
        ·
          refine ⟨5631820160839848780611321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754546773893232520407547 5631820160839848780611321)
          ·
            refine ⟨4223865120629886585458491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5631820160839848780611321 4223865120629886585458491)
            ·
              refine ⟨6335797680944829878187737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223865120629886585458491 6335797680944829878187737)
              ·
                refine ⟨4751848260708622408640803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6335797680944829878187737 4751848260708622408640803)
                ·
                  refine ⟨7127772391062933612961205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751848260708622408640803 7127772391062933612961205)
                  ·
                    refine ⟨668228661662150026215113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7127772391062933612961205 668228661662150026215113)
                    ·
                      refine ⟨501171496246612519661335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668228661662150026215113 501171496246612519661335)
                      ·
                        rfl

theorem cell23_976028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_976028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976028 prefixEnd_976028 := by exact prefixLift 976028
  have htrace : WordTrace (prefixWord ++ tailWord_976028) baseStart_976028 baseEnd_976028 := by
    simpa [prefixWord, tailWord_976028, baseEnd_976028] using wordTrace_append hprefix tailTrace_976028
  have hstable : (prefixWord ++ tailWord_976028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976028).length < 2 ^ (prefixWord ++ tailWord_976028).sum := by decide
  have hdescent : baseEnd_976028 < baseStart_976028 := by decide
  rcases family_descends (prefixWord ++ tailWord_976028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976051 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 4, 4]
def baseStart_976051 : Nat := 118140960795 + 976051 * 2 ^ 59
def prefixEnd_976051 : Nat := 4983230072969 + 3 ^ 40 * 976051 * 2
def baseEnd_976051 : Nat := 167061102100555309891243

theorem tailTrace_976051 : CollatzResearch.WordTrace tailWord_976051 prefixEnd_976051 167061102100555309891243 := by
  unfold tailWord_976051
  simp only [CollatzResearch.WordTrace]
  refine ⟨35599504586941398084544007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23733003057960932056362671 35599504586941398084544007)
  ·
    refine ⟨53399256880412097126816011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35599504586941398084544007 53399256880412097126816011)
    ·
      refine ⟨80098885320618145690224017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53399256880412097126816011 80098885320618145690224017)
      ·
        refine ⟨60074163990463609267668013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80098885320618145690224017 60074163990463609267668013)
        ·
          refine ⟨22527811496423853475375505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60074163990463609267668013 22527811496423853475375505)
          ·
            refine ⟨16895858622317890106531629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22527811496423853475375505 16895858622317890106531629)
            ·
              refine ⟨6335946983369208789949361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16895858622317890106531629 6335946983369208789949361)
              ·
                refine ⟨4751960237526906592462021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6335946983369208789949361 4751960237526906592462021)
                ·
                  refine ⟨890992544536294986086629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4751960237526906592462021 890992544536294986086629)
                  ·
                    refine ⟨167061102100555309891243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890992544536294986086629 167061102100555309891243)
                    ·
                      rfl

theorem cell23_976051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 4].length) (baseStart_976051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976051 prefixEnd_976051 := by exact prefixLift 976051
  have htrace : WordTrace (prefixWord ++ tailWord_976051) baseStart_976051 baseEnd_976051 := by
    simpa [prefixWord, tailWord_976051, baseEnd_976051] using wordTrace_append hprefix tailTrace_976051
  have hstable : (prefixWord ++ tailWord_976051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976051).length < 2 ^ (prefixWord ++ tailWord_976051).sum := by decide
  have hdescent : baseEnd_976051 < baseStart_976051 := by decide
  rcases family_descends (prefixWord ++ tailWord_976051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976061 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_976061 : Nat := 118140960795 + 976061 * 2 ^ 59
def prefixEnd_976061 : Nat := 4983230072969 + 3 ^ 40 * 976061 * 2
def baseEnd_976061 : Nat := 501188441108210890548683

theorem tailTrace_976061 : CollatzResearch.WordTrace tailWord_976061 prefixEnd_976061 501188441108210890548683 := by
  unfold tailWord_976061
  simp only [CollatzResearch.WordTrace]
  refine ⟨35599869316905169792408037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23733246211270113194938691 35599869316905169792408037)
  ·
    refine ⟨6674975496919719336076507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35599869316905169792408037 6674975496919719336076507)
    ·
      refine ⟨10012463245379579004114761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6674975496919719336076507 10012463245379579004114761)
      ·
        refine ⟨7509347434034684253086071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10012463245379579004114761 7509347434034684253086071)
        ·
          refine ⟨11264021151052026379629107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509347434034684253086071 11264021151052026379629107)
          ·
            refine ⟨16896031726578039569443661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264021151052026379629107 16896031726578039569443661)
            ·
              refine ⟨6336011897466764838541373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16896031726578039569443661 6336011897466764838541373)
              ·
                refine ⟨2376004461550036814453015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6336011897466764838541373 2376004461550036814453015)
                ·
                  refine ⟨3564006692325055221679523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376004461550036814453015 3564006692325055221679523)
                  ·
                    refine ⟨5346010038487582832519285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3564006692325055221679523 5346010038487582832519285)
                    ·
                      refine ⟨501188441108210890548683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5346010038487582832519285 501188441108210890548683)
                      ·
                        rfl

theorem cell23_976061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_976061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976061 prefixEnd_976061 := by exact prefixLift 976061
  have htrace : WordTrace (prefixWord ++ tailWord_976061) baseStart_976061 baseEnd_976061 := by
    simpa [prefixWord, tailWord_976061, baseEnd_976061] using wordTrace_append hprefix tailTrace_976061
  have hstable : (prefixWord ++ tailWord_976061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976061).length < 2 ^ (prefixWord ++ tailWord_976061).sum := by decide
  have hdescent : baseEnd_976061 < baseStart_976061 := by decide
  rcases family_descends (prefixWord ++ tailWord_976061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976085 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_976085 : Nat := 118140960795 + 976085 * 2 ^ 59
def prefixEnd_976085 : Nat := 4983230072969 + 3 ^ 40 * 976085 * 2
def baseEnd_976085 : Nat := 167066921547972932216191

theorem tailTrace_976085 : CollatzResearch.WordTrace tailWord_976085 prefixEnd_976085 167066921547972932216191 := by
  unfold tailWord_976085
  simp only [CollatzResearch.WordTrace]
  refine ⟨35600744668818221891281709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23733829779212147927521139 35600744668818221891281709)
  ·
    refine ⟨13350279250806833209230641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35600744668818221891281709 13350279250806833209230641)
    ·
      refine ⟨10012709438105124906922981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13350279250806833209230641 10012709438105124906922981)
      ·
        refine ⟨1877383019644710920048059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10012709438105124906922981 1877383019644710920048059)
        ·
          refine ⟨2816074529467066380072089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877383019644710920048059 2816074529467066380072089)
          ·
            refine ⟨2112055897100299785054067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2816074529467066380072089 2112055897100299785054067)
            ·
              refine ⟨3168083845650449677581101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112055897100299785054067 3168083845650449677581101)
              ·
                refine ⟨1188031442118918629092913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3168083845650449677581101 1188031442118918629092913)
                ·
                  refine ⟨891023581589188971819685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188031442118918629092913 891023581589188971819685)
                  ·
                    refine ⟨167066921547972932216191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 891023581589188971819685 167066921547972932216191)
                    ·
                      rfl

theorem cell23_976085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_976085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976085 prefixEnd_976085 := by exact prefixLift 976085
  have htrace : WordTrace (prefixWord ++ tailWord_976085) baseStart_976085 baseEnd_976085 := by
    simpa [prefixWord, tailWord_976085, baseEnd_976085] using wordTrace_append hprefix tailTrace_976085
  have hstable : (prefixWord ++ tailWord_976085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976085).length < 2 ^ (prefixWord ++ tailWord_976085).sum := by decide
  have hdescent : baseEnd_976085 < baseStart_976085 := by decide
  rcases family_descends (prefixWord ++ tailWord_976085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976108 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_976108 : Nat := 118140960795 + 976108 * 2 ^ 59
def prefixEnd_976108 : Nat := 4983230072969 + 3 ^ 40 * 976108 * 2
def baseEnd_976108 : Nat := 501212574698972206660967

theorem tailTrace_976108 : CollatzResearch.WordTrace tailWord_976108 prefixEnd_976108 501212574698972206660967 := by
  unfold tailWord_976108
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800791773867448409684489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23734389031823264546245985 17800791773867448409684489)
  ·
    refine ⟨13350593830400586307263367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17800791773867448409684489 13350593830400586307263367)
    ·
      refine ⟨20025890745600879460895051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350593830400586307263367 20025890745600879460895051)
      ·
        refine ⟨30038836118401319191342577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20025890745600879460895051 30038836118401319191342577)
        ·
          refine ⟨22529127088800989393506933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30038836118401319191342577 22529127088800989393506933)
          ·
            refine ⟨2112105664575092755641275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22529127088800989393506933 2112105664575092755641275)
            ·
              refine ⟨3168158496862639133461913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112105664575092755641275 3168158496862639133461913)
              ·
                refine ⟨2376118872646979350096435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168158496862639133461913 2376118872646979350096435)
                ·
                  refine ⟨3564178308970469025144653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376118872646979350096435 3564178308970469025144653)
                  ·
                    refine ⟨1336566865863925884429245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3564178308970469025144653 1336566865863925884429245)
                    ·
                      refine ⟨501212574698972206660967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1336566865863925884429245 501212574698972206660967)
                      ·
                        rfl

theorem cell23_976108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_976108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976108 prefixEnd_976108 := by exact prefixLift 976108
  have htrace : WordTrace (prefixWord ++ tailWord_976108) baseStart_976108 baseEnd_976108 := by
    simpa [prefixWord, tailWord_976108, baseEnd_976108] using wordTrace_append hprefix tailTrace_976108
  have hstable : (prefixWord ++ tailWord_976108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976108).length < 2 ^ (prefixWord ++ tailWord_976108).sum := by decide
  have hdescent : baseEnd_976108 < baseStart_976108 := by decide
  rcases family_descends (prefixWord ++ tailWord_976108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976126 : List Nat := [4, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_976126 : Nat := 118140960795 + 976126 * 2 ^ 59
def prefixEnd_976126 : Nat := 4983230072969 + 3 ^ 40 * 976126 * 2
def baseEnd_976126 : Nat := 501221817350753136235885

theorem tailTrace_976126 : CollatzResearch.WordTrace tailWord_976126 prefixEnd_976126 501221817350753136235885 := by
  unfold tailWord_976126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450280007708710736690529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23734826707779790595682821 4450280007708710736690529)
  ·
    refine ⟨3337710005781533052517897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4450280007708710736690529 3337710005781533052517897)
    ·
      refine ⟨2503282504336149789388423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3337710005781533052517897 2503282504336149789388423)
      ·
        refine ⟨3754923756504224684082635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503282504336149789388423 3754923756504224684082635)
        ·
          refine ⟨5632385634756337026123953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754923756504224684082635 5632385634756337026123953)
          ·
            refine ⟨4224289226067252769592965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5632385634756337026123953 4224289226067252769592965)
            ·
              refine ⟨792054229887609894298681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4224289226067252769592965 792054229887609894298681)
              ·
                refine ⟨594040672415707420724011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792054229887609894298681 594040672415707420724011)
                ·
                  refine ⟨891061008623561131086017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594040672415707420724011 891061008623561131086017)
                  ·
                    refine ⟨668295756467670848314513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 891061008623561131086017 668295756467670848314513)
                    ·
                      refine ⟨501221817350753136235885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668295756467670848314513 501221817350753136235885)
                      ·
                        rfl

theorem cell23_976126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_976126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976126 prefixEnd_976126 := by exact prefixLift 976126
  have htrace : WordTrace (prefixWord ++ tailWord_976126) baseStart_976126 baseEnd_976126 := by
    simpa [prefixWord, tailWord_976126, baseEnd_976126] using wordTrace_append hprefix tailTrace_976126
  have hstable : (prefixWord ++ tailWord_976126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976126).length < 2 ^ (prefixWord ++ tailWord_976126).sum := by decide
  have hdescent : baseEnd_976126 < baseStart_976126 := by decide
  rcases family_descends (prefixWord ++ tailWord_976126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
