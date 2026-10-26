import V185TrunkScan23Chunk0108

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_644510 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_644510 : Nat := 118140960795 + 644510 * 2 ^ 59
def prefixEnd_644510 : Nat := 4983230072969 + 3 ^ 40 * 644510 * 2
def baseEnd_644510 : Nat := 330943416629378585360959

theorem tailTrace_644510 : CollatzResearch.WordTrace tailWord_644510 prefixEnd_644510 330943416629378585360959 := by
  unfold tailWord_644510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938401361882227298713373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15671473930038545593137989 2938401361882227298713373)
  ·
    refine ⟨1101900510705835237017515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2938401361882227298713373 1101900510705835237017515)
    ·
      refine ⟨1652850766058752855526273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101900510705835237017515 1652850766058752855526273)
      ·
        refine ⟨1239638074544064641644705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652850766058752855526273 1239638074544064641644705)
        ·
          refine ⟨929728555908048481233529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239638074544064641644705 929728555908048481233529)
          ·
            refine ⟨697296416931036360925147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929728555908048481233529 697296416931036360925147)
            ·
              refine ⟨1045944625396554541387721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697296416931036360925147 1045944625396554541387721)
              ·
                refine ⟨784458469047415906040791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045944625396554541387721 784458469047415906040791)
                ·
                  refine ⟨1176687703571123859061187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784458469047415906040791 1176687703571123859061187)
                  ·
                    refine ⟨1765031555356685788591781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1176687703571123859061187 1765031555356685788591781)
                    ·
                      refine ⟨330943416629378585360959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1765031555356685788591781 330943416629378585360959)
                      ·
                        rfl

theorem cell23_644510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_644510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644510 prefixEnd_644510 := by exact prefixLift 644510
  have htrace : WordTrace (prefixWord ++ tailWord_644510) baseStart_644510 baseEnd_644510 := by
    simpa [prefixWord, tailWord_644510, baseEnd_644510] using wordTrace_append hprefix tailTrace_644510
  have hstable : (prefixWord ++ tailWord_644510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644510).length < 2 ^ (prefixWord ++ tailWord_644510).sum := by decide
  have hdescent : baseEnd_644510 < baseStart_644510 := by decide
  rcases family_descends (prefixWord ++ tailWord_644510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644536 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 1, 3, 2]
def baseStart_644536 : Nat := 118140960795 + 644536 * 2 ^ 59
def prefixEnd_644536 : Nat := 4983230072969 + 3 ^ 40 * 644536 * 2
def baseEnd_644536 : Nat := 330956767126395483635839

theorem tailTrace_644536 : CollatzResearch.WordTrace tailWord_644536 prefixEnd_644536 330956767126395483635839 := by
  unfold tailWord_644536
  simp only [CollatzResearch.WordTrace]
  refine ⟨11754079596481812415076731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15672106128642416553435641 11754079596481812415076731)
  ·
    refine ⟨17631119394722718622615097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11754079596481812415076731 17631119394722718622615097)
    ·
      refine ⟨13223339546042038966961323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17631119394722718622615097 13223339546042038966961323)
      ·
        refine ⟨19835009319063058450441985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13223339546042038966961323 19835009319063058450441985)
        ·
          refine ⟨14876256989297293837831489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19835009319063058450441985 14876256989297293837831489)
          ·
            refine ⟨11157192741972970378373617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14876256989297293837831489 11157192741972970378373617)
            ·
              refine ⟨8367894556479727783780213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11157192741972970378373617 8367894556479727783780213)
              ·
                refine ⟨784490114669974479729395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8367894556479727783780213 784490114669974479729395)
                ·
                  refine ⟨1176735172004961719594093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784490114669974479729395 1176735172004961719594093)
                  ·
                    refine ⟨441275689501860644847785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176735172004961719594093 441275689501860644847785)
                    ·
                      refine ⟨330956767126395483635839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441275689501860644847785 330956767126395483635839)
                      ·
                        rfl

theorem cell23_644536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_644536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644536 prefixEnd_644536 := by exact prefixLift 644536
  have htrace : WordTrace (prefixWord ++ tailWord_644536) baseStart_644536 baseEnd_644536 := by
    simpa [prefixWord, tailWord_644536, baseEnd_644536] using wordTrace_append hprefix tailTrace_644536
  have hstable : (prefixWord ++ tailWord_644536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644536).length < 2 ^ (prefixWord ++ tailWord_644536).sum := by decide
  have hdescent : baseEnd_644536 < baseStart_644536 := by decide
  rcases family_descends (prefixWord ++ tailWord_644536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644600 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 2, 2, 2]
def baseStart_644600 : Nat := 118140960795 + 644600 * 2 ^ 59
def prefixEnd_644600 : Nat := 4983230072969 + 3 ^ 40 * 644600 * 2
def baseEnd_644600 : Nat := 330989629888283233235545

theorem tailTrace_644600 : CollatzResearch.WordTrace tailWord_644600 prefixEnd_644600 330989629888283233235545 := by
  unfold tailWord_644600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11755246732365881880241627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15673662309821175840322169 11755246732365881880241627)
  ·
    refine ⟨17632870098548822820362441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11755246732365881880241627 17632870098548822820362441)
    ·
      refine ⟨13224652573911617115271831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17632870098548822820362441 13224652573911617115271831)
      ·
        refine ⟨19836978860867425672907747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13224652573911617115271831 19836978860867425672907747)
        ·
          refine ⟨29755468291301138509361621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19836978860867425672907747 29755468291301138509361621)
          ·
            refine ⟨697393788077370433813163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29755468291301138509361621 697393788077370433813163)
            ·
              refine ⟨1046090682116055650719745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697393788077370433813163 1046090682116055650719745)
              ·
                refine ⟨784568011587041738039809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046090682116055650719745 784568011587041738039809)
                ·
                  refine ⟨588426008690281303529857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 784568011587041738039809 588426008690281303529857)
                  ·
                    refine ⟨441319506517710977647393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 588426008690281303529857 441319506517710977647393)
                    ·
                      refine ⟨330989629888283233235545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441319506517710977647393 330989629888283233235545)
                      ·
                        rfl

theorem cell23_644600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_644600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644600 prefixEnd_644600 := by exact prefixLift 644600
  have htrace : WordTrace (prefixWord ++ tailWord_644600) baseStart_644600 baseEnd_644600 := by
    simpa [prefixWord, tailWord_644600, baseEnd_644600] using wordTrace_append hprefix tailTrace_644600
  have hstable : (prefixWord ++ tailWord_644600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644600).length < 2 ^ (prefixWord ++ tailWord_644600).sum := by decide
  have hdescent : baseEnd_644600 < baseStart_644600 := by decide
  rcases family_descends (prefixWord ++ tailWord_644600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644639 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_644639 : Nat := 118140960795 + 644639 * 2 ^ 59
def prefixEnd_644639 : Nat := 4983230072969 + 3 ^ 40 * 644639 * 2
def baseEnd_644639 : Nat := 331009655633808580647865

theorem tailTrace_644639 : CollatzResearch.WordTrace tailWord_644639 prefixEnd_644639 331009655633808580647865 := by
  unfold tailWord_644639
  simp only [CollatzResearch.WordTrace]
  refine ⟨23511915911590473421152971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15674610607726982280768647 23511915911590473421152971)
  ·
    refine ⟨35267873867385710131729457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23511915911590473421152971 35267873867385710131729457)
    ·
      refine ⟨26450905400539282598797093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35267873867385710131729457 26450905400539282598797093)
      ·
        refine ⟨4959544762601115487274455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26450905400539282598797093 4959544762601115487274455)
        ·
          refine ⟨7439317143901673230911683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4959544762601115487274455 7439317143901673230911683)
          ·
            refine ⟨11158975715852509846367525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7439317143901673230911683 11158975715852509846367525)
            ·
              refine ⟨2092307946722345596193911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11158975715852509846367525 2092307946722345596193911)
              ·
                refine ⟨3138461920083518394290867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092307946722345596193911 3138461920083518394290867)
                ·
                  refine ⟨4707692880125277591436301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3138461920083518394290867 4707692880125277591436301)
                  ·
                    refine ⟨1765384830046979096788613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4707692880125277591436301 1765384830046979096788613)
                    ·
                      refine ⟨331009655633808580647865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1765384830046979096788613 331009655633808580647865)
                      ·
                        rfl

theorem cell23_644639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_644639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644639 prefixEnd_644639 := by exact prefixLift 644639
  have htrace : WordTrace (prefixWord ++ tailWord_644639) baseStart_644639 baseEnd_644639 := by
    simpa [prefixWord, tailWord_644639, baseEnd_644639] using wordTrace_append hprefix tailTrace_644639
  have hstable : (prefixWord ++ tailWord_644639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644639).length < 2 ^ (prefixWord ++ tailWord_644639).sum := by decide
  have hdescent : baseEnd_644639 < baseStart_644639 := by decide
  rcases family_descends (prefixWord ++ tailWord_644639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644716 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 3, 5, 2]
def baseStart_644716 : Nat := 118140960795 + 644716 * 2 ^ 59
def prefixEnd_644716 : Nat := 4983230072969 + 3 ^ 40 * 644716 * 2
def baseEnd_644716 : Nat := 331049193644204779385011

theorem tailTrace_644716 : CollatzResearch.WordTrace tailWord_644716 prefixEnd_644716 331049193644204779385011 := by
  unfold tailWord_644716
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757362166155757785853001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15676482888207677047804001 11757362166155757785853001)
  ·
    refine ⟨8818021624616818339389751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11757362166155757785853001 8818021624616818339389751)
    ·
      refine ⟨13227032436925227509084627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8818021624616818339389751 13227032436925227509084627)
      ·
        refine ⟨19840548655387841263626941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13227032436925227509084627 19840548655387841263626941)
        ·
          refine ⟨7440205745770440473860103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19840548655387841263626941 7440205745770440473860103)
          ·
            refine ⟨11160308618655660710790155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7440205745770440473860103 11160308618655660710790155)
            ·
              refine ⟨16740462927983491066185233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11160308618655660710790155 16740462927983491066185233)
              ·
                refine ⟨12555347195987618299638925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16740462927983491066185233 12555347195987618299638925)
                ·
                  refine ⟨4708255198495356862364597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12555347195987618299638925 4708255198495356862364597)
                  ·
                    refine ⟨441398924858939705846681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4708255198495356862364597 441398924858939705846681)
                    ·
                      refine ⟨331049193644204779385011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441398924858939705846681 331049193644204779385011)
                      ·
                        rfl

theorem cell23_644716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_644716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644716 prefixEnd_644716 := by exact prefixLift 644716
  have htrace : WordTrace (prefixWord ++ tailWord_644716) baseStart_644716 baseEnd_644716 := by
    simpa [prefixWord, tailWord_644716, baseEnd_644716] using wordTrace_append hprefix tailTrace_644716
  have hstable : (prefixWord ++ tailWord_644716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644716).length < 2 ^ (prefixWord ++ tailWord_644716).sum := by decide
  have hdescent : baseEnd_644716 < baseStart_644716 := by decide
  rcases family_descends (prefixWord ++ tailWord_644716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644740 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_644740 : Nat := 118140960795 + 644740 * 2 ^ 59
def prefixEnd_644740 : Nat := 4983230072969 + 3 ^ 40 * 644740 * 2
def baseEnd_644740 : Nat := 331061517179912685484901

theorem tailTrace_644740 : CollatzResearch.WordTrace tailWord_644740 prefixEnd_644740 331061517179912685484901 := by
  unfold tailWord_644740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757799842112283835289837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15677066456149711780386449 11757799842112283835289837)
  ·
    refine ⟨4409174940792106438233689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11757799842112283835289837 4409174940792106438233689)
    ·
      refine ⟨3306881205594079828675267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409174940792106438233689 3306881205594079828675267)
      ·
        refine ⟨4960321808391119743012901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306881205594079828675267 4960321808391119743012901)
        ·
          refine ⟨930060339073334951814919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4960321808391119743012901 930060339073334951814919)
          ·
            refine ⟨1395090508610002427722379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930060339073334951814919 1395090508610002427722379)
            ·
              refine ⟨2092635762915003641583569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395090508610002427722379 2092635762915003641583569)
              ·
                refine ⟨1569476822186252731187677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092635762915003641583569 1569476822186252731187677)
                ·
                  refine ⟨588553808319844774195379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1569476822186252731187677 588553808319844774195379)
                  ·
                    refine ⟨882830712479767161293069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 588553808319844774195379 882830712479767161293069)
                    ·
                      refine ⟨331061517179912685484901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 882830712479767161293069 331061517179912685484901)
                      ·
                        rfl

theorem cell23_644740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_644740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644740 prefixEnd_644740 := by exact prefixLift 644740
  have htrace : WordTrace (prefixWord ++ tailWord_644740) baseStart_644740 baseEnd_644740 := by
    simpa [prefixWord, tailWord_644740, baseEnd_644740] using wordTrace_append hprefix tailTrace_644740
  have hstable : (prefixWord ++ tailWord_644740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644740).length < 2 ^ (prefixWord ++ tailWord_644740).sum := by decide
  have hdescent : baseEnd_644740 < baseStart_644740 := by decide
  rcases family_descends (prefixWord ++ tailWord_644740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644750 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_644750 : Nat := 118140960795 + 644750 * 2 ^ 59
def prefixEnd_644750 : Nat := 4983230072969 + 3 ^ 40 * 644750 * 2
def baseEnd_644750 : Nat := 331066651986457646359855

theorem tailTrace_644750 : CollatzResearch.WordTrace tailWord_644750 prefixEnd_644750 331066651986457646359855 := by
  unfold tailWord_644750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939495551773542422305463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15677309609458892918962469 2939495551773542422305463)
  ·
    refine ⟨4409243327660313633458195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939495551773542422305463 4409243327660313633458195)
    ·
      refine ⟨6613864991490470450187293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409243327660313633458195 6613864991490470450187293)
      ·
        refine ⟨2480199371808926418820235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6613864991490470450187293 2480199371808926418820235)
        ·
          refine ⟨3720299057713389628230353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480199371808926418820235 3720299057713389628230353)
          ·
            refine ⟨2790224293285042221172765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720299057713389628230353 2790224293285042221172765)
            ·
              refine ⟨1046334109981890832939787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2790224293285042221172765 1046334109981890832939787)
              ·
                refine ⟨1569501164972836249409681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046334109981890832939787 1569501164972836249409681)
                ·
                  refine ⟨1177125873729627187057261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1569501164972836249409681 1177125873729627187057261)
                  ·
                    refine ⟨441422202648610195146473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1177125873729627187057261 441422202648610195146473)
                    ·
                      refine ⟨331066651986457646359855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441422202648610195146473 331066651986457646359855)
                      ·
                        rfl

theorem cell23_644750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_644750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644750 prefixEnd_644750 := by exact prefixLift 644750
  have htrace : WordTrace (prefixWord ++ tailWord_644750) baseStart_644750 baseEnd_644750 := by
    simpa [prefixWord, tailWord_644750, baseEnd_644750] using wordTrace_append hprefix tailTrace_644750
  have hstable : (prefixWord ++ tailWord_644750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644750).length < 2 ^ (prefixWord ++ tailWord_644750).sum := by decide
  have hdescent : baseEnd_644750 < baseStart_644750 := by decide
  rcases family_descends (prefixWord ++ tailWord_644750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644760 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 1, 5]
def baseStart_644760 : Nat := 118140960795 + 644760 * 2 ^ 59
def prefixEnd_644760 : Nat := 4983230072969 + 3 ^ 40 * 644760 * 2
def baseEnd_644760 : Nat := 110357262264334202411603

theorem tailTrace_644760 : CollatzResearch.WordTrace tailWord_644760 prefixEnd_644760 110357262264334202411603 := by
  unfold tailWord_644760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11758164572076055543153867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15677552762768074057538489 11758164572076055543153867)
  ·
    refine ⟨17637246858114083314730801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11758164572076055543153867 17637246858114083314730801)
    ·
      refine ⟨13227935143585562486048101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17637246858114083314730801 13227935143585562486048101)
      ·
        refine ⟨2480237839422292966134019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13227935143585562486048101 2480237839422292966134019)
        ·
          refine ⟨3720356759133439449201029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480237839422292966134019 3720356759133439449201029)
          ·
            refine ⟨697566892337519896725193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3720356759133439449201029 697566892337519896725193)
            ·
              refine ⟨523175169253139922543895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697566892337519896725193 523175169253139922543895)
              ·
                refine ⟨784762753879709883815843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523175169253139922543895 784762753879709883815843)
                ·
                  refine ⟨1177144130819564825723765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784762753879709883815843 1177144130819564825723765)
                  ·
                    refine ⟨110357262264334202411603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1177144130819564825723765 110357262264334202411603)
                    ·
                      rfl

theorem cell23_644760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_644760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644760 prefixEnd_644760 := by exact prefixLift 644760
  have htrace : WordTrace (prefixWord ++ tailWord_644760) baseStart_644760 baseEnd_644760 := by
    simpa [prefixWord, tailWord_644760, baseEnd_644760] using wordTrace_append hprefix tailTrace_644760
  have hstable : (prefixWord ++ tailWord_644760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644760).length < 2 ^ (prefixWord ++ tailWord_644760).sum := by decide
  have hdescent : baseEnd_644760 < baseStart_644760 := by decide
  rcases family_descends (prefixWord ++ tailWord_644760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644773 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_644773 : Nat := 118140960795 + 644773 * 2 ^ 59
def prefixEnd_644773 : Nat := 4983230072969 + 3 ^ 40 * 644773 * 2
def baseEnd_644773 : Nat := 110359487347170352124083

theorem tailTrace_644773 : CollatzResearch.WordTrace tailWord_644773 prefixEnd_644773 110359487347170352124083 := by
  unfold tailWord_644773
  simp only [CollatzResearch.WordTrace]
  refine ⟨23516803293105014306530973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15677868862070009537687315 23516803293105014306530973)
  ·
    refine ⟨8818801234914380364949115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23516803293105014306530973 8818801234914380364949115)
    ·
      refine ⟨13228201852371570547423673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8818801234914380364949115 13228201852371570547423673)
      ·
        refine ⟨9921151389278677910567755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13228201852371570547423673 9921151389278677910567755)
        ·
          refine ⟨14881727083918016865851633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9921151389278677910567755 14881727083918016865851633)
          ·
            refine ⟨11161295312938512649388725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14881727083918016865851633 11161295312938512649388725)
            ·
              refine ⟨1046371435587985560880193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11161295312938512649388725 1046371435587985560880193)
              ·
                refine ⟨784778576690989170660145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046371435587985560880193 784778576690989170660145)
                ·
                  refine ⟨588583932518241877995109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 784778576690989170660145 588583932518241877995109)
                  ·
                    refine ⟨110359487347170352124083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 588583932518241877995109 110359487347170352124083)
                    ·
                      rfl

theorem cell23_644773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_644773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644773 prefixEnd_644773 := by exact prefixLift 644773
  have htrace : WordTrace (prefixWord ++ tailWord_644773) baseStart_644773 baseEnd_644773 := by
    simpa [prefixWord, tailWord_644773, baseEnd_644773] using wordTrace_append hprefix tailTrace_644773
  have hstable : (prefixWord ++ tailWord_644773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644773).length < 2 ^ (prefixWord ++ tailWord_644773).sum := by decide
  have hdescent : baseEnd_644773 < baseStart_644773 := by decide
  rcases family_descends (prefixWord ++ tailWord_644773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644790 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_644790 : Nat := 118140960795 + 644790 * 2 ^ 59
def prefixEnd_644790 : Nat := 4983230072969 + 3 ^ 40 * 644790 * 2
def baseEnd_644790 : Nat := 110362397070879163286557

theorem tailTrace_644790 : CollatzResearch.WordTrace tailWord_644790 prefixEnd_644790 110362397070879163286557 := by
  unfold tailWord_644790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469838958377714138118739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15678282222695617473266549 1469838958377714138118739)
  ·
    refine ⟨2204758437566571207178109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1469838958377714138118739 2204758437566571207178109)
    ·
      refine ⟨826784414087464202691791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2204758437566571207178109 826784414087464202691791)
      ·
        refine ⟨1240176621131196304037687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826784414087464202691791 1240176621131196304037687)
        ·
          refine ⟨1860264931696794456056531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240176621131196304037687 1860264931696794456056531)
          ·
            refine ⟨2790397397545191684084797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860264931696794456056531 2790397397545191684084797)
            ·
              refine ⟨1046399024079446881531799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2790397397545191684084797 1046399024079446881531799)
              ·
                refine ⟨1569598536119170322297699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046399024079446881531799 1569598536119170322297699)
                ·
                  refine ⟨2354397804178755483446549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569598536119170322297699 2354397804178755483446549)
                  ·
                    refine ⟨110362397070879163286557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2354397804178755483446549 110362397070879163286557)
                    ·
                      rfl

theorem cell23_644790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_644790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644790 prefixEnd_644790 := by exact prefixLift 644790
  have htrace : WordTrace (prefixWord ++ tailWord_644790) baseStart_644790 baseEnd_644790 := by
    simpa [prefixWord, tailWord_644790, baseEnd_644790] using wordTrace_append hprefix tailTrace_644790
  have hstable : (prefixWord ++ tailWord_644790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644790).length < 2 ^ (prefixWord ++ tailWord_644790).sum := by decide
  have hdescent : baseEnd_644790 < baseStart_644790 := by decide
  rcases family_descends (prefixWord ++ tailWord_644790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644836 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_644836 : Nat := 118140960795 + 644836 * 2 ^ 59
def prefixEnd_644836 : Nat := 4983230072969 + 3 ^ 40 * 644836 * 2
def baseEnd_644836 : Nat := 331110811322744309884459

theorem tailTrace_644836 : CollatzResearch.WordTrace tailWord_644836 prefixEnd_644836 331110811322744309884459 := by
  unfold tailWord_644836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11759550545938388033037181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15679400727917850710716241 11759550545938388033037181)
  ·
    refine ⟨4409831454726895512388943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11759550545938388033037181 4409831454726895512388943)
    ·
      refine ⟨6614747182090343268583415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409831454726895512388943 6614747182090343268583415)
      ·
        refine ⟨9922120773135514902875123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614747182090343268583415 9922120773135514902875123)
        ·
          refine ⟨14883181159703272354312685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9922120773135514902875123 14883181159703272354312685)
          ·
            refine ⟨5581192934888727132867257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14883181159703272354312685 5581192934888727132867257)
            ·
              refine ⟨4185894701166545349650443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5581192934888727132867257 4185894701166545349650443)
              ·
                refine ⟨6278842051749818024475665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185894701166545349650443 6278842051749818024475665)
                ·
                  refine ⟨4709131538812363518356749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6278842051749818024475665 4709131538812363518356749)
                  ·
                    refine ⟨1765924327054636319383781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4709131538812363518356749 1765924327054636319383781)
                    ·
                      refine ⟨331110811322744309884459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1765924327054636319383781 331110811322744309884459)
                      ·
                        rfl

theorem cell23_644836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_644836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644836 prefixEnd_644836 := by exact prefixLift 644836
  have htrace : WordTrace (prefixWord ++ tailWord_644836) baseStart_644836 baseEnd_644836 := by
    simpa [prefixWord, tailWord_644836, baseEnd_644836] using wordTrace_append hprefix tailTrace_644836
  have hstable : (prefixWord ++ tailWord_644836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644836).length < 2 ^ (prefixWord ++ tailWord_644836).sum := by decide
  have hdescent : baseEnd_644836 < baseStart_644836 := by decide
  rcases family_descends (prefixWord ++ tailWord_644836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644846 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_644846 : Nat := 118140960795 + 644846 * 2 ^ 59
def prefixEnd_644846 : Nat := 4983230072969 + 3 ^ 40 * 644846 * 2
def baseEnd_644846 : Nat := 110371982043096423586471

theorem tailTrace_644846 : CollatzResearch.WordTrace tailWord_644846 prefixEnd_644846 110371982043096423586471 := by
  unfold tailWord_644846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939933227730068471742299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15679643881227031849292261 2939933227730068471742299)
  ·
    refine ⟨4409899841595102707613449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939933227730068471742299 4409899841595102707613449)
    ·
      refine ⟨3307424881196327030710087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409899841595102707613449 3307424881196327030710087)
      ·
        refine ⟨4961137321794490546065131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307424881196327030710087 4961137321794490546065131)
        ·
          refine ⟨7441705982691735819097697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961137321794490546065131 7441705982691735819097697)
          ·
            refine ⟨5581279487018801864323273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7441705982691735819097697 5581279487018801864323273)
            ·
              refine ⟨4185959615264101398242455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5581279487018801864323273 4185959615264101398242455)
              ·
                refine ⟨6278939422896152097363683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185959615264101398242455 6278939422896152097363683)
                ·
                  refine ⟨9418409134344228146045525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6278939422896152097363683 9418409134344228146045525)
                  ·
                    refine ⟨110371982043096423586471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9418409134344228146045525 110371982043096423586471)
                    ·
                      rfl

theorem cell23_644846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_644846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644846 prefixEnd_644846 := by exact prefixLift 644846
  have htrace : WordTrace (prefixWord ++ tailWord_644846) baseStart_644846 baseEnd_644846 := by
    simpa [prefixWord, tailWord_644846, baseEnd_644846] using wordTrace_append hprefix tailTrace_644846
  have hstable : (prefixWord ++ tailWord_644846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644846).length < 2 ^ (prefixWord ++ tailWord_644846).sum := by decide
  have hdescent : baseEnd_644846 < baseStart_644846 := by decide
  rcases family_descends (prefixWord ++ tailWord_644846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644856 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_644856 : Nat := 118140960795 + 644856 * 2 ^ 59
def prefixEnd_644856 : Nat := 4983230072969 + 3 ^ 40 * 644856 * 2
def baseEnd_644856 : Nat := 331121080935834231634367

theorem tailTrace_644856 : CollatzResearch.WordTrace tailWord_644856 prefixEnd_644856 331121080935834231634367 := by
  unfold tailWord_644856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11759915275902159740901211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15679887034536212987868281 11759915275902159740901211)
  ·
    refine ⟨17639872913853239611351817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11759915275902159740901211 17639872913853239611351817)
    ·
      refine ⟨13229904685389929708513863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17639872913853239611351817 13229904685389929708513863)
      ·
        refine ⟨19844857028084894562770795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13229904685389929708513863 19844857028084894562770795)
        ·
          refine ⟨29767285542127341844156193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19844857028084894562770795 29767285542127341844156193)
          ·
            refine ⟨22325464156595506383117145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29767285542127341844156193 22325464156595506383117145)
            ·
              refine ⟨16744098117446629787337859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22325464156595506383117145 16744098117446629787337859)
              ·
                refine ⟨25116147176169944681006789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16744098117446629787337859 25116147176169944681006789)
                ·
                  refine ⟨4709277595531864627688773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25116147176169944681006789 4709277595531864627688773)
                  ·
                    refine ⟨882989549162224617691645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4709277595531864627688773 882989549162224617691645)
                    ·
                      refine ⟨331121080935834231634367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 882989549162224617691645 331121080935834231634367)
                      ·
                        rfl

theorem cell23_644856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_644856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644856 prefixEnd_644856 := by exact prefixLift 644856
  have htrace : WordTrace (prefixWord ++ tailWord_644856) baseStart_644856 baseEnd_644856 := by
    simpa [prefixWord, tailWord_644856, baseEnd_644856] using wordTrace_append hprefix tailTrace_644856
  have hstable : (prefixWord ++ tailWord_644856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644856).length < 2 ^ (prefixWord ++ tailWord_644856).sum := by decide
  have hdescent : baseEnd_644856 < baseStart_644856 := by decide
  rcases family_descends (prefixWord ++ tailWord_644856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644887 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 2, 2, 2]
def baseStart_644887 : Nat := 118140960795 + 644887 * 2 ^ 59
def prefixEnd_644887 : Nat := 4983230072969 + 3 ^ 40 * 644887 * 2
def baseEnd_644887 : Nat := 331136998836123610346725

theorem tailTrace_644887 : CollatzResearch.WordTrace tailWord_644887 prefixEnd_644887 331136998836123610346725 := by
  unfold tailWord_644887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23520961214692011776180915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15680640809794674517453943 23520961214692011776180915)
  ·
    refine ⟨35281441822038017664271373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23520961214692011776180915 35281441822038017664271373)
    ·
      refine ⟨13230540683264256624101765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35281441822038017664271373 13230540683264256624101765)
      ·
        refine ⟨2480726378112048117019081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13230540683264256624101765 2480726378112048117019081)
        ·
          refine ⟨1860544783584036087764311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2480726378112048117019081 1860544783584036087764311)
          ·
            refine ⟨2790817175376054131646467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860544783584036087764311 2790817175376054131646467)
            ·
              refine ⟨4186225763064081197469701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790817175376054131646467 4186225763064081197469701)
              ·
                refine ⟨784917330574515224525569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4186225763064081197469701 784917330574515224525569)
                ·
                  refine ⟨588687997930886418394177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 784917330574515224525569 588687997930886418394177)
                  ·
                    refine ⟨441515998448164813795633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 588687997930886418394177 441515998448164813795633)
                    ·
                      refine ⟨331136998836123610346725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441515998448164813795633 331136998836123610346725)
                      ·
                        rfl

theorem cell23_644887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_644887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644887 prefixEnd_644887 := by exact prefixLift 644887
  have htrace : WordTrace (prefixWord ++ tailWord_644887) baseStart_644887 baseEnd_644887 := by
    simpa [prefixWord, tailWord_644887, baseEnd_644887] using wordTrace_append hprefix tailTrace_644887
  have hstable : (prefixWord ++ tailWord_644887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644887).length < 2 ^ (prefixWord ++ tailWord_644887).sum := by decide
  have hdescent : baseEnd_644887 < baseStart_644887 := by decide
  rcases family_descends (prefixWord ++ tailWord_644887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644910 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_644910 : Nat := 118140960795 + 644910 * 2 ^ 59
def prefixEnd_644910 : Nat := 4983230072969 + 3 ^ 40 * 644910 * 2
def baseEnd_644910 : Nat := 36794312099019668928791

theorem tailTrace_644910 : CollatzResearch.WordTrace tailWord_644910 prefixEnd_644910 36794312099019668928791 := by
  unfold tailWord_644910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940225011701085838033523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15681200062405791136178789 2940225011701085838033523)
  ·
    refine ⟨4410337517551628757050285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940225011701085838033523 4410337517551628757050285)
    ·
      refine ⟨1653876569081860783893857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4410337517551628757050285 1653876569081860783893857)
      ·
        refine ⟨1240407426811395587920393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1653876569081860783893857 1240407426811395587920393)
        ·
          refine ⟨930305570108546690940295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240407426811395587920393 930305570108546690940295)
          ·
            refine ⟨1395458355162820036410443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930305570108546690940295 1395458355162820036410443)
            ·
              refine ⟨2093187532744230054615665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395458355162820036410443 2093187532744230054615665)
              ·
                refine ⟨1569890649558172540961749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2093187532744230054615665 1569890649558172540961749)
                ·
                  refine ⟨36794312099019668928791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1569890649558172540961749 36794312099019668928791)
                  ·
                    rfl

theorem cell23_644910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_644910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644910 prefixEnd_644910 := by exact prefixLift 644910
  have htrace : WordTrace (prefixWord ++ tailWord_644910) baseStart_644910 baseEnd_644910 := by
    simpa [prefixWord, tailWord_644910, baseEnd_644910] using wordTrace_append hprefix tailTrace_644910
  have hstable : (prefixWord ++ tailWord_644910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644910).length < 2 ^ (prefixWord ++ tailWord_644910).sum := by decide
  have hdescent : baseEnd_644910 < baseStart_644910 := by decide
  rcases family_descends (prefixWord ++ tailWord_644910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644960 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 2, 4, 2]
def baseStart_644960 : Nat := 118140960795 + 644960 * 2 ^ 59
def prefixEnd_644960 : Nat := 4983230072969 + 3 ^ 40 * 644960 * 2
def baseEnd_644960 : Nat := 331174482923901824733889

theorem tailTrace_644960 : CollatzResearch.WordTrace tailWord_644960 prefixEnd_644960 331174482923901824733889 := by
  unfold tailWord_644960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11761811871713772621794167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15682415828951696829058889 11761811871713772621794167)
  ·
    refine ⟨17642717807570658932691251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11761811871713772621794167 17642717807570658932691251)
    ·
      refine ⟨26464076711355988399036877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17642717807570658932691251 26464076711355988399036877)
      ·
        refine ⟨9924028766758495649638829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26464076711355988399036877 9924028766758495649638829)
        ·
          refine ⟨3721510787534435868614561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9924028766758495649638829 3721510787534435868614561)
          ·
            refine ⟨2791133090650826901460921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3721510787534435868614561 2791133090650826901460921)
            ·
              refine ⟨2093349817988120176095691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791133090650826901460921 2093349817988120176095691)
              ·
                refine ⟨3140024726982180264143537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093349817988120176095691 3140024726982180264143537)
                ·
                  refine ⟨2355018545236635198107653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3140024726982180264143537 2355018545236635198107653)
                  ·
                    refine ⟨441565977231869099645185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2355018545236635198107653 441565977231869099645185)
                    ·
                      refine ⟨331174482923901824733889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441565977231869099645185 331174482923901824733889)
                      ·
                        rfl

theorem cell23_644960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_644960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644960 prefixEnd_644960 := by exact prefixLift 644960
  have htrace : WordTrace (prefixWord ++ tailWord_644960) baseStart_644960 baseEnd_644960 := by
    simpa [prefixWord, tailWord_644960, baseEnd_644960] using wordTrace_append hprefix tailTrace_644960
  have hstable : (prefixWord ++ tailWord_644960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644960).length < 2 ^ (prefixWord ++ tailWord_644960).sum := by decide
  have hdescent : baseEnd_644960 < baseStart_644960 := by decide
  rcases family_descends (prefixWord ++ tailWord_644960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645013 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_645013 : Nat := 118140960795 + 645013 * 2 ^ 59
def prefixEnd_645013 : Nat := 4983230072969 + 3 ^ 40 * 645013 * 2
def baseEnd_645013 : Nat := 110400565799530039123715

theorem tailTrace_645013 : CollatzResearch.WordTrace tailWord_645013 prefixEnd_645013 110400565799530039123715 := by
  unfold tailWord_645013
  simp only [CollatzResearch.WordTrace]
  refine ⟨23525556812235535295267693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15683704541490356863511795 23525556812235535295267693)
  ·
    refine ⟨8822083804588325735725385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23525556812235535295267693 8822083804588325735725385)
    ·
      refine ⟨6616562853441244301794039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8822083804588325735725385 6616562853441244301794039)
      ·
        refine ⟨9924844280161866452691059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6616562853441244301794039 9924844280161866452691059)
        ·
          refine ⟨14887266420242799679036589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924844280161866452691059 14887266420242799679036589)
          ·
            refine ⟨5582724907591049879638721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14887266420242799679036589 5582724907591049879638721)
            ·
              refine ⟨4187043680693287409729041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5582724907591049879638721 4187043680693287409729041)
              ·
                refine ⟨3140282760519965557296781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4187043680693287409729041 3140282760519965557296781)
                ·
                  refine ⟨1177606035194987083986293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3140282760519965557296781 1177606035194987083986293)
                  ·
                    refine ⟨110400565799530039123715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1177606035194987083986293 110400565799530039123715)
                    ·
                      rfl

theorem cell23_645013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_645013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645013 prefixEnd_645013 := by exact prefixLift 645013
  have htrace : WordTrace (prefixWord ++ tailWord_645013) baseStart_645013 baseEnd_645013 := by
    simpa [prefixWord, tailWord_645013, baseEnd_645013] using wordTrace_append hprefix tailTrace_645013
  have hstable : (prefixWord ++ tailWord_645013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645013).length < 2 ^ (prefixWord ++ tailWord_645013).sum := by decide
  have hdescent : baseEnd_645013 < baseStart_645013 := by decide
  rcases family_descends (prefixWord ++ tailWord_645013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645043 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 1, 6]
def baseStart_645043 : Nat := 118140960795 + 645043 * 2 ^ 59
def prefixEnd_645043 : Nat := 4983230072969 + 3 ^ 40 * 645043 * 2
def baseEnd_645043 : Nat := 110405700606074999998669

theorem tailTrace_645043 : CollatzResearch.WordTrace tailWord_645043 prefixEnd_645043 110405700606074999998669 := by
  unfold tailWord_645043
  simp only [CollatzResearch.WordTrace]
  refine ⟨23526651002126850418859783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15684434001417900279239855 23526651002126850418859783)
  ·
    refine ⟨35289976503190275628289675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23526651002126850418859783 35289976503190275628289675)
    ·
      refine ⟨52934964754785413442434513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35289976503190275628289675 52934964754785413442434513)
      ·
        refine ⟨39701223566089060081825885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52934964754785413442434513 39701223566089060081825885)
        ·
          refine ⟨14887958837283397530684707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39701223566089060081825885 14887958837283397530684707)
          ·
            refine ⟨22331938255925096296027061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14887958837283397530684707 22331938255925096296027061)
            ·
              refine ⟨2093619211492977777752537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22331938255925096296027061 2093619211492977777752537)
              ·
                refine ⟨1570214408619733333314403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2093619211492977777752537 1570214408619733333314403)
                ·
                  refine ⟨2355321612929599999971605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570214408619733333314403 2355321612929599999971605)
                  ·
                    refine ⟨110405700606074999998669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2355321612929599999971605 110405700606074999998669)
                    ·
                      rfl

theorem cell23_645043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 6].length) (baseStart_645043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645043 prefixEnd_645043 := by exact prefixLift 645043
  have htrace : WordTrace (prefixWord ++ tailWord_645043) baseStart_645043 baseEnd_645043 := by
    simpa [prefixWord, tailWord_645043, baseEnd_645043] using wordTrace_append hprefix tailTrace_645043
  have hstable : (prefixWord ++ tailWord_645043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645043).length < 2 ^ (prefixWord ++ tailWord_645043).sum := by decide
  have hdescent : baseEnd_645043 < baseStart_645043 := by decide
  rcases family_descends (prefixWord ++ tailWord_645043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645063 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_645063 : Nat := 118140960795 + 645063 * 2 ^ 59
def prefixEnd_645063 : Nat := 4983230072969 + 3 ^ 40 * 645063 * 2
def baseEnd_645063 : Nat := 331227371431314921745915

theorem tailTrace_645063 : CollatzResearch.WordTrace tailWord_645063 prefixEnd_645063 331227371431314921745915 := by
  unfold tailWord_645063
  simp only [CollatzResearch.WordTrace]
  refine ⟨23527380462054393834587843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15684920308036262556391895 23527380462054393834587843)
  ·
    refine ⟨35291070693081590751881765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23527380462054393834587843 35291070693081590751881765)
    ·
      refine ⟨6617075754952798265977831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35291070693081590751881765 6617075754952798265977831)
      ·
        refine ⟨9925613632429197398966747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617075754952798265977831 9925613632429197398966747)
        ·
          refine ⟨14888420448643796098450121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9925613632429197398966747 14888420448643796098450121)
          ·
            refine ⟨11166315336482847073837591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14888420448643796098450121 11166315336482847073837591)
            ·
              refine ⟨16749473004724270610756387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11166315336482847073837591 16749473004724270610756387)
              ·
                refine ⟨25124209507086405916134581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16749473004724270610756387 25124209507086405916134581)
                ·
                  refine ⟨2355394641289350554637617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25124209507086405916134581 2355394641289350554637617)
                  ·
                    refine ⟨1766545980967012915978213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2355394641289350554637617 1766545980967012915978213)
                    ·
                      refine ⟨331227371431314921745915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1766545980967012915978213 331227371431314921745915)
                      ·
                        rfl

theorem cell23_645063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_645063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645063 prefixEnd_645063 := by exact prefixLift 645063
  have htrace : WordTrace (prefixWord ++ tailWord_645063) baseStart_645063 baseEnd_645063 := by
    simpa [prefixWord, tailWord_645063, baseEnd_645063] using wordTrace_append hprefix tailTrace_645063
  have hstable : (prefixWord ++ tailWord_645063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645063).length < 2 ^ (prefixWord ++ tailWord_645063).sum := by decide
  have hdescent : baseEnd_645063 < baseStart_645063 := by decide
  rcases family_descends (prefixWord ++ tailWord_645063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645067 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 3, 2, 2]
def baseStart_645067 : Nat := 118140960795 + 645067 * 2 ^ 59
def prefixEnd_645067 : Nat := 4983230072969 + 3 ^ 40 * 645067 * 2
def baseEnd_645067 : Nat := 331229425353932906095897

theorem tailTrace_645067 : CollatzResearch.WordTrace tailWord_645067 prefixEnd_645067 331229425353932906095897 := by
  unfold tailWord_645067
  simp only [CollatzResearch.WordTrace]
  refine ⟨23527526354039902517733455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15685017569359935011822303 23527526354039902517733455)
  ·
    refine ⟨35291289531059853776600183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23527526354039902517733455 35291289531059853776600183)
    ·
      refine ⟨52936934296589780664900275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35291289531059853776600183 52936934296589780664900275)
      ·
        refine ⟨79405401444884670997350413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52936934296589780664900275 79405401444884670997350413)
        ·
          refine ⟨29777025541831751624006405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79405401444884670997350413 29777025541831751624006405)
          ·
            refine ⟨5583192289093453429501201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29777025541831751624006405 5583192289093453429501201)
            ·
              refine ⟨4187394216820090072125901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5583192289093453429501201 4187394216820090072125901)
              ·
                refine ⟨1570272831307533777047213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4187394216820090072125901 1570272831307533777047213)
                ·
                  refine ⟨588852311740325166392705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1570272831307533777047213 588852311740325166392705)
                  ·
                    refine ⟨441639233805243874794529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 588852311740325166392705 441639233805243874794529)
                    ·
                      refine ⟨331229425353932906095897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441639233805243874794529 331229425353932906095897)
                      ·
                        rfl

theorem cell23_645067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 2, 2].length) (baseStart_645067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645067 prefixEnd_645067 := by exact prefixLift 645067
  have htrace : WordTrace (prefixWord ++ tailWord_645067) baseStart_645067 baseEnd_645067 := by
    simpa [prefixWord, tailWord_645067, baseEnd_645067] using wordTrace_append hprefix tailTrace_645067
  have hstable : (prefixWord ++ tailWord_645067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645067).length < 2 ^ (prefixWord ++ tailWord_645067).sum := by decide
  have hdescent : baseEnd_645067 < baseStart_645067 := by decide
  rcases family_descends (prefixWord ++ tailWord_645067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645070 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_645070 : Nat := 118140960795 + 645070 * 2 ^ 59
def prefixEnd_645070 : Nat := 4983230072969 + 3 ^ 40 * 645070 * 2
def baseEnd_645070 : Nat := 331230965795896394358383

theorem tailTrace_645070 : CollatzResearch.WordTrace tailWord_645070 prefixEnd_645070 331230965795896394358383 := by
  unfold tailWord_645070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940954471628629253761583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15685090515352689353395109 2940954471628629253761583)
  ·
    refine ⟨4411431707442943880642375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940954471628629253761583 4411431707442943880642375)
    ·
      refine ⟨6617147561164415820963563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411431707442943880642375 6617147561164415820963563)
      ·
        refine ⟨9925721341746623731445345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617147561164415820963563 9925721341746623731445345)
        ·
          refine ⟨7444291006309967798584009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9925721341746623731445345 7444291006309967798584009)
          ·
            refine ⟨5583218254732475848938007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7444291006309967798584009 5583218254732475848938007)
            ·
              refine ⟨8374827382098713773407011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583218254732475848938007 8374827382098713773407011)
              ·
                refine ⟨12562241073148070660110517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8374827382098713773407011 12562241073148070660110517)
                ·
                  refine ⟨1177710100607631624385361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12562241073148070660110517 1177710100607631624385361)
                  ·
                    refine ⟨883282575455723718289021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1177710100607631624385361 883282575455723718289021)
                    ·
                      refine ⟨331230965795896394358383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 883282575455723718289021 331230965795896394358383)
                      ·
                        rfl

theorem cell23_645070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_645070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645070 prefixEnd_645070 := by exact prefixLift 645070
  have htrace : WordTrace (prefixWord ++ tailWord_645070) baseStart_645070 baseEnd_645070 := by
    simpa [prefixWord, tailWord_645070, baseEnd_645070] using wordTrace_append hprefix tailTrace_645070
  have hstable : (prefixWord ++ tailWord_645070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645070).length < 2 ^ (prefixWord ++ tailWord_645070).sum := by decide
  have hdescent : baseEnd_645070 < baseStart_645070 := by decide
  rcases family_descends (prefixWord ++ tailWord_645070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645077 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_645077 : Nat := 118140960795 + 645077 * 2 ^ 59
def prefixEnd_645077 : Nat := 4983230072969 + 3 ^ 40 * 645077 * 2
def baseEnd_645077 : Nat := 110411520053492622323617

theorem tailTrace_645077 : CollatzResearch.WordTrace tailWord_645077 prefixEnd_645077 110411520053492622323617 := by
  unfold tailWord_645077
  simp only [CollatzResearch.WordTrace]
  refine ⟨23527891084003674225597485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15685260722669116150398323 23527891084003674225597485)
  ·
    refine ⟨8822959156501377834599057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23527891084003674225597485 8822959156501377834599057)
    ·
      refine ⟨6617219367376033375949293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8822959156501377834599057 6617219367376033375949293)
      ·
        refine ⟨2481457262766012515980985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6617219367376033375949293 2481457262766012515980985)
        ·
          refine ⟨1861092947074509386985739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2481457262766012515980985 1861092947074509386985739)
          ·
            refine ⟨2791639420611764080478609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861092947074509386985739 2791639420611764080478609)
            ·
              refine ⟨2093729565458823060358957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791639420611764080478609 2093729565458823060358957)
              ·
                refine ⟨785148587047058647634609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2093729565458823060358957 785148587047058647634609)
                ·
                  refine ⟨588861440285293985725957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785148587047058647634609 588861440285293985725957)
                  ·
                    refine ⟨110411520053492622323617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 588861440285293985725957 110411520053492622323617)
                    ·
                      rfl

theorem cell23_645077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_645077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645077 prefixEnd_645077 := by exact prefixLift 645077
  have htrace : WordTrace (prefixWord ++ tailWord_645077) baseStart_645077 baseEnd_645077 := by
    simpa [prefixWord, tailWord_645077, baseEnd_645077] using wordTrace_append hprefix tailTrace_645077
  have hstable : (prefixWord ++ tailWord_645077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645077).length < 2 ^ (prefixWord ++ tailWord_645077).sum := by decide
  have hdescent : baseEnd_645077 < baseStart_645077 := by decide
  rcases family_descends (prefixWord ++ tailWord_645077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645080 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_645080 : Nat := 118140960795 + 645080 * 2 ^ 59
def prefixEnd_645080 : Nat := 4983230072969 + 3 ^ 40 * 645080 * 2
def baseEnd_645080 : Nat := 331236100602441355233337

theorem tailTrace_645080 : CollatzResearch.WordTrace tailWord_645080 prefixEnd_645080 331236100602441355233337 := by
  unfold tailWord_645080
  simp only [CollatzResearch.WordTrace]
  refine ⟨11764000251496402868978347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15685333668661870491971129 11764000251496402868978347)
  ·
    refine ⟨17646000377244604303467521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11764000251496402868978347 17646000377244604303467521)
    ·
      refine ⟨13234500282933453227600641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17646000377244604303467521 13234500282933453227600641)
      ·
        refine ⟨9925875212200089920700481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13234500282933453227600641 9925875212200089920700481)
        ·
          refine ⟨7444406409150067440525361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9925875212200089920700481 7444406409150067440525361)
          ·
            refine ⟨5583304806862550580394021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7444406409150067440525361 5583304806862550580394021)
            ·
              refine ⟨1046869651286728233823879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5583304806862550580394021 1046869651286728233823879)
              ·
                refine ⟨1570304476930092350735819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046869651286728233823879 1570304476930092350735819)
                ·
                  refine ⟨2355456715395138526103729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570304476930092350735819 2355456715395138526103729)
                  ·
                    refine ⟨1766592536546353894577797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2355456715395138526103729 1766592536546353894577797)
                    ·
                      refine ⟨331236100602441355233337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1766592536546353894577797 331236100602441355233337)
                      ·
                        rfl

theorem cell23_645080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_645080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645080 prefixEnd_645080 := by exact prefixLift 645080
  have htrace : WordTrace (prefixWord ++ tailWord_645080) baseStart_645080 baseEnd_645080 := by
    simpa [prefixWord, tailWord_645080, baseEnd_645080] using wordTrace_append hprefix tailTrace_645080
  have hstable : (prefixWord ++ tailWord_645080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645080).length < 2 ^ (prefixWord ++ tailWord_645080).sum := by decide
  have hdescent : baseEnd_645080 < baseStart_645080 := by decide
  rcases family_descends (prefixWord ++ tailWord_645080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645118 : List Nat := [4, 2, 2, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_645118 : Nat := 118140960795 + 645118 * 2 ^ 59
def prefixEnd_645118 : Nat := 4983230072969 + 3 ^ 40 * 645118 * 2
def baseEnd_645118 : Nat := 331255612867312206558163

theorem tailTrace_645118 : CollatzResearch.WordTrace tailWord_645118 prefixEnd_645118 331255612867312206558163 := by
  unfold tailWord_645118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941173309606892278480001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15686257651236758818560005 2941173309606892278480001)
  ·
    refine ⟨2205879982205169208860001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2941173309606892278480001 2205879982205169208860001)
    ·
      refine ⟨1654409986653876906645001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2205879982205169208860001 1654409986653876906645001)
      ·
        refine ⟨1240807489990407679983751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1654409986653876906645001 1240807489990407679983751)
        ·
          refine ⟨1861211234985611519975627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240807489990407679983751 1861211234985611519975627)
          ·
            refine ⟨2791816852478417279963441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861211234985611519975627 2791816852478417279963441)
            ·
              refine ⟨2093862639358812959972581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791816852478417279963441 2093862639358812959972581)
              ·
                refine ⟨392599244879777429994859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2093862639358812959972581 392599244879777429994859)
                ·
                  refine ⟨588898867319666144992289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392599244879777429994859 588898867319666144992289)
                  ·
                    refine ⟨441674150489749608744217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 588898867319666144992289 441674150489749608744217)
                    ·
                      refine ⟨331255612867312206558163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441674150489749608744217 331255612867312206558163)
                      ·
                        rfl

theorem cell23_645118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_645118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645118 prefixEnd_645118 := by exact prefixLift 645118
  have htrace : WordTrace (prefixWord ++ tailWord_645118) baseStart_645118 baseEnd_645118 := by
    simpa [prefixWord, tailWord_645118, baseEnd_645118] using wordTrace_append hprefix tailTrace_645118
  have hstable : (prefixWord ++ tailWord_645118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645118).length < 2 ^ (prefixWord ++ tailWord_645118).sum := by decide
  have hdescent : baseEnd_645118 < baseStart_645118 := by decide
  rcases family_descends (prefixWord ++ tailWord_645118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645123 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4]
def baseStart_645123 : Nat := 118140960795 + 645123 * 2 ^ 59
def prefixEnd_645123 : Nat := 4983230072969 + 3 ^ 40 * 645123 * 2
def baseEnd_645123 : Nat := 331258180270584686995639

theorem tailTrace_645123 : CollatzResearch.WordTrace tailWord_645123 prefixEnd_645123 331258180270584686995639 := by
  unfold tailWord_645123
  simp only [CollatzResearch.WordTrace]
  refine ⟨23529568841837024081772023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15686379227891349387848015 23529568841837024081772023)
  ·
    refine ⟨35294353262755536122658035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23529568841837024081772023 35294353262755536122658035)
    ·
      refine ⟨52941529894133304183987053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35294353262755536122658035 52941529894133304183987053)
      ·
        refine ⟨19853073710299989068995145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52941529894133304183987053 19853073710299989068995145)
        ·
          refine ⟨14889805282724991801746359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19853073710299989068995145 14889805282724991801746359)
          ·
            refine ⟨22334707924087487702619539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14889805282724991801746359 22334707924087487702619539)
            ·
              refine ⟨33502061886131231553929309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22334707924087487702619539 33502061886131231553929309)
              ·
                refine ⟨12563273207299211832723491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33502061886131231553929309 12563273207299211832723491)
                ·
                  refine ⟨18844909810948817749085237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12563273207299211832723491 18844909810948817749085237)
                  ·
                    refine ⟨1766710294776451663976741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18844909810948817749085237 1766710294776451663976741)
                    ·
                      refine ⟨331258180270584686995639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1766710294776451663976741 331258180270584686995639)
                      ·
                        rfl

theorem cell23_645123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_645123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645123 prefixEnd_645123 := by exact prefixLift 645123
  have htrace : WordTrace (prefixWord ++ tailWord_645123) baseStart_645123 baseEnd_645123 := by
    simpa [prefixWord, tailWord_645123, baseEnd_645123] using wordTrace_append hprefix tailTrace_645123
  have hstable : (prefixWord ++ tailWord_645123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645123).length < 2 ^ (prefixWord ++ tailWord_645123).sum := by decide
  have hdescent : baseEnd_645123 < baseStart_645123 := by decide
  rcases family_descends (prefixWord ++ tailWord_645123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645144 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 1, 3, 2]
def baseStart_645144 : Nat := 118140960795 + 645144 * 2 ^ 59
def prefixEnd_645144 : Nat := 4983230072969 + 3 ^ 40 * 645144 * 2
def baseEnd_645144 : Nat := 331268963364329104833043

theorem tailTrace_645144 : CollatzResearch.WordTrace tailWord_645144 prefixEnd_645144 331268963364329104833043 := by
  unfold tailWord_645144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765167387380472334143243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15686889849840629778857657 11765167387380472334143243)
  ·
    refine ⟨17647751081070708501214865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11765167387380472334143243 17647751081070708501214865)
    ·
      refine ⟨13235813310803031375911149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17647751081070708501214865 13235813310803031375911149)
      ·
        refine ⟨4963429991551136765966681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13235813310803031375911149 4963429991551136765966681)
        ·
          refine ⟨3722572493663352574475011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4963429991551136765966681 3722572493663352574475011)
          ·
            refine ⟨5583858740495028861712517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722572493663352574475011 5583858740495028861712517)
            ·
              refine ⟨1046973513842817911571097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5583858740495028861712517 1046973513842817911571097)
              ·
                refine ⟨785230135382113433678323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046973513842817911571097 785230135382113433678323)
                ·
                  refine ⟨1177845203073170150517485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785230135382113433678323 1177845203073170150517485)
                  ·
                    refine ⟨441691951152438806444057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1177845203073170150517485 441691951152438806444057)
                    ·
                      refine ⟨331268963364329104833043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441691951152438806444057 331268963364329104833043)
                      ·
                        rfl

theorem cell23_645144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_645144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645144 prefixEnd_645144 := by exact prefixLift 645144
  have htrace : WordTrace (prefixWord ++ tailWord_645144) baseStart_645144 baseEnd_645144 := by
    simpa [prefixWord, tailWord_645144, baseEnd_645144] using wordTrace_append hprefix tailTrace_645144
  have hstable : (prefixWord ++ tailWord_645144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645144).length < 2 ^ (prefixWord ++ tailWord_645144).sum := by decide
  have hdescent : baseEnd_645144 < baseStart_645144 := by decide
  rcases family_descends (prefixWord ++ tailWord_645144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645220 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_645220 : Nat := 118140960795 + 645220 * 2 ^ 59
def prefixEnd_645220 : Nat := 4983230072969 + 3 ^ 40 * 645220 * 2
def baseEnd_645220 : Nat := 331307987894070807482693

theorem tailTrace_645220 : CollatzResearch.WordTrace tailWord_645220 prefixEnd_645220 331307987894070807482693 := by
  unfold tailWord_645220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766553361242804824026557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15688737814990406432035409 11766553361242804824026557)
  ·
    refine ⟨4412457510466051809009959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11766553361242804824026557 4412457510466051809009959)
    ·
      refine ⟨6618686265699077713514939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4412457510466051809009959 6618686265699077713514939)
      ·
        refine ⟨9928029398548616570272409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6618686265699077713514939 9928029398548616570272409)
        ·
          refine ⟨7446022048911462427704307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9928029398548616570272409 7446022048911462427704307)
          ·
            refine ⟨11169033073367193641556461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446022048911462427704307 11169033073367193641556461)
            ·
              refine ⟨4188387402512697615583673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11169033073367193641556461 4188387402512697615583673)
              ·
                refine ⟨3141290551884523211687755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4188387402512697615583673 3141290551884523211687755)
                ·
                  refine ⟨4711935827826784817531633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141290551884523211687755 4711935827826784817531633)
                  ·
                    refine ⟨3533951870870088613148725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4711935827826784817531633 3533951870870088613148725)
                    ·
                      refine ⟨331307987894070807482693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3533951870870088613148725 331307987894070807482693)
                      ·
                        rfl

theorem cell23_645220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_645220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645220 prefixEnd_645220 := by exact prefixLift 645220
  have htrace : WordTrace (prefixWord ++ tailWord_645220) baseStart_645220 baseEnd_645220 := by
    simpa [prefixWord, tailWord_645220, baseEnd_645220] using wordTrace_append hprefix tailTrace_645220
  have hstable : (prefixWord ++ tailWord_645220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645220).length < 2 ^ (prefixWord ++ tailWord_645220).sum := by decide
  have hdescent : baseEnd_645220 < baseStart_645220 := by decide
  rcases family_descends (prefixWord ++ tailWord_645220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645257 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 3, 4]
def baseStart_645257 : Nat := 118140960795 + 645257 * 2 ^ 59
def prefixEnd_645257 : Nat := 4983230072969 + 3 ^ 40 * 645257 * 2
def baseEnd_645257 : Nat := 110442328892762387573341

theorem tailTrace_645257 : CollatzResearch.WordTrace tailWord_645257 prefixEnd_645257 110442328892762387573341 := by
  unfold tailWord_645257
  simp only [CollatzResearch.WordTrace]
  refine ⟨23534456223351564967150025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15689637482234376644766683 23534456223351564967150025)
  ·
    refine ⟨17650842167513673725362519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23534456223351564967150025 17650842167513673725362519)
    ·
      refine ⟨26476263251270510588043779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17650842167513673725362519 26476263251270510588043779)
      ·
        refine ⟨39714394876905765882065669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26476263251270510588043779 39714394876905765882065669)
        ·
          refine ⟨7446449039419831102887313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39714394876905765882065669 7446449039419831102887313)
          ·
            refine ⟨5584836779564873327165485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7446449039419831102887313 5584836779564873327165485)
            ·
              refine ⟨2094313792336827497687057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5584836779564873327165485 2094313792336827497687057)
              ·
                refine ⟨1570735344252620623265293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094313792336827497687057 1570735344252620623265293)
                ·
                  refine ⟨589025754094732733724485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1570735344252620623265293 589025754094732733724485)
                  ·
                    refine ⟨110442328892762387573341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 589025754094732733724485 110442328892762387573341)
                    ·
                      rfl

theorem cell23_645257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_645257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645257 prefixEnd_645257 := by exact prefixLift 645257
  have htrace : WordTrace (prefixWord ++ tailWord_645257) baseStart_645257 baseEnd_645257 := by
    simpa [prefixWord, tailWord_645257, baseEnd_645257] using wordTrace_append hprefix tailTrace_645257
  have hstable : (prefixWord ++ tailWord_645257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645257).length < 2 ^ (prefixWord ++ tailWord_645257).sum := by decide
  have hdescent : baseEnd_645257 < baseStart_645257 := by decide
  rcases family_descends (prefixWord ++ tailWord_645257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645307 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 3, 5, 2]
def baseStart_645307 : Nat := 118140960795 + 645307 * 2 ^ 59
def prefixEnd_645307 : Nat := 4983230072969 + 3 ^ 40 * 645307 * 2
def baseEnd_645307 : Nat := 331352660711011967094793

theorem tailTrace_645307 : CollatzResearch.WordTrace tailWord_645307 prefixEnd_645307 331352660711011967094793 := by
  unfold tailWord_645307
  simp only [CollatzResearch.WordTrace]
  refine ⟨23536279873170423506470175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15690853248780282337646783 23536279873170423506470175)
  ·
    refine ⟨35304419809755635259705263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23536279873170423506470175 35304419809755635259705263)
    ·
      refine ⟨52956629714633452889557895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35304419809755635259705263 52956629714633452889557895)
      ·
        refine ⟨79434944571950179334336843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52956629714633452889557895 79434944571950179334336843)
        ·
          refine ⟨119152416857925269001505265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79434944571950179334336843 119152416857925269001505265)
          ·
            refine ⟨89364312643443951751128949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119152416857925269001505265 89364312643443951751128949)
            ·
              refine ⟨8377904310322870476668339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89364312643443951751128949 8377904310322870476668339)
              ·
                refine ⟨12566856465484305715002509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377904310322870476668339 12566856465484305715002509)
                ·
                  refine ⟨4712571174556614643125941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12566856465484305715002509 4712571174556614643125941)
                  ·
                    refine ⟨441803547614682622793057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4712571174556614643125941 441803547614682622793057)
                    ·
                      refine ⟨331352660711011967094793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441803547614682622793057 331352660711011967094793)
                      ·
                        rfl

theorem cell23_645307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5, 2].length) (baseStart_645307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645307 prefixEnd_645307 := by exact prefixLift 645307
  have htrace : WordTrace (prefixWord ++ tailWord_645307) baseStart_645307 baseEnd_645307 := by
    simpa [prefixWord, tailWord_645307, baseEnd_645307] using wordTrace_append hprefix tailTrace_645307
  have hstable : (prefixWord ++ tailWord_645307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645307).length < 2 ^ (prefixWord ++ tailWord_645307).sum := by decide
  have hdescent : baseEnd_645307 < baseStart_645307 := by decide
  rcases family_descends (prefixWord ++ tailWord_645307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645317 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_645317 : Nat := 118140960795 + 645317 * 2 ^ 59
def prefixEnd_645317 : Nat := 4983230072969 + 3 ^ 40 * 645317 * 2
def baseEnd_645317 : Nat := 110452598505852309323249

theorem tailTrace_645317 : CollatzResearch.WordTrace tailWord_645317 prefixEnd_645317 110452598505852309323249 := by
  unfold tailWord_645317
  simp only [CollatzResearch.WordTrace]
  refine ⟨23536644603134195214334205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15691096402089463476222803 23536644603134195214334205)
  ·
    refine ⟨8826241726175323205375327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23536644603134195214334205 8826241726175323205375327)
    ·
      refine ⟨13239362589262984808062991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826241726175323205375327 13239362589262984808062991)
      ·
        refine ⟨19859043883894477212094487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13239362589262984808062991 19859043883894477212094487)
        ·
          refine ⟨29788565825841715818141731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19859043883894477212094487 29788565825841715818141731)
          ·
            refine ⟨44682848738762573727212597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29788565825841715818141731 44682848738762573727212597)
            ·
              refine ⟨4189017069258991286926181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44682848738762573727212597 4189017069258991286926181)
              ·
                refine ⟨785440700486060866298659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4189017069258991286926181 785440700486060866298659)
                ·
                  refine ⟨1178161050729091299447989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785440700486060866298659 1178161050729091299447989)
                  ·
                    refine ⟨110452598505852309323249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1178161050729091299447989 110452598505852309323249)
                    ·
                      rfl

theorem cell23_645317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_645317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645317 prefixEnd_645317 := by exact prefixLift 645317
  have htrace : WordTrace (prefixWord ++ tailWord_645317) baseStart_645317 baseEnd_645317 := by
    simpa [prefixWord, tailWord_645317, baseEnd_645317] using wordTrace_append hprefix tailTrace_645317
  have hstable : (prefixWord ++ tailWord_645317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645317).length < 2 ^ (prefixWord ++ tailWord_645317).sum := by decide
  have hdescent : baseEnd_645317 < baseStart_645317 := by decide
  rcases family_descends (prefixWord ++ tailWord_645317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645341 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_645341 : Nat := 118140960795 + 645341 * 2 ^ 59
def prefixEnd_645341 : Nat := 4983230072969 + 3 ^ 40 * 645341 * 2
def baseEnd_645341 : Nat := 331370119053264834069637

theorem tailTrace_645341 : CollatzResearch.WordTrace tailWord_645341 prefixEnd_645341 331370119053264834069637 := by
  unfold tailWord_645341
  simp only [CollatzResearch.WordTrace]
  refine ⟨23537519955047247313207877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15691679970031498208805251 23537519955047247313207877)
  ·
    refine ⟨4413284991571358871226477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23537519955047247313207877 4413284991571358871226477)
    ·
      refine ⟨1654981871839259576709929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4413284991571358871226477 1654981871839259576709929)
      ·
        refine ⟨1241236403879444682532447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1654981871839259576709929 1241236403879444682532447)
        ·
          refine ⟨1861854605819167023798671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241236403879444682532447 1861854605819167023798671)
          ·
            refine ⟨2792781908728750535698007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861854605819167023798671 2792781908728750535698007)
            ·
              refine ⟨4189172863093125803547011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792781908728750535698007 4189172863093125803547011)
              ·
                refine ⟨6283759294639688705320517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4189172863093125803547011 6283759294639688705320517)
                ·
                  refine ⟨1178204867744941632247597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6283759294639688705320517 1178204867744941632247597)
                  ·
                    refine ⟨441826825404353112092849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178204867744941632247597 441826825404353112092849)
                    ·
                      refine ⟨331370119053264834069637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441826825404353112092849 331370119053264834069637)
                      ·
                        rfl

theorem cell23_645341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_645341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645341 prefixEnd_645341 := by exact prefixLift 645341
  have htrace : WordTrace (prefixWord ++ tailWord_645341) baseStart_645341 baseEnd_645341 := by
    simpa [prefixWord, tailWord_645341, baseEnd_645341] using wordTrace_append hprefix tailTrace_645341
  have hstable : (prefixWord ++ tailWord_645341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645341).length < 2 ^ (prefixWord ++ tailWord_645341).sum := by decide
  have hdescent : baseEnd_645341 < baseStart_645341 := by decide
  rcases family_descends (prefixWord ++ tailWord_645341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645384 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_645384 : Nat := 118140960795 + 645384 * 2 ^ 59
def prefixEnd_645384 : Nat := 4983230072969 + 3 ^ 40 * 645384 * 2
def baseEnd_645384 : Nat := 331392198721408165831939

theorem tailTrace_645384 : CollatzResearch.WordTrace tailWord_645384 prefixEnd_645384 331392198721408165831939 := by
  unfold tailWord_645384
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769544146945732828511603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15692725529260977104682137 11769544146945732828511603)
  ·
    refine ⟨17654316220418599242767405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11769544146945732828511603 17654316220418599242767405)
    ·
      refine ⟨6620368582656974716037777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17654316220418599242767405 6620368582656974716037777)
      ·
        refine ⟨4965276436992731037028333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6620368582656974716037777 4965276436992731037028333)
        ·
          refine ⟨1861978663872274138885625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4965276436992731037028333 1861978663872274138885625)
          ·
            refine ⟨1396483997904205604164219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1861978663872274138885625 1396483997904205604164219)
            ·
              refine ⟨2094725996856308406246329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396483997904205604164219 2094725996856308406246329)
              ·
                refine ⟨1571044497642231304684747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094725996856308406246329 1571044497642231304684747)
                ·
                  refine ⟨2356566746463346957027121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571044497642231304684747 2356566746463346957027121)
                  ·
                    refine ⟨1767425059847510217770341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2356566746463346957027121 1767425059847510217770341)
                    ·
                      refine ⟨331392198721408165831939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1767425059847510217770341 331392198721408165831939)
                      ·
                        rfl

theorem cell23_645384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_645384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645384 prefixEnd_645384 := by exact prefixLift 645384
  have htrace : WordTrace (prefixWord ++ tailWord_645384) baseStart_645384 baseEnd_645384 := by
    simpa [prefixWord, tailWord_645384, baseEnd_645384] using wordTrace_append hprefix tailTrace_645384
  have hstable : (prefixWord ++ tailWord_645384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645384).length < 2 ^ (prefixWord ++ tailWord_645384).sum := by decide
  have hdescent : baseEnd_645384 < baseStart_645384 := by decide
  rcases family_descends (prefixWord ++ tailWord_645384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645388 : List Nat := [2, 2, 1, 2, 2, 2, 2, 5, 1, 2, 2]
def baseStart_645388 : Nat := 118140960795 + 645388 * 2 ^ 59
def prefixEnd_645388 : Nat := 4983230072969 + 3 ^ 40 * 645388 * 2
def baseEnd_645388 : Nat := 331394252644026150181921

theorem tailTrace_645388 : CollatzResearch.WordTrace tailWord_645388 prefixEnd_645388 331394252644026150181921 := by
  unfold tailWord_645388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769617092938487170084409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15692822790584649560112545 11769617092938487170084409)
  ·
    refine ⟨8827212819703865377563307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11769617092938487170084409 8827212819703865377563307)
    ·
      refine ⟨13240819229555798066344961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8827212819703865377563307 13240819229555798066344961)
      ·
        refine ⟨9930614422166848549758721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13240819229555798066344961 9930614422166848549758721)
        ·
          refine ⟨7447960816625136412319041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9930614422166848549758721 7447960816625136412319041)
          ·
            refine ⟨5585970612468852309239281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7447960816625136412319041 5585970612468852309239281)
            ·
              refine ⟨4189477959351639231929461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5585970612468852309239281 4189477959351639231929461)
              ·
                refine ⟨392763558689216177993387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4189477959351639231929461 392763558689216177993387)
                ·
                  refine ⟨589145338033824266990081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392763558689216177993387 589145338033824266990081)
                  ·
                    refine ⟨441859003525368200242561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 589145338033824266990081 441859003525368200242561)
                    ·
                      refine ⟨331394252644026150181921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441859003525368200242561 331394252644026150181921)
                      ·
                        rfl

theorem cell23_645388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_645388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645388 prefixEnd_645388 := by exact prefixLift 645388
  have htrace : WordTrace (prefixWord ++ tailWord_645388) baseStart_645388 baseEnd_645388 := by
    simpa [prefixWord, tailWord_645388, baseEnd_645388] using wordTrace_append hprefix tailTrace_645388
  have hstable : (prefixWord ++ tailWord_645388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645388).length < 2 ^ (prefixWord ++ tailWord_645388).sum := by decide
  have hdescent : baseEnd_645388 < baseStart_645388 := by decide
  rcases family_descends (prefixWord ++ tailWord_645388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645407 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 2, 7]
def baseStart_645407 : Nat := 118140960795 + 645407 * 2 ^ 59
def prefixEnd_645407 : Nat := 4983230072969 + 3 ^ 40 * 645407 * 2
def baseEnd_645407 : Nat := 110468002925487191948111

theorem tailTrace_645407 : CollatzResearch.WordTrace tailWord_645407 prefixEnd_645407 110468002925487191948111 := by
  unfold tailWord_645407
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539927172808140585110475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15693284781872093723406983 23539927172808140585110475)
  ·
    refine ⟨35309890759212210877665713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23539927172808140585110475 35309890759212210877665713)
    ·
      refine ⟨26482418069409158158249285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35309890759212210877665713 26482418069409158158249285)
      ·
        refine ⟨4965453388014217154671741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26482418069409158158249285 4965453388014217154671741)
        ·
          refine ⟨1862045020505331433001903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4965453388014217154671741 1862045020505331433001903)
          ·
            refine ⟨2793067530757997149502855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862045020505331433001903 2793067530757997149502855)
            ·
              refine ⟨4189601296136995724254283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2793067530757997149502855 4189601296136995724254283)
              ·
                refine ⟨6284401944205493586381425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4189601296136995724254283 6284401944205493586381425)
                ·
                  refine ⟨4713301458154120189786069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6284401944205493586381425 4713301458154120189786069)
                  ·
                    refine ⟨110468002925487191948111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4713301458154120189786069 110468002925487191948111)
                    ·
                      rfl

theorem cell23_645407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_645407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645407 prefixEnd_645407 := by exact prefixLift 645407
  have htrace : WordTrace (prefixWord ++ tailWord_645407) baseStart_645407 baseEnd_645407 := by
    simpa [prefixWord, tailWord_645407, baseEnd_645407] using wordTrace_append hprefix tailTrace_645407
  have hstable : (prefixWord ++ tailWord_645407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645407).length < 2 ^ (prefixWord ++ tailWord_645407).sum := by decide
  have hdescent : baseEnd_645407 < baseStart_645407 := by decide
  rcases family_descends (prefixWord ++ tailWord_645407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645427 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4]
def baseStart_645427 : Nat := 118140960795 + 645427 * 2 ^ 59
def prefixEnd_645427 : Nat := 4983230072969 + 3 ^ 40 * 645427 * 2
def baseEnd_645427 : Nat := 331414278389551497594241

theorem tailTrace_645427 : CollatzResearch.WordTrace tailWord_645427 prefixEnd_645427 331414278389551497594241 := by
  unfold tailWord_645427
  simp only [CollatzResearch.WordTrace]
  refine ⟨23540656632735684000838535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15693771088490456000559023 23540656632735684000838535)
  ·
    refine ⟨35310984949103526001257803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23540656632735684000838535 35310984949103526001257803)
    ·
      refine ⟨52966477423655289001886705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35310984949103526001257803 52966477423655289001886705)
      ·
        refine ⟨39724858067741466751415029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52966477423655289001886705 39724858067741466751415029)
        ·
          refine ⟨3724205443850762507945159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39724858067741466751415029 3724205443850762507945159)
          ·
            refine ⟨5586308165776143761917739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724205443850762507945159 5586308165776143761917739)
            ·
              refine ⟨8379462248664215642876609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586308165776143761917739 8379462248664215642876609)
              ·
                refine ⟨6284596686498161732157457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8379462248664215642876609 6284596686498161732157457)
                ·
                  refine ⟨4713447514873621299118093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6284596686498161732157457 4713447514873621299118093)
                  ·
                    refine ⟨1767542818077607987169285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4713447514873621299118093 1767542818077607987169285)
                    ·
                      refine ⟨331414278389551497594241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1767542818077607987169285 331414278389551497594241)
                      ·
                        rfl

theorem cell23_645427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_645427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645427 prefixEnd_645427 := by exact prefixLift 645427
  have htrace : WordTrace (prefixWord ++ tailWord_645427) baseStart_645427 baseEnd_645427 := by
    simpa [prefixWord, tailWord_645427, baseEnd_645427] using wordTrace_append hprefix tailTrace_645427
  have hstable : (prefixWord ++ tailWord_645427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645427).length < 2 ^ (prefixWord ++ tailWord_645427).sum := by decide
  have hdescent : baseEnd_645427 < baseStart_645427 := by decide
  rcases family_descends (prefixWord ++ tailWord_645427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645447 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_645447 : Nat := 118140960795 + 645447 * 2 ^ 59
def prefixEnd_645447 : Nat := 4983230072969 + 3 ^ 40 * 645447 * 2
def baseEnd_645447 : Nat := 331424548002641419344149

theorem tailTrace_645447 : CollatzResearch.WordTrace tailWord_645447 prefixEnd_645447 331424548002641419344149 := by
  unfold tailWord_645447
  simp only [CollatzResearch.WordTrace]
  refine ⟨23541386092663227416566595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15694257395108818277711063 23541386092663227416566595)
  ·
    refine ⟨35312079138994841124849893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23541386092663227416566595 35312079138994841124849893)
    ·
      refine ⟨6621014838561532710909355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35312079138994841124849893 6621014838561532710909355)
      ·
        refine ⟨9931522257842299066364033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6621014838561532710909355 9931522257842299066364033)
        ·
          refine ⟨7448641693381724299773025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9931522257842299066364033 7448641693381724299773025)
          ·
            refine ⟨5586481270036293224829769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7448641693381724299773025 5586481270036293224829769)
            ·
              refine ⟨4189860952527219918622327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5586481270036293224829769 4189860952527219918622327)
              ·
                refine ⟨6284791428790829877933491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4189860952527219918622327 6284791428790829877933491)
                ·
                  refine ⟨9427187143186244816900237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6284791428790829877933491 9427187143186244816900237)
                  ·
                    refine ⟨3535195178694841806337589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9427187143186244816900237 3535195178694841806337589)
                    ·
                      refine ⟨331424548002641419344149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3535195178694841806337589 331424548002641419344149)
                      ·
                        rfl

theorem cell23_645447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_645447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645447 prefixEnd_645447 := by exact prefixLift 645447
  have htrace : WordTrace (prefixWord ++ tailWord_645447) baseStart_645447 baseEnd_645447 := by
    simpa [prefixWord, tailWord_645447, baseEnd_645447] using wordTrace_append hprefix tailTrace_645447
  have hstable : (prefixWord ++ tailWord_645447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645447).length < 2 ^ (prefixWord ++ tailWord_645447).sum := by decide
  have hdescent : baseEnd_645447 < baseStart_645447 := by decide
  rcases family_descends (prefixWord ++ tailWord_645447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645448 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_645448 : Nat := 118140960795 + 645448 * 2 ^ 59
def prefixEnd_645448 : Nat := 4983230072969 + 3 ^ 40 * 645448 * 2
def baseEnd_645448 : Nat := 331425061483295915431645

theorem tailTrace_645448 : CollatzResearch.WordTrace tailWord_645448 prefixEnd_645448 331425061483295915431645 := by
  unfold tailWord_645448
  simp only [CollatzResearch.WordTrace]
  refine ⟨11770711282829802293676499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15694281710439736391568665 11770711282829802293676499)
  ·
    refine ⟨17656066924244703440514749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11770711282829802293676499 17656066924244703440514749)
    ·
      refine ⟨6621025096591763790193031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17656066924244703440514749 6621025096591763790193031)
      ·
        refine ⟨9931537644887645685289547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6621025096591763790193031 9931537644887645685289547)
        ·
          refine ⟨14897306467331468527934321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9931537644887645685289547 14897306467331468527934321)
          ·
            refine ⟨11172979850498601395950741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14897306467331468527934321 11172979850498601395950741)
            ·
              refine ⟨523733430492121940435191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11172979850498601395950741 523733430492121940435191)
              ·
                refine ⟨785600145738182910652787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523733430492121940435191 785600145738182910652787)
                ·
                  refine ⟨1178400218607274365979181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785600145738182910652787 1178400218607274365979181)
                  ·
                    refine ⟨441900081977727887242193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178400218607274365979181 441900081977727887242193)
                    ·
                      refine ⟨331425061483295915431645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441900081977727887242193 331425061483295915431645)
                      ·
                        rfl

theorem cell23_645448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_645448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645448 prefixEnd_645448 := by exact prefixLift 645448
  have htrace : WordTrace (prefixWord ++ tailWord_645448) baseStart_645448 baseEnd_645448 := by
    simpa [prefixWord, tailWord_645448, baseEnd_645448] using wordTrace_append hprefix tailTrace_645448
  have hstable : (prefixWord ++ tailWord_645448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645448).length < 2 ^ (prefixWord ++ tailWord_645448).sum := by decide
  have hdescent : baseEnd_645448 < baseStart_645448 := by decide
  rcases family_descends (prefixWord ++ tailWord_645448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645501 : List Nat := [1, 4, 1, 1, 2, 3, 3, 3, 5]
def baseStart_645501 : Nat := 118140960795 + 645501 * 2 ^ 59
def prefixEnd_645501 : Nat := 4983230072969 + 3 ^ 40 * 645501 * 2
def baseEnd_645501 : Nat := 36828030661998245340989

theorem tailTrace_645501 : CollatzResearch.WordTrace tailWord_645501 prefixEnd_645501 36828030661998245340989 := by
  unfold tailWord_645501
  simp only [CollatzResearch.WordTrace]
  refine ⟨23543355634467594639032357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15695570422978396426021571 23543355634467594639032357)
  ·
    refine ⟨4414379181462673994818567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23543355634467594639032357 4414379181462673994818567)
    ·
      refine ⟨6621568772194010992227851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4414379181462673994818567 6621568772194010992227851)
      ·
        refine ⟨9932353158291016488341777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6621568772194010992227851 9932353158291016488341777)
        ·
          refine ⟨7449264868718262366256333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9932353158291016488341777 7449264868718262366256333)
          ·
            refine ⟨2793474325769348387346125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7449264868718262366256333 2793474325769348387346125)
            ·
              refine ⟨1047552872163505645254797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2793474325769348387346125 1047552872163505645254797)
              ·
                refine ⟨392832327061314616970549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047552872163505645254797 392832327061314616970549)
                ·
                  refine ⟨36828030661998245340989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392832327061314616970549 36828030661998245340989)
                  ·
                    rfl

theorem cell23_645501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_645501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645501 prefixEnd_645501 := by exact prefixLift 645501
  have htrace : WordTrace (prefixWord ++ tailWord_645501) baseStart_645501 baseEnd_645501 := by
    simpa [prefixWord, tailWord_645501, baseEnd_645501] using wordTrace_append hprefix tailTrace_645501
  have hstable : (prefixWord ++ tailWord_645501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645501).length < 2 ^ (prefixWord ++ tailWord_645501).sum := by decide
  have hdescent : baseEnd_645501 < baseStart_645501 := by decide
  rcases family_descends (prefixWord ++ tailWord_645501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645504 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 7, 2]
def baseStart_645504 : Nat := 118140960795 + 645504 * 2 ^ 59
def prefixEnd_645504 : Nat := 4983230072969 + 3 ^ 40 * 645504 * 2
def baseEnd_645504 : Nat := 331453816399947696331387

theorem tailTrace_645504 : CollatzResearch.WordTrace tailWord_645504 prefixEnd_645504 331453816399947696331387 := by
  unfold tailWord_645504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11771732526728363075695783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15695643368971150767594377 11771732526728363075695783)
  ·
    refine ⟨17657598790092544613543675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11771732526728363075695783 17657598790092544613543675)
    ·
      refine ⟨26486398185138816920315513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17657598790092544613543675 26486398185138816920315513)
      ·
        refine ⟨19864798638854112690236635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26486398185138816920315513 19864798638854112690236635)
        ·
          refine ⟨29797197958281169035354953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19864798638854112690236635 29797197958281169035354953)
          ·
            refine ⟨22347898468710876776516215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29797197958281169035354953 22347898468710876776516215)
            ·
              refine ⟨33521847703066315164774323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22347898468710876776516215 33521847703066315164774323)
              ·
                refine ⟨50282771554599472747161485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33521847703066315164774323 50282771554599472747161485)
                ·
                  refine ⟨18856039332974802280185557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50282771554599472747161485 18856039332974802280185557)
                  ·
                    refine ⟨441938421866596928441849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18856039332974802280185557 441938421866596928441849)
                    ·
                      refine ⟨331453816399947696331387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441938421866596928441849 331453816399947696331387)
                      ·
                        rfl

theorem cell23_645504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_645504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645504 prefixEnd_645504 := by exact prefixLift 645504
  have htrace : WordTrace (prefixWord ++ tailWord_645504) baseStart_645504 baseEnd_645504 := by
    simpa [prefixWord, tailWord_645504, baseEnd_645504] using wordTrace_append hprefix tailTrace_645504
  have hstable : (prefixWord ++ tailWord_645504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645504).length < 2 ^ (prefixWord ++ tailWord_645504).sum := by decide
  have hdescent : baseEnd_645504 < baseStart_645504 := by decide
  rcases family_descends (prefixWord ++ tailWord_645504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645569 : List Nat := [1, 2, 7, 1, 1, 2, 2, 2, 5]
def baseStart_645569 : Nat := 118140960795 + 645569 * 2 ^ 59
def prefixEnd_645569 : Nat := 4983230072969 + 3 ^ 40 * 645569 * 2
def baseEnd_645569 : Nat := 36831910293609993557621

theorem tailTrace_645569 : CollatzResearch.WordTrace tailWord_645569 prefixEnd_645569 36831910293609993557621 := by
  unfold tailWord_645569
  simp only [CollatzResearch.WordTrace]
  refine ⟨23545835798221242252507761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15697223865480828168338507 23545835798221242252507761)
  ·
    refine ⟨17659376848665931689380821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23545835798221242252507761 17659376848665931689380821)
    ·
      refine ⟨413891644890607773969863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17659376848665931689380821 413891644890607773969863)
      ·
        refine ⟨620837467335911660954795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413891644890607773969863 620837467335911660954795)
        ·
          refine ⟨931256201003867491432193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620837467335911660954795 931256201003867491432193)
          ·
            refine ⟨698442150752900618574145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931256201003867491432193 698442150752900618574145)
            ·
              refine ⟨523831613064675463930609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698442150752900618574145 523831613064675463930609)
              ·
                refine ⟨392873709798506597947957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523831613064675463930609 392873709798506597947957)
                ·
                  refine ⟨36831910293609993557621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392873709798506597947957 36831910293609993557621)
                  ·
                    rfl

theorem cell23_645569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 5].length) (baseStart_645569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645569 prefixEnd_645569 := by exact prefixLift 645569
  have htrace : WordTrace (prefixWord ++ tailWord_645569) baseStart_645569 baseEnd_645569 := by
    simpa [prefixWord, tailWord_645569, baseEnd_645569] using wordTrace_append hprefix tailTrace_645569
  have hstable : (prefixWord ++ tailWord_645569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645569).length < 2 ^ (prefixWord ++ tailWord_645569).sum := by decide
  have hdescent : baseEnd_645569 < baseStart_645569 := by decide
  rcases family_descends (prefixWord ++ tailWord_645569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645578 : List Nat := [3, 1, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_645578 : Nat := 118140960795 + 645578 * 2 ^ 59
def prefixEnd_645578 : Nat := 4983230072969 + 3 ^ 40 * 645578 * 2
def baseEnd_645578 : Nat := 110497271322793468935349

theorem tailTrace_645578 : CollatzResearch.WordTrace tailWord_645578 prefixEnd_645578 110497271322793468935349 := by
  unfold tailWord_645578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886541013797159197396347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15697442703459091193056925 5886541013797159197396347)
  ·
    refine ⟨8829811520695738796094521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5886541013797159197396347 8829811520695738796094521)
    ·
      refine ⟨6622358640521804097070891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8829811520695738796094521 6622358640521804097070891)
      ·
        refine ⟨9933537960782706145606337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6622358640521804097070891 9933537960782706145606337)
        ·
          refine ⟨7450153470587029609204753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9933537960782706145606337 7450153470587029609204753)
          ·
            refine ⟨5587615102940272206903565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7450153470587029609204753 5587615102940272206903565)
            ·
              refine ⟨2095355663602602077588837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5587615102940272206903565 2095355663602602077588837)
              ·
                refine ⟨392879186925487889547907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2095355663602602077588837 392879186925487889547907)
                ·
                  refine ⟨589318780388231834321861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392879186925487889547907 589318780388231834321861)
                  ·
                    refine ⟨110497271322793468935349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 589318780388231834321861 110497271322793468935349)
                    ·
                      rfl

theorem cell23_645578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_645578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645578 prefixEnd_645578 := by exact prefixLift 645578
  have htrace : WordTrace (prefixWord ++ tailWord_645578) baseStart_645578 baseEnd_645578 := by
    simpa [prefixWord, tailWord_645578, baseEnd_645578] using wordTrace_append hprefix tailTrace_645578
  have hstable : (prefixWord ++ tailWord_645578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645578).length < 2 ^ (prefixWord ++ tailWord_645578).sum := by decide
  have hdescent : baseEnd_645578 < baseStart_645578 := by decide
  rcases family_descends (prefixWord ++ tailWord_645578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645602 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_645602 : Nat := 118140960795 + 645602 * 2 ^ 59
def prefixEnd_645602 : Nat := 4983230072969 + 3 ^ 40 * 645602 * 2
def baseEnd_645602 : Nat := 331504137504088312905937

theorem tailTrace_645602 : CollatzResearch.WordTrace tailWord_645602 prefixEnd_645602 331504137504088312905937 := by
  unfold tailWord_645602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886759851775422222114765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15698026271401125925639373 5886759851775422222114765)
  ·
    refine ⟨2207534944415783333293037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5886759851775422222114765 2207534944415783333293037)
    ·
      refine ⟨827825604155918749984889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2207534944415783333293037 827825604155918749984889)
      ·
        refine ⟨620869203116939062488667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 827825604155918749984889 620869203116939062488667)
        ·
          refine ⟨931303804675408593733001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620869203116939062488667 931303804675408593733001)
          ·
            refine ⟨698477853506556445299751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931303804675408593733001 698477853506556445299751)
            ·
              refine ⟨1047716780259834667949627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698477853506556445299751 1047716780259834667949627)
              ·
                refine ⟨1571575170389752001924441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047716780259834667949627 1571575170389752001924441)
                ·
                  refine ⟨1178681377792314001443331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1571575170389752001924441 1178681377792314001443331)
                  ·
                    refine ⟨1768022066688471002164997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1178681377792314001443331 1768022066688471002164997)
                    ·
                      refine ⟨331504137504088312905937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1768022066688471002164997 331504137504088312905937)
                      ·
                        rfl

theorem cell23_645602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_645602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645602 prefixEnd_645602 := by exact prefixLift 645602
  have htrace : WordTrace (prefixWord ++ tailWord_645602) baseStart_645602 baseEnd_645602 := by
    simpa [prefixWord, tailWord_645602, baseEnd_645602] using wordTrace_append hprefix tailTrace_645602
  have hstable : (prefixWord ++ tailWord_645602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645602).length < 2 ^ (prefixWord ++ tailWord_645602).sum := by decide
  have hdescent : baseEnd_645602 < baseStart_645602 := by decide
  rcases family_descends (prefixWord ++ tailWord_645602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645605 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_645605 : Nat := 118140960795 + 645605 * 2 ^ 59
def prefixEnd_645605 : Nat := 4983230072969 + 3 ^ 40 * 645605 * 2
def baseEnd_645605 : Nat := 331505677946051801168423

theorem tailTrace_645605 : CollatzResearch.WordTrace tailWord_645605 prefixEnd_645605 331505677946051801168423 := by
  unfold tailWord_645605
  simp only [CollatzResearch.WordTrace]
  refine ⟨23547148826090820400818269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15698099217393880267212179 23547148826090820400818269)
  ·
    refine ⟨8830180809784057650306851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23547148826090820400818269 8830180809784057650306851)
    ·
      refine ⟨13245271214676086475460277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8830180809784057650306851 13245271214676086475460277)
      ·
        refine ⟨1241744176375883107074401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13245271214676086475460277 1241744176375883107074401)
        ·
          refine ⟨931308132281912330305801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241744176375883107074401 931308132281912330305801)
          ·
            refine ⟨698481099211434247729351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931308132281912330305801 698481099211434247729351)
            ·
              refine ⟨1047721648817151371594027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698481099211434247729351 1047721648817151371594027)
              ·
                refine ⟨1571582473225727057391041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047721648817151371594027 1571582473225727057391041)
                ·
                  refine ⟨1178686854919295293043281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1571582473225727057391041 1178686854919295293043281)
                  ·
                    refine ⟨884015141189471469782461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1178686854919295293043281 884015141189471469782461)
                    ·
                      refine ⟨331505677946051801168423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 884015141189471469782461 331505677946051801168423)
                      ·
                        rfl

theorem cell23_645605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_645605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645605 prefixEnd_645605 := by exact prefixLift 645605
  have htrace : WordTrace (prefixWord ++ tailWord_645605) baseStart_645605 baseEnd_645605 := by
    simpa [prefixWord, tailWord_645605, baseEnd_645605] using wordTrace_append hprefix tailTrace_645605
  have hstable : (prefixWord ++ tailWord_645605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645605).length < 2 ^ (prefixWord ++ tailWord_645605).sum := by decide
  have hdescent : baseEnd_645605 < baseStart_645605 := by decide
  rcases family_descends (prefixWord ++ tailWord_645605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645611 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 1, 5, 2]
def baseStart_645611 : Nat := 118140960795 + 645611 * 2 ^ 59
def prefixEnd_645611 : Nat := 4983230072969 + 3 ^ 40 * 645611 * 2
def baseEnd_645611 : Nat := 331508758829978777693395

theorem tailTrace_645611 : CollatzResearch.WordTrace tailWord_645611 prefixEnd_645611 331508758829978777693395 := by
  unfold tailWord_645611
  simp only [CollatzResearch.WordTrace]
  refine ⟨23547367664069083425536687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15698245109379388950357791 23547367664069083425536687)
  ·
    refine ⟨35321051496103625138305031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23547367664069083425536687 35321051496103625138305031)
    ·
      refine ⟨52981577244155437707457547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35321051496103625138305031 52981577244155437707457547)
      ·
        refine ⟨79472365866233156561186321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52981577244155437707457547 79472365866233156561186321)
        ·
          refine ⟨59604274399674867420889741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79472365866233156561186321 59604274399674867420889741)
          ·
            refine ⟨22351602899878075282833653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59604274399674867420889741 22351602899878075282833653)
            ·
              refine ⟨2095462771863569557765655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22351602899878075282833653 2095462771863569557765655)
              ·
                refine ⟨3143194157795354336648483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095462771863569557765655 3143194157795354336648483)
                ·
                  refine ⟨4714791236693031504972725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143194157795354336648483 4714791236693031504972725)
                  ·
                    refine ⟨442011678439971703591193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4714791236693031504972725 442011678439971703591193)
                    ·
                      refine ⟨331508758829978777693395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442011678439971703591193 331508758829978777693395)
                      ·
                        rfl

theorem cell23_645611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5, 2].length) (baseStart_645611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645611 prefixEnd_645611 := by exact prefixLift 645611
  have htrace : WordTrace (prefixWord ++ tailWord_645611) baseStart_645611 baseEnd_645611 := by
    simpa [prefixWord, tailWord_645611, baseEnd_645611] using wordTrace_append hprefix tailTrace_645611
  have hstable : (prefixWord ++ tailWord_645611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645611).length < 2 ^ (prefixWord ++ tailWord_645611).sum := by decide
  have hdescent : baseEnd_645611 < baseStart_645611 := by decide
  rcases family_descends (prefixWord ++ tailWord_645611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645655 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 1, 5]
def baseStart_645655 : Nat := 118140960795 + 645655 * 2 ^ 59
def prefixEnd_645655 : Nat := 4983230072969 + 3 ^ 40 * 645655 * 2
def baseEnd_645655 : Nat := 110510450659592201847731

theorem tailTrace_645655 : CollatzResearch.WordTrace tailWord_645655 prefixEnd_645655 110510450659592201847731 := by
  unfold tailWord_645655
  simp only [CollatzResearch.WordTrace]
  refine ⟨23548972475909678940138419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15699314983939785960092279 23548972475909678940138419)
  ·
    refine ⟨35323458713864518410207629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23548972475909678940138419 35323458713864518410207629)
    ·
      refine ⟨13246297017699194403827861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35323458713864518410207629 13246297017699194403827861)
      ·
        refine ⟨620920172704649737679431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13246297017699194403827861 620920172704649737679431)
        ·
          refine ⟨931380259056974606519147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620920172704649737679431 931380259056974606519147)
          ·
            refine ⟨1397070388585461909778721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931380259056974606519147 1397070388585461909778721)
            ·
              refine ⟨1047802791439096432334041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397070388585461909778721 1047802791439096432334041)
              ·
                refine ⟨785852093579322324250531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047802791439096432334041 785852093579322324250531)
                ·
                  refine ⟨1178778140368983486375797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785852093579322324250531 1178778140368983486375797)
                  ·
                    refine ⟨110510450659592201847731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1178778140368983486375797 110510450659592201847731)
                    ·
                      rfl

theorem cell23_645655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_645655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645655 prefixEnd_645655 := by exact prefixLift 645655
  have htrace : WordTrace (prefixWord ++ tailWord_645655) baseStart_645655 baseEnd_645655 := by
    simpa [prefixWord, tailWord_645655, baseEnd_645655] using wordTrace_append hprefix tailTrace_645655
  have hstable : (prefixWord ++ tailWord_645655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645655).length < 2 ^ (prefixWord ++ tailWord_645655).sum := by decide
  have hdescent : baseEnd_645655 < baseStart_645655 := by decide
  rcases family_descends (prefixWord ++ tailWord_645655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645692 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_645692 : Nat := 118140960795 + 645692 * 2 ^ 59
def prefixEnd_645692 : Nat := 4983230072969 + 3 ^ 40 * 645692 * 2
def baseEnd_645692 : Nat := 331550350762992960780523

theorem tailTrace_645692 : CollatzResearch.WordTrace tailWord_645692 prefixEnd_645692 331550350762992960780523 := by
  unfold tailWord_645692
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775160988387817129617665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15700214651183756172823553 11775160988387817129617665)
  ·
    refine ⟨8831370741290862847213249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11775160988387817129617665 8831370741290862847213249)
    ·
      refine ⟨6623528055968147135409937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8831370741290862847213249 6623528055968147135409937)
      ·
        refine ⟨4967646041976110351557453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6623528055968147135409937 4967646041976110351557453)
        ·
          refine ⟨1862867265741041381834045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4967646041976110351557453 1862867265741041381834045)
          ·
            refine ⟨698575224652890518187767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1862867265741041381834045 698575224652890518187767)
            ·
              refine ⟨1047862836979335777281651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698575224652890518187767 1047862836979335777281651)
              ·
                refine ⟨1571794255469003665922477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047862836979335777281651 1571794255469003665922477)
                ·
                  refine ⟨589422845800876374720929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1571794255469003665922477 589422845800876374720929)
                  ·
                    refine ⟨442067134350657281040697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 589422845800876374720929 442067134350657281040697)
                    ·
                      refine ⟨331550350762992960780523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442067134350657281040697 331550350762992960780523)
                      ·
                        rfl

theorem cell23_645692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_645692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645692 prefixEnd_645692 := by exact prefixLift 645692
  have htrace : WordTrace (prefixWord ++ tailWord_645692) baseStart_645692 baseEnd_645692 := by
    simpa [prefixWord, tailWord_645692, baseEnd_645692] using wordTrace_append hprefix tailTrace_645692
  have hstable : (prefixWord ++ tailWord_645692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645692).length < 2 ^ (prefixWord ++ tailWord_645692).sum := by decide
  have hdescent : baseEnd_645692 < baseStart_645692 := by decide
  rcases family_descends (prefixWord ++ tailWord_645692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645702 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_645702 : Nat := 118140960795 + 645702 * 2 ^ 59
def prefixEnd_645702 : Nat := 4983230072969 + 3 ^ 40 * 645702 * 2
def baseEnd_645702 : Nat := 110518495189845973885159

theorem tailTrace_645702 : CollatzResearch.WordTrace tailWord_645702 prefixEnd_645702 110518495189845973885159 := by
  unfold tailWord_645702
  simp only [CollatzResearch.WordTrace]
  refine ⟨735958959585606436471855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15700457804492937311399573 735958959585606436471855)
  ·
    refine ⟨1103938439378409654707783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 735958959585606436471855 1103938439378409654707783)
    ·
      refine ⟨1655907659067614482061675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103938439378409654707783 1655907659067614482061675)
      ·
        refine ⟨2483861488601421723092513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655907659067614482061675 2483861488601421723092513)
        ·
          refine ⟨1862896116451066292319385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2483861488601421723092513 1862896116451066292319385)
          ·
            refine ⟨1397172087338299719239539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1862896116451066292319385 1397172087338299719239539)
            ·
              refine ⟨2095758131007449578859309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397172087338299719239539 2095758131007449578859309)
              ·
                refine ⟨785909299127793592072241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2095758131007449578859309 785909299127793592072241)
                ·
                  refine ⟨589431974345845194054181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785909299127793592072241 589431974345845194054181)
                  ·
                    refine ⟨110518495189845973885159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 589431974345845194054181 110518495189845973885159)
                    ·
                      rfl

theorem cell23_645702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_645702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645702 prefixEnd_645702 := by exact prefixLift 645702
  have htrace : WordTrace (prefixWord ++ tailWord_645702) baseStart_645702 baseEnd_645702 := by
    simpa [prefixWord, tailWord_645702, baseEnd_645702] using wordTrace_append hprefix tailTrace_645702
  have hstable : (prefixWord ++ tailWord_645702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645702).length < 2 ^ (prefixWord ++ tailWord_645702).sum := by decide
  have hdescent : baseEnd_645702 < baseStart_645702 := by decide
  rcases family_descends (prefixWord ++ tailWord_645702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645726 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_645726 : Nat := 118140960795 + 645726 * 2 ^ 59
def prefixEnd_645726 : Nat := 4983230072969 + 3 ^ 40 * 645726 * 2
def baseEnd_645726 : Nat := 331567809105245827755367

theorem tailTrace_645726 : CollatzResearch.WordTrace tailWord_645726 prefixEnd_645726 331567809105245827755367 := by
  unfold tailWord_645726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2943945257331557258246629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15701041372434972043982021 2943945257331557258246629)
  ·
    refine ⟨551989735749666985921243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2943945257331557258246629 551989735749666985921243)
    ·
      refine ⟨827984603624500478881865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551989735749666985921243 827984603624500478881865)
      ·
        refine ⟨620988452718375359161399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 827984603624500478881865 620988452718375359161399)
        ·
          refine ⟨931482679077563038742099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620988452718375359161399 931482679077563038742099)
          ·
            refine ⟨1397224018616344558113149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931482679077563038742099 1397224018616344558113149)
            ·
              refine ⟨523959006981129209292431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1397224018616344558113149 523959006981129209292431)
              ·
                refine ⟨785938510471693813938647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523959006981129209292431 785938510471693813938647)
                ·
                  refine ⟨1178907765707540720907971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785938510471693813938647 1178907765707540720907971)
                  ·
                    refine ⟨1768361648561311081361957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1178907765707540720907971 1768361648561311081361957)
                    ·
                      refine ⟨331567809105245827755367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1768361648561311081361957 331567809105245827755367)
                      ·
                        rfl

theorem cell23_645726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_645726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645726 prefixEnd_645726 := by exact prefixLift 645726
  have htrace : WordTrace (prefixWord ++ tailWord_645726) baseStart_645726 baseEnd_645726 := by
    simpa [prefixWord, tailWord_645726, baseEnd_645726] using wordTrace_append hprefix tailTrace_645726
  have hstable : (prefixWord ++ tailWord_645726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645726).length < 2 ^ (prefixWord ++ tailWord_645726).sum := by decide
  have hdescent : baseEnd_645726 < baseStart_645726 := by decide
  rcases family_descends (prefixWord ++ tailWord_645726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645742 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_645742 : Nat := 118140960795 + 645742 * 2 ^ 59
def prefixEnd_645742 : Nat := 4983230072969 + 3 ^ 40 * 645742 * 2
def baseEnd_645742 : Nat := 331576024795717765155293

theorem tailTrace_645742 : CollatzResearch.WordTrace tailWord_645742 prefixEnd_645742 331576024795717765155293 := by
  unfold tailWord_645742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2944018203324311599819435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15701430417729661865703653 2944018203324311599819435)
  ·
    refine ⟨4416027304986467399729153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2944018203324311599819435 4416027304986467399729153)
    ·
      refine ⟨3312020478739850549796865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4416027304986467399729153 3312020478739850549796865)
      ·
        refine ⟨2484015359054887912347649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3312020478739850549796865 2484015359054887912347649)
        ·
          refine ⟨1863011519291165934260737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2484015359054887912347649 1863011519291165934260737)
          ·
            refine ⟨1397258639468374450695553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863011519291165934260737 1397258639468374450695553)
            ·
              refine ⟨1047943979601280838021665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397258639468374450695553 1047943979601280838021665)
              ·
                refine ⟨785957984700960628516249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047943979601280838021665 785957984700960628516249)
                ·
                  refine ⟨589468488525720471387187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785957984700960628516249 589468488525720471387187)
                  ·
                    refine ⟨884202732788580707080781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 589468488525720471387187 884202732788580707080781)
                    ·
                      refine ⟨331576024795717765155293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 884202732788580707080781 331576024795717765155293)
                      ·
                        rfl

theorem cell23_645742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_645742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645742 prefixEnd_645742 := by exact prefixLift 645742
  have htrace : WordTrace (prefixWord ++ tailWord_645742) baseStart_645742 baseEnd_645742 := by
    simpa [prefixWord, tailWord_645742, baseEnd_645742] using wordTrace_append hprefix tailTrace_645742
  have hstable : (prefixWord ++ tailWord_645742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645742).length < 2 ^ (prefixWord ++ tailWord_645742).sum := by decide
  have hdescent : baseEnd_645742 < baseStart_645742 := by decide
  rcases family_descends (prefixWord ++ tailWord_645742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645751 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_645751 : Nat := 118140960795 + 645751 * 2 ^ 59
def prefixEnd_645751 : Nat := 4983230072969 + 3 ^ 40 * 645751 * 2
def baseEnd_645751 : Nat := 331580646121608229942751

theorem tailTrace_645751 : CollatzResearch.WordTrace tailWord_645751 prefixEnd_645751 331580646121608229942751 := by
  unfold tailWord_645751
  simp only [CollatzResearch.WordTrace]
  refine ⟨23552473883561887335633107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15701649255707924890422071 23552473883561887335633107)
  ·
    refine ⟨35328710825342831003449661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23552473883561887335633107 35328710825342831003449661)
    ·
      refine ⟨13248266559503561626293623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35328710825342831003449661 13248266559503561626293623)
      ·
        refine ⟨19872399839255342439440435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13248266559503561626293623 19872399839255342439440435)
        ·
          refine ⟨29808599758883013659160653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19872399839255342439440435 29808599758883013659160653)
          ·
            refine ⟨11178224909581130122185245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29808599758883013659160653 11178224909581130122185245)
            ·
              refine ⟨4191834341092923795819467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11178224909581130122185245 4191834341092923795819467)
              ·
                refine ⟨6287751511639385693729201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191834341092923795819467 6287751511639385693729201)
                ·
                  refine ⟨4715813633729539270296901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6287751511639385693729201 4715813633729539270296901)
                  ·
                    refine ⟨884215056324288613180669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4715813633729539270296901 884215056324288613180669)
                    ·
                      refine ⟨331580646121608229942751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 884215056324288613180669 331580646121608229942751)
                      ·
                        rfl

theorem cell23_645751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_645751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645751 prefixEnd_645751 := by exact prefixLift 645751
  have htrace : WordTrace (prefixWord ++ tailWord_645751) baseStart_645751 baseEnd_645751 := by
    simpa [prefixWord, tailWord_645751, baseEnd_645751] using wordTrace_append hprefix tailTrace_645751
  have hstable : (prefixWord ++ tailWord_645751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645751).length < 2 ^ (prefixWord ++ tailWord_645751).sum := by decide
  have hdescent : baseEnd_645751 < baseStart_645751 := by decide
  rcases family_descends (prefixWord ++ tailWord_645751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645765 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 1, 4, 2]
def baseStart_645765 : Nat := 118140960795 + 645765 * 2 ^ 59
def prefixEnd_645765 : Nat := 4983230072969 + 3 ^ 40 * 645765 * 2
def baseEnd_645765 : Nat := 331587834850771175167687

theorem tailTrace_645765 : CollatzResearch.WordTrace tailWord_645765 prefixEnd_645765 331587834850771175167687 := by
  unfold tailWord_645765
  simp only [CollatzResearch.WordTrace]
  refine ⟨23552984505511167726642749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15701989670340778484428499 23552984505511167726642749)
  ·
    refine ⟨8832369189566687897491031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23552984505511167726642749 8832369189566687897491031)
    ·
      refine ⟨13248553784350031846236547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8832369189566687897491031 13248553784350031846236547)
      ·
        refine ⟨19872830676525047769354821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13248553784350031846236547 19872830676525047769354821)
        ·
          refine ⟨3726155751848446456754029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19872830676525047769354821 3726155751848446456754029)
          ·
            refine ⟨1397308406943167421282761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3726155751848446456754029 1397308406943167421282761)
            ·
              refine ⟨1047981305207375565962071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397308406943167421282761 1047981305207375565962071)
              ·
                refine ⟨1571971957811063348943107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047981305207375565962071 1571971957811063348943107)
                ·
                  refine ⟨2357957936716595023414661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571971957811063348943107 2357957936716595023414661)
                  ·
                    refine ⟨442117113134361566890249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357957936716595023414661 442117113134361566890249)
                    ·
                      refine ⟨331587834850771175167687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442117113134361566890249 331587834850771175167687)
                      ·
                        rfl

theorem cell23_645765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_645765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645765 prefixEnd_645765 := by exact prefixLift 645765
  have htrace : WordTrace (prefixWord ++ tailWord_645765) baseStart_645765 baseEnd_645765 := by
    simpa [prefixWord, tailWord_645765, baseEnd_645765] using wordTrace_append hprefix tailTrace_645765
  have hstable : (prefixWord ++ tailWord_645765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645765).length < 2 ^ (prefixWord ++ tailWord_645765).sum := by decide
  have hdescent : baseEnd_645765 < baseStart_645765 := by decide
  rcases family_descends (prefixWord ++ tailWord_645765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645786 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2]
def baseStart_645786 : Nat := 118140960795 + 645786 * 2 ^ 59
def prefixEnd_645786 : Nat := 4983230072969 + 3 ^ 40 * 645786 * 2
def baseEnd_645786 : Nat := 331598617944515593005091

theorem tailTrace_645786 : CollatzResearch.WordTrace tailWord_645786 prefixEnd_645786 331598617944515593005091 := by
  unfold tailWord_645786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5888437609608772078289303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15702500292290058875438141 5888437609608772078289303)
  ·
    refine ⟨8832656414413158117433955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5888437609608772078289303 8832656414413158117433955)
    ·
      refine ⟨13248984621619737176150933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8832656414413158117433955 13248984621619737176150933)
      ·
        refine ⟨621046154138425180132075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13248984621619737176150933 621046154138425180132075)
        ·
          refine ⟨931569231207637770198113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621046154138425180132075 931569231207637770198113)
          ·
            refine ⟨698676923405728327648585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931569231207637770198113 698676923405728327648585)
            ·
              refine ⟨524007692554296245736439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698676923405728327648585 524007692554296245736439)
              ·
                refine ⟨786011538831444368604659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524007692554296245736439 786011538831444368604659)
                ·
                  refine ⟨1179017308247166552906989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786011538831444368604659 1179017308247166552906989)
                  ·
                    refine ⟨442131490592687457340121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1179017308247166552906989 442131490592687457340121)
                    ·
                      refine ⟨331598617944515593005091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442131490592687457340121 331598617944515593005091)
                      ·
                        rfl

theorem cell23_645786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_645786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645786 prefixEnd_645786 := by exact prefixLift 645786
  have htrace : WordTrace (prefixWord ++ tailWord_645786) baseStart_645786 baseEnd_645786 := by
    simpa [prefixWord, tailWord_645786, baseEnd_645786] using wordTrace_append hprefix tailTrace_645786
  have hstable : (prefixWord ++ tailWord_645786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645786).length < 2 ^ (prefixWord ++ tailWord_645786).sum := by decide
  have hdescent : baseEnd_645786 < baseStart_645786 := by decide
  rcases family_descends (prefixWord ++ tailWord_645786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645799 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_645799 : Nat := 118140960795 + 645799 * 2 ^ 59
def prefixEnd_645799 : Nat := 4983230072969 + 3 ^ 40 * 645799 * 2
def baseEnd_645799 : Nat := 331605293193024042142531

theorem tailTrace_645799 : CollatzResearch.WordTrace tailWord_645799 prefixEnd_645799 331605293193024042142531 := by
  unfold tailWord_645799
  simp only [CollatzResearch.WordTrace]
  refine ⟨23554224587387991533380451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15702816391591994355586967 23554224587387991533380451)
  ·
    refine ⟨35331336881081987300070677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23554224587387991533380451 35331336881081987300070677)
    ·
      refine ⟨1656156416300718154690813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35331336881081987300070677 1656156416300718154690813)
      ·
        refine ⟨621058656112769308009055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1656156416300718154690813 621058656112769308009055)
        ·
          refine ⟨931587984169153962013583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621058656112769308009055 931587984169153962013583)
          ·
            refine ⟨1397381976253730943020375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931587984169153962013583 1397381976253730943020375)
            ·
              refine ⟨2096072964380596414530563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397381976253730943020375 2096072964380596414530563)
              ·
                refine ⟨3144109446570894621795845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096072964380596414530563 3144109446570894621795845)
                ·
                  refine ⟨589520521232042741586721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3144109446570894621795845 589520521232042741586721)
                  ·
                    refine ⟨442140390924032056190041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 589520521232042741586721 442140390924032056190041)
                    ·
                      refine ⟨331605293193024042142531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442140390924032056190041 331605293193024042142531)
                      ·
                        rfl

theorem cell23_645799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_645799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645799 prefixEnd_645799 := by exact prefixLift 645799
  have htrace : WordTrace (prefixWord ++ tailWord_645799) baseStart_645799 baseEnd_645799 := by
    simpa [prefixWord, tailWord_645799, baseEnd_645799] using wordTrace_append hprefix tailTrace_645799
  have hstable : (prefixWord ++ tailWord_645799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645799).length < 2 ^ (prefixWord ++ tailWord_645799).sum := by decide
  have hdescent : baseEnd_645799 < baseStart_645799 := by decide
  rcases family_descends (prefixWord ++ tailWord_645799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645805 : List Nat := [1, 5, 2, 1, 1, 2, 2, 4, 5]
def baseStart_645805 : Nat := 118140960795 + 645805 * 2 ^ 59
def prefixEnd_645805 : Nat := 4983230072969 + 3 ^ 40 * 645805 * 2
def baseEnd_645805 : Nat := 36845374897439002074167

theorem tailTrace_645805 : CollatzResearch.WordTrace tailWord_645805 prefixEnd_645805 36845374897439002074167 := by
  unfold tailWord_645805
  simp only [CollatzResearch.WordTrace]
  refine ⟨23554443425366254558098869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15702962283577503038732579 23554443425366254558098869)
  ·
    refine ⟨2208229071128086364821769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23554443425366254558098869 2208229071128086364821769)
    ·
      refine ⟨1656171803346064773616327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2208229071128086364821769 1656171803346064773616327)
      ·
        refine ⟨2484257705019097160424491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1656171803346064773616327 2484257705019097160424491)
        ·
          refine ⟨3726386557528645740636737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484257705019097160424491 3726386557528645740636737)
          ·
            refine ⟨2794789918146484305477553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726386557528645740636737 2794789918146484305477553)
            ·
              refine ⟨2096092438609863229108165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2794789918146484305477553 2096092438609863229108165)
              ·
                refine ⟨393017332239349355457781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2096092438609863229108165 393017332239349355457781)
                ·
                  refine ⟨36845374897439002074167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393017332239349355457781 36845374897439002074167)
                  ·
                    rfl

theorem cell23_645805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_645805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645805 prefixEnd_645805 := by exact prefixLift 645805
  have htrace : WordTrace (prefixWord ++ tailWord_645805) baseStart_645805 baseEnd_645805 := by
    simpa [prefixWord, tailWord_645805, baseEnd_645805] using wordTrace_append hprefix tailTrace_645805
  have hstable : (prefixWord ++ tailWord_645805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645805).length < 2 ^ (prefixWord ++ tailWord_645805).sum := by decide
  have hdescent : baseEnd_645805 < baseStart_645805 := by decide
  rcases family_descends (prefixWord ++ tailWord_645805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645838 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_645838 : Nat := 118140960795 + 645838 * 2 ^ 59
def prefixEnd_645838 : Nat := 4983230072969 + 3 ^ 40 * 645838 * 2
def baseEnd_645838 : Nat := 331625318938549389554851

theorem tailTrace_645838 : CollatzResearch.WordTrace tailWord_645838 prefixEnd_645838 331625318938549389554851 := by
  unfold tailWord_645838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2944455879280837649256271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15703764689497800796033445 2944455879280837649256271)
  ·
    refine ⟨4416683818921256473884407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2944455879280837649256271 4416683818921256473884407)
    ·
      refine ⟨6625025728381884710826611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4416683818921256473884407 6625025728381884710826611)
      ·
        refine ⟨9937538592572827066239917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6625025728381884710826611 9937538592572827066239917)
        ·
          refine ⟨3726576972214810149839969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9937538592572827066239917 3726576972214810149839969)
          ·
            refine ⟨2794932729161107612379977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726576972214810149839969 2794932729161107612379977)
            ·
              refine ⟨2096199546870830709284983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2794932729161107612379977 2096199546870830709284983)
              ·
                refine ⟨3144299320306246063927475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096199546870830709284983 3144299320306246063927475)
                ·
                  refine ⟨4716448980459369095891213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144299320306246063927475 4716448980459369095891213)
                  ·
                    refine ⟨1768668367672263410959205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4716448980459369095891213 1768668367672263410959205)
                    ·
                      refine ⟨331625318938549389554851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1768668367672263410959205 331625318938549389554851)
                      ·
                        rfl

theorem cell23_645838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_645838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645838 prefixEnd_645838 := by exact prefixLift 645838
  have htrace : WordTrace (prefixWord ++ tailWord_645838) baseStart_645838 baseEnd_645838 := by
    simpa [prefixWord, tailWord_645838, baseEnd_645838] using wordTrace_append hprefix tailTrace_645838
  have hstable : (prefixWord ++ tailWord_645838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645838).length < 2 ^ (prefixWord ++ tailWord_645838).sum := by decide
  have hdescent : baseEnd_645838 < baseStart_645838 := by decide
  rcases family_descends (prefixWord ++ tailWord_645838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645865 : List Nat := [1, 2, 1, 1, 1, 2, 4, 6, 1, 4]
def baseStart_645865 : Nat := 118140960795 + 645865 * 2 ^ 59
def prefixEnd_645865 : Nat := 4983230072969 + 3 ^ 40 * 645865 * 2
def baseEnd_645865 : Nat := 110546394305406927972409

theorem tailTrace_645865 : CollatzResearch.WordTrace tailWord_645865 prefixEnd_645865 110546394305406927972409 := by
  unfold tailWord_645865
  simp only [CollatzResearch.WordTrace]
  refine ⟨23556631805148884805283049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15704421203432589870188699 23556631805148884805283049)
  ·
    refine ⟨17667473853861663603962287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23556631805148884805283049 17667473853861663603962287)
    ·
      refine ⟨26501210780792495405943431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17667473853861663603962287 26501210780792495405943431)
      ·
        refine ⟨39751816171188743108915147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26501210780792495405943431 39751816171188743108915147)
        ·
          refine ⟨59627724256783114663372721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39751816171188743108915147 59627724256783114663372721)
          ·
            refine ⟨44720793192587335997529541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59627724256783114663372721 44720793192587335997529541)
            ·
              refine ⟨8385148723610125499536789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44720793192587335997529541 8385148723610125499536789)
              ·
                refine ⟨393053846419224632790787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8385148723610125499536789 393053846419224632790787)
                ·
                  refine ⟨589580769628836949186181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393053846419224632790787 589580769628836949186181)
                  ·
                    refine ⟨110546394305406927972409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 589580769628836949186181 110546394305406927972409)
                    ·
                      rfl

theorem cell23_645865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 4].length) (baseStart_645865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645865 prefixEnd_645865 := by exact prefixLift 645865
  have htrace : WordTrace (prefixWord ++ tailWord_645865) baseStart_645865 baseEnd_645865 := by
    simpa [prefixWord, tailWord_645865, baseEnd_645865] using wordTrace_append hprefix tailTrace_645865
  have hstable : (prefixWord ++ tailWord_645865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645865).length < 2 ^ (prefixWord ++ tailWord_645865).sum := by decide
  have hdescent : baseEnd_645865 < baseStart_645865 := by decide
  rcases family_descends (prefixWord ++ tailWord_645865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645881 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_645881 : Nat := 118140960795 + 645881 * 2 ^ 59
def prefixEnd_645881 : Nat := 4983230072969 + 3 ^ 40 * 645881 * 2
def baseEnd_645881 : Nat := 331647398606692721317153

theorem tailTrace_645881 : CollatzResearch.WordTrace tailWord_645881 prefixEnd_645881 331647398606692721317153 := by
  unfold tailWord_645881
  simp only [CollatzResearch.WordTrace]
  refine ⟨23557215373090919537865497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15704810248727279691910331 23557215373090919537865497)
  ·
    refine ⟨17667911529818189653399123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23557215373090919537865497 17667911529818189653399123)
    ·
      refine ⟨26501867294727284480098685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17667911529818189653399123 26501867294727284480098685)
      ·
        refine ⟨9938200235522731680037007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26501867294727284480098685 9938200235522731680037007)
        ·
          refine ⟨14907300353284097520055511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9938200235522731680037007 14907300353284097520055511)
          ·
            refine ⟨22360950529926146280083267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14907300353284097520055511 22360950529926146280083267)
            ·
              refine ⟨33541425794889219420124901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22360950529926146280083267 33541425794889219420124901)
              ·
                refine ⟨6289017336541728641273419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33541425794889219420124901 6289017336541728641273419)
                ·
                  refine ⟨9433526004812592961910129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289017336541728641273419 9433526004812592961910129)
                  ·
                    refine ⟨7075144503609444721432597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9433526004812592961910129 7075144503609444721432597)
                    ·
                      refine ⟨331647398606692721317153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7075144503609444721432597 331647398606692721317153)
                      ·
                        rfl

theorem cell23_645881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_645881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645881 prefixEnd_645881 := by exact prefixLift 645881
  have htrace : WordTrace (prefixWord ++ tailWord_645881) baseStart_645881 baseEnd_645881 := by
    simpa [prefixWord, tailWord_645881, baseEnd_645881] using wordTrace_append hprefix tailTrace_645881
  have hstable : (prefixWord ++ tailWord_645881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645881).length < 2 ^ (prefixWord ++ tailWord_645881).sum := by decide
  have hdescent : baseEnd_645881 < baseStart_645881 := by decide
  rcases family_descends (prefixWord ++ tailWord_645881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645972 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_645972 : Nat := 118140960795 + 645972 * 2 ^ 59
def prefixEnd_645972 : Nat := 4983230072969 + 3 ^ 40 * 645972 * 2
def baseEnd_645972 : Nat := 110564708448750621759745

theorem tailTrace_645972 : CollatzResearch.WordTrace tailWord_645972 prefixEnd_645972 110564708448750621759745 := by
  unfold tailWord_645972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780267207880621039714085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15707022943840828052952113 11780267207880621039714085)
  ·
    refine ⟨2208800101477616444946391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11780267207880621039714085 2208800101477616444946391)
    ·
      refine ⟨3313200152216424667419587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208800101477616444946391 3313200152216424667419587)
      ·
        refine ⟨4969800228324637001129381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313200152216424667419587 4969800228324637001129381)
        ·
          refine ⟨931837542810869437711759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4969800228324637001129381 931837542810869437711759)
          ·
            refine ⟨1397756314216304156567639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931837542810869437711759 1397756314216304156567639)
            ·
              refine ⟨2096634471324456234851459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397756314216304156567639 2096634471324456234851459)
              ·
                refine ⟨3144951706986684352277189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096634471324456234851459 3144951706986684352277189)
                ·
                  refine ⟨589678445060003316051973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3144951706986684352277189 589678445060003316051973)
                  ·
                    refine ⟨110564708448750621759745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 589678445060003316051973 110564708448750621759745)
                    ·
                      rfl

theorem cell23_645972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_645972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645972 prefixEnd_645972 := by exact prefixLift 645972
  have htrace : WordTrace (prefixWord ++ tailWord_645972) baseStart_645972 baseEnd_645972 := by
    simpa [prefixWord, tailWord_645972, baseEnd_645972] using wordTrace_append hprefix tailTrace_645972
  have hstable : (prefixWord ++ tailWord_645972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645972).length < 2 ^ (prefixWord ++ tailWord_645972).sum := by decide
  have hdescent : baseEnd_645972 < baseStart_645972 := by decide
  rcases family_descends (prefixWord ++ tailWord_645972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645992 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_645992 : Nat := 118140960795 + 645992 * 2 ^ 59
def prefixEnd_645992 : Nat := 4983230072969 + 3 ^ 40 * 645992 * 2
def baseEnd_645992 : Nat := 331704394959341787029143

theorem tailTrace_645992 : CollatzResearch.WordTrace tailWord_645992 prefixEnd_645992 331704394959341787029143 := by
  unfold tailWord_645992
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780631937844392747578115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15707509250459190330104153 11780631937844392747578115)
  ·
    refine ⟨17670947906766589121367173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11780631937844392747578115 17670947906766589121367173)
    ·
      refine ⟨3313302732518735460256345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17670947906766589121367173 3313302732518735460256345)
      ·
        refine ⟨2484977049389051595192259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3313302732518735460256345 2484977049389051595192259)
        ·
          refine ⟨3727465574083577392788389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484977049389051595192259 3727465574083577392788389)
          ·
            refine ⟨698899795140670761147823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3727465574083577392788389 698899795140670761147823)
            ·
              refine ⟨1048349692711006141721735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698899795140670761147823 1048349692711006141721735)
              ·
                refine ⟨1572524539066509212582603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048349692711006141721735 1572524539066509212582603)
                ·
                  refine ⟨2358786808599763818873905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572524539066509212582603 2358786808599763818873905)
                  ·
                    refine ⟨1769090106449822864155429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358786808599763818873905 1769090106449822864155429)
                    ·
                      refine ⟨331704394959341787029143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1769090106449822864155429 331704394959341787029143)
                      ·
                        rfl

theorem cell23_645992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_645992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645992 prefixEnd_645992 := by exact prefixLift 645992
  have htrace : WordTrace (prefixWord ++ tailWord_645992) baseStart_645992 baseEnd_645992 := by
    simpa [prefixWord, tailWord_645992, baseEnd_645992] using wordTrace_append hprefix tailTrace_645992
  have hstable : (prefixWord ++ tailWord_645992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645992).length < 2 ^ (prefixWord ++ tailWord_645992).sum := by decide
  have hdescent : baseEnd_645992 < baseStart_645992 := by decide
  rcases family_descends (prefixWord ++ tailWord_645992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645995 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 3]
def baseStart_645995 : Nat := 118140960795 + 645995 * 2 ^ 59
def prefixEnd_645995 : Nat := 4983230072969 + 3 ^ 40 * 645995 * 2
def baseEnd_645995 : Nat := 331705935401305275291629

theorem tailTrace_645995 : CollatzResearch.WordTrace tailWord_645995 prefixEnd_645995 331705935401305275291629 := by
  unfold tailWord_645995
  simp only [CollatzResearch.WordTrace]
  refine ⟨23561373294677917007515439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15707582196451944671676959 23561373294677917007515439)
  ·
    refine ⟨35342059942016875511273159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23561373294677917007515439 35342059942016875511273159)
    ·
      refine ⟨53013089913025313266909739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35342059942016875511273159 53013089913025313266909739)
      ·
        refine ⟨79519634869537969900364609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53013089913025313266909739 79519634869537969900364609)
        ·
          refine ⟨59639726152153477425273457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79519634869537969900364609 59639726152153477425273457)
          ·
            refine ⟨44729794614115108068955093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59639726152153477425273457 44729794614115108068955093)
            ·
              refine ⟨1048354561268322845366135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44729794614115108068955093 1048354561268322845366135)
              ·
                refine ⟨1572531841902484268049203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048354561268322845366135 1572531841902484268049203)
                ·
                  refine ⟨2358797762853726402073805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572531841902484268049203 2358797762853726402073805)
                  ·
                    refine ⟨884549161070147400777677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358797762853726402073805 884549161070147400777677)
                    ·
                      refine ⟨331705935401305275291629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 884549161070147400777677 331705935401305275291629)
                      ·
                        rfl

theorem cell23_645995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 3].length) (baseStart_645995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_645995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_645995 prefixEnd_645995 := by exact prefixLift 645995
  have htrace : WordTrace (prefixWord ++ tailWord_645995) baseStart_645995 baseEnd_645995 := by
    simpa [prefixWord, tailWord_645995, baseEnd_645995] using wordTrace_append hprefix tailTrace_645995
  have hstable : (prefixWord ++ tailWord_645995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645995).length < 2 ^ (prefixWord ++ tailWord_645995).sum := by decide
  have hdescent : baseEnd_645995 < baseStart_645995 := by decide
  rcases family_descends (prefixWord ++ tailWord_645995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646028 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_646028 : Nat := 118140960795 + 646028 * 2 ^ 59
def prefixEnd_646028 : Nat := 4983230072969 + 3 ^ 40 * 646028 * 2
def baseEnd_646028 : Nat := 110574293420967882059659

theorem tailTrace_646028 : CollatzResearch.WordTrace tailWord_646028 prefixEnd_646028 110574293420967882059659 := by
  unfold tailWord_646028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11781288451779181821733369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15708384602372242428977825 11781288451779181821733369)
  ·
    refine ⟨8835966338834386366300027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11781288451779181821733369 8835966338834386366300027)
    ·
      refine ⟨13253949508251579549450041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8835966338834386366300027 13253949508251579549450041)
      ·
        refine ⟨9940462131188684662087531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13253949508251579549450041 9940462131188684662087531)
        ·
          refine ⟨14910693196783026993131297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9940462131188684662087531 14910693196783026993131297)
          ·
            refine ⟨11183019897587270244848473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14910693196783026993131297 11183019897587270244848473)
            ·
              refine ⟨8387264923190452683636355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11183019897587270244848473 8387264923190452683636355)
              ·
                refine ⟨12580897384785679025454533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8387264923190452683636355 12580897384785679025454533)
                ·
                  refine ⟨2358918259647314817272725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12580897384785679025454533 2358918259647314817272725)
                  ·
                    refine ⟨110574293420967882059659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2358918259647314817272725 110574293420967882059659)
                    ·
                      rfl

theorem cell23_646028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_646028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646028 prefixEnd_646028 := by exact prefixLift 646028
  have htrace : WordTrace (prefixWord ++ tailWord_646028) baseStart_646028 baseEnd_646028 := by
    simpa [prefixWord, tailWord_646028, baseEnd_646028] using wordTrace_append hprefix tailTrace_646028
  have hstable : (prefixWord ++ tailWord_646028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646028).length < 2 ^ (prefixWord ++ tailWord_646028).sum := by decide
  have hdescent : baseEnd_646028 < baseStart_646028 := by decide
  rcases family_descends (prefixWord ++ tailWord_646028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646035 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 5, 4, 2]
def baseStart_646035 : Nat := 118140960795 + 646035 * 2 ^ 59
def prefixEnd_646035 : Nat := 4983230072969 + 3 ^ 40 * 646035 * 2
def baseEnd_646035 : Nat := 331726474627485118791445

theorem tailTrace_646035 : CollatzResearch.WordTrace tailWord_646035 prefixEnd_646035 331726474627485118791445 := by
  unfold tailWord_646035
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562832214533003838971559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15708554809688669225981039 23562832214533003838971559)
  ·
    refine ⟨35344248321799505758457339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23562832214533003838971559 35344248321799505758457339)
    ·
      refine ⟨53016372482699258637686009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35344248321799505758457339 53016372482699258637686009)
      ·
        refine ⟨39762279362024443978264507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53016372482699258637686009 39762279362024443978264507)
        ·
          refine ⟨59643419043036665967396761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39762279362024443978264507 59643419043036665967396761)
          ·
            refine ⟨44732564282277499475547571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59643419043036665967396761 44732564282277499475547571)
            ·
              refine ⟨67098846423416249213321357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44732564282277499475547571 67098846423416249213321357)
              ·
                refine ⟨25162067408781093454995509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67098846423416249213321357 25162067408781093454995509)
                ·
                  refine ⟨2358943819573227511405829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25162067408781093454995509 2358943819573227511405829)
                  ·
                    refine ⟨442301966169980158388593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358943819573227511405829 442301966169980158388593)
                    ·
                      refine ⟨331726474627485118791445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442301966169980158388593 331726474627485118791445)
                      ·
                        rfl

theorem cell23_646035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4, 2].length) (baseStart_646035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646035 prefixEnd_646035 := by exact prefixLift 646035
  have htrace : WordTrace (prefixWord ++ tailWord_646035) baseStart_646035 baseEnd_646035 := by
    simpa [prefixWord, tailWord_646035, baseEnd_646035] using wordTrace_append hprefix tailTrace_646035
  have hstable : (prefixWord ++ tailWord_646035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646035).length < 2 ^ (prefixWord ++ tailWord_646035).sum := by decide
  have hdescent : baseEnd_646035 < baseStart_646035 := by decide
  rcases family_descends (prefixWord ++ tailWord_646035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646052 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_646052 : Nat := 118140960795 + 646052 * 2 ^ 59
def prefixEnd_646052 : Nat := 4983230072969 + 3 ^ 40 * 646052 * 2
def baseEnd_646052 : Nat := 331735203798611552278867

theorem tailTrace_646052 : CollatzResearch.WordTrace tailWord_646052 prefixEnd_646052 331735203798611552278867 := by
  unfold tailWord_646052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11781726127735707871170205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15708968170314277161560273 11781726127735707871170205)
  ·
    refine ⟨4418147297900890451688827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11781726127735707871170205 4418147297900890451688827)
    ·
      refine ⟨6627220946851335677533241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4418147297900890451688827 6627220946851335677533241)
      ·
        refine ⟨4970415710138501758149931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6627220946851335677533241 4970415710138501758149931)
        ·
          refine ⟨7455623565207752637224897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970415710138501758149931 7455623565207752637224897)
          ·
            refine ⟨5591717673905814477918673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7455623565207752637224897 5591717673905814477918673)
            ·
              refine ⟨4193788255429360858439005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5591717673905814477918673 4193788255429360858439005)
              ·
                refine ⟨1572670595786010321914627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4193788255429360858439005 1572670595786010321914627)
                ·
                  refine ⟨2359005893679015482871941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572670595786010321914627 2359005893679015482871941)
                  ·
                    refine ⟨442313605064815403038489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359005893679015482871941 442313605064815403038489)
                    ·
                      refine ⟨331735203798611552278867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442313605064815403038489 331735203798611552278867)
                      ·
                        rfl

theorem cell23_646052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_646052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646052 prefixEnd_646052 := by exact prefixLift 646052
  have htrace : WordTrace (prefixWord ++ tailWord_646052) baseStart_646052 baseEnd_646052 := by
    simpa [prefixWord, tailWord_646052, baseEnd_646052] using wordTrace_append hprefix tailTrace_646052
  have hstable : (prefixWord ++ tailWord_646052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646052).length < 2 ^ (prefixWord ++ tailWord_646052).sum := by decide
  have hdescent : baseEnd_646052 < baseStart_646052 := by decide
  rcases family_descends (prefixWord ++ tailWord_646052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646092 : List Nat := [2, 2, 1, 4, 1, 1, 3, 4, 5]
def baseStart_646092 : Nat := 118140960795 + 646092 * 2 ^ 59
def prefixEnd_646092 : Nat := 4983230072969 + 3 ^ 40 * 646092 * 2
def baseEnd_646092 : Nat := 36861749224976821753187

theorem tailTrace_646092 : CollatzResearch.WordTrace tailWord_646092 prefixEnd_646092 36861749224976821753187 := by
  unfold tailWord_646092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782455587663251286898265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15709940783551001715864353 11782455587663251286898265)
  ·
    refine ⟨8836841690747438465173699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11782455587663251286898265 8836841690747438465173699)
    ·
      refine ⟨13255262536121157697760549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8836841690747438465173699 13255262536121157697760549)
      ·
        refine ⟨2485361725522717068330103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13255262536121157697760549 2485361725522717068330103)
        ·
          refine ⟨3728042588284075602495155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485361725522717068330103 3728042588284075602495155)
          ·
            refine ⟨5592063882426113403742733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728042588284075602495155 5592063882426113403742733)
            ·
              refine ⟨2097023955909792526403525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5592063882426113403742733 2097023955909792526403525)
              ·
                refine ⟨393191991733086098700661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2097023955909792526403525 393191991733086098700661)
                ·
                  refine ⟨36861749224976821753187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393191991733086098700661 36861749224976821753187)
                  ·
                    rfl

theorem cell23_646092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_646092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646092 prefixEnd_646092 := by exact prefixLift 646092
  have htrace : WordTrace (prefixWord ++ tailWord_646092) baseStart_646092 baseEnd_646092 := by
    simpa [prefixWord, tailWord_646092, baseEnd_646092] using wordTrace_append hprefix tailTrace_646092
  have hstable : (prefixWord ++ tailWord_646092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646092).length < 2 ^ (prefixWord ++ tailWord_646092).sum := by decide
  have hdescent : baseEnd_646092 < baseStart_646092 := by decide
  rcases family_descends (prefixWord ++ tailWord_646092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646122 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_646122 : Nat := 118140960795 + 646122 * 2 ^ 59
def prefixEnd_646122 : Nat := 4983230072969 + 3 ^ 40 * 646122 * 2
def baseEnd_646122 : Nat := 110590382481475426134515

theorem tailTrace_646122 : CollatzResearch.WordTrace tailWord_646122 prefixEnd_646122 110590382481475426134515 := by
  unfold tailWord_646122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891501341304454424347155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15710670243478545131592413 5891501341304454424347155)
  ·
    refine ⟨8837252011956681636520733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5891501341304454424347155 8837252011956681636520733)
    ·
      refine ⟨3313969504483755613695275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8837252011956681636520733 3313969504483755613695275)
      ·
        refine ⟨4970954256725633420542913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313969504483755613695275 4970954256725633420542913)
        ·
          refine ⟨3728215692544225065407185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4970954256725633420542913 3728215692544225065407185)
          ·
            refine ⟨2796161769408168799055389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3728215692544225065407185 2796161769408168799055389)
            ·
              refine ⟨1048560663528063299645771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2796161769408168799055389 1048560663528063299645771)
              ·
                refine ⟨1572840995292094949468657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048560663528063299645771 1572840995292094949468657)
                ·
                  refine ⟨1179630746469071212101493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1572840995292094949468657 1179630746469071212101493)
                  ·
                    refine ⟨110590382481475426134515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1179630746469071212101493 110590382481475426134515)
                    ·
                      rfl

theorem cell23_646122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_646122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646122 prefixEnd_646122 := by exact prefixLift 646122
  have htrace : WordTrace (prefixWord ++ tailWord_646122) baseStart_646122 baseEnd_646122 := by
    simpa [prefixWord, tailWord_646122, baseEnd_646122] using wordTrace_append hprefix tailTrace_646122
  have hstable : (prefixWord ++ tailWord_646122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646122).length < 2 ^ (prefixWord ++ tailWord_646122).sum := by decide
  have hdescent : baseEnd_646122 < baseStart_646122 := by decide
  rcases family_descends (prefixWord ++ tailWord_646122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646152 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 3, 4]
def baseStart_646152 : Nat := 118140960795 + 646152 * 2 ^ 59
def prefixEnd_646152 : Nat := 4983230072969 + 3 ^ 40 * 646152 * 2
def baseEnd_646152 : Nat := 110595517288020387009469

theorem tailTrace_646152 : CollatzResearch.WordTrace tailWord_646152 prefixEnd_646152 110595517288020387009469 := by
  unfold tailWord_646152
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783549777554566410490355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15711399703406088547320473 11783549777554566410490355)
  ·
    refine ⟨17675324666331849615735533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11783549777554566410490355 17675324666331849615735533)
    ·
      refine ⟨6628246749874443605900825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17675324666331849615735533 6628246749874443605900825)
      ·
        refine ⟨4971185062405832704425619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6628246749874443605900825 4971185062405832704425619)
        ·
          refine ⟨7456777593608749056638429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971185062405832704425619 7456777593608749056638429)
          ·
            refine ⟨2796291597603280896239411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7456777593608749056638429 2796291597603280896239411)
            ·
              refine ⟨4194437396404921344359117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796291597603280896239411 4194437396404921344359117)
              ·
                refine ⟨1572914023651845504134669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4194437396404921344359117 1572914023651845504134669)
                ·
                  refine ⟨589842758869442064050501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1572914023651845504134669 589842758869442064050501)
                  ·
                    refine ⟨110595517288020387009469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 589842758869442064050501 110595517288020387009469)
                    ·
                      rfl

theorem cell23_646152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_646152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646152 prefixEnd_646152 := by exact prefixLift 646152
  have htrace : WordTrace (prefixWord ++ tailWord_646152) baseStart_646152 baseEnd_646152 := by
    simpa [prefixWord, tailWord_646152, baseEnd_646152] using wordTrace_append hprefix tailTrace_646152
  have hstable : (prefixWord ++ tailWord_646152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646152).length < 2 ^ (prefixWord ++ tailWord_646152).sum := by decide
  have hdescent : baseEnd_646152 < baseStart_646152 := by decide
  rcases family_descends (prefixWord ++ tailWord_646152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646195 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 5, 5]
def baseStart_646195 : Nat := 118140960795 + 646195 * 2 ^ 59
def prefixEnd_646195 : Nat := 4983230072969 + 3 ^ 40 * 646195 * 2
def baseEnd_646195 : Nat := 110602877177401497596903

theorem tailTrace_646195 : CollatzResearch.WordTrace tailWord_646195 prefixEnd_646195 110602877177401497596903 := by
  unfold tailWord_646195
  simp only [CollatzResearch.WordTrace]
  refine ⟨23568667893953351164796039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15712445262635567443197359 23568667893953351164796039)
  ·
    refine ⟨35353001840930026747194059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23568667893953351164796039 35353001840930026747194059)
    ·
      refine ⟨53029502761395040120791089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35353001840930026747194059 53029502761395040120791089)
      ·
        refine ⟨39772127071046280090593317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53029502761395040120791089 39772127071046280090593317)
        ·
          refine ⟨7457273825821177516986247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39772127071046280090593317 7457273825821177516986247)
          ·
            refine ⟨11185910738731766275479371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457273825821177516986247 11185910738731766275479371)
            ·
              refine ⟨16778866108097649413219057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11185910738731766275479371 16778866108097649413219057)
              ·
                refine ⟨12584149581073237059914293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16778866108097649413219057 12584149581073237059914293)
                ·
                  refine ⟨1179764023225615974366965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12584149581073237059914293 1179764023225615974366965)
                  ·
                    refine ⟨110602877177401497596903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1179764023225615974366965 110602877177401497596903)
                    ·
                      rfl

theorem cell23_646195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 5].length) (baseStart_646195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646195 prefixEnd_646195 := by exact prefixLift 646195
  have htrace : WordTrace (prefixWord ++ tailWord_646195) baseStart_646195 baseEnd_646195 := by
    simpa [prefixWord, tailWord_646195, baseEnd_646195] using wordTrace_append hprefix tailTrace_646195
  have hstable : (prefixWord ++ tailWord_646195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646195).length < 2 ^ (prefixWord ++ tailWord_646195).sum := by decide
  have hdescent : baseEnd_646195 < baseStart_646195 := by decide
  rcases family_descends (prefixWord ++ tailWord_646195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646196 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_646196 : Nat := 118140960795 + 646196 * 2 ^ 59
def prefixEnd_646196 : Nat := 4983230072969 + 3 ^ 40 * 646196 * 2
def baseEnd_646196 : Nat := 331809145012858988878205

theorem tailTrace_646196 : CollatzResearch.WordTrace tailWord_646196 prefixEnd_646196 331809145012858988878205 := by
  unfold tailWord_646196
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784352183474864167791221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15712469577966485557054961 11784352183474864167791221)
  ·
    refine ⟨1104783017200768515730427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11784352183474864167791221 1104783017200768515730427)
    ·
      refine ⟨1657174525801152773595641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1104783017200768515730427 1657174525801152773595641)
      ·
        refine ⟨1242880894350864580196731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1657174525801152773595641 1242880894350864580196731)
        ·
          refine ⟨1864321341526296870295097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242880894350864580196731 1864321341526296870295097)
          ·
            refine ⟨1398241006144722652721323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1864321341526296870295097 1398241006144722652721323)
            ·
              refine ⟨2097361509217083979081985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398241006144722652721323 2097361509217083979081985)
              ·
                refine ⟨1573021131912812984311489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097361509217083979081985 1573021131912812984311489)
                ·
                  refine ⟨1179765848934609738233617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1573021131912812984311489 1179765848934609738233617)
                  ·
                    refine ⟨884824386700957303675213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1179765848934609738233617 884824386700957303675213)
                    ·
                      refine ⟨331809145012858988878205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 884824386700957303675213 331809145012858988878205)
                      ·
                        rfl

theorem cell23_646196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_646196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646196 prefixEnd_646196 := by exact prefixLift 646196
  have htrace : WordTrace (prefixWord ++ tailWord_646196) baseStart_646196 baseEnd_646196 := by
    simpa [prefixWord, tailWord_646196, baseEnd_646196] using wordTrace_append hprefix tailTrace_646196
  have hstable : (prefixWord ++ tailWord_646196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646196).length < 2 ^ (prefixWord ++ tailWord_646196).sum := by decide
  have hdescent : baseEnd_646196 < baseStart_646196 := by decide
  rcases family_descends (prefixWord ++ tailWord_646196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646232 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_646232 : Nat := 118140960795 + 646232 * 2 ^ 59
def prefixEnd_646232 : Nat := 4983230072969 + 3 ^ 40 * 646232 * 2
def baseEnd_646232 : Nat := 331827630316420848028039

theorem tailTrace_646232 : CollatzResearch.WordTrace tailWord_646232 prefixEnd_646232 331827630316420848028039 := by
  unfold tailWord_646232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785008697409653241946475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15713344929879537655928633 11785008697409653241946475)
  ·
    refine ⟨17677513046114479862919713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11785008697409653241946475 17677513046114479862919713)
    ·
      refine ⟨13258134784585859897189785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17677513046114479862919713 13258134784585859897189785)
      ·
        refine ⟨9943601088439394922892339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13258134784585859897189785 9943601088439394922892339)
        ·
          refine ⟨14915401632659092384338509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9943601088439394922892339 14915401632659092384338509)
          ·
            refine ⟨5593275612247159644126941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14915401632659092384338509 5593275612247159644126941)
            ·
              refine ⟨2097478354592684866547603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5593275612247159644126941 2097478354592684866547603)
              ·
                refine ⟨3146217531889027299821405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097478354592684866547603 3146217531889027299821405)
                ·
                  refine ⟨1179831574458385237433027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3146217531889027299821405 1179831574458385237433027)
                  ·
                    refine ⟨1769747361687577856149541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1179831574458385237433027 1769747361687577856149541)
                    ·
                      refine ⟨331827630316420848028039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1769747361687577856149541 331827630316420848028039)
                      ·
                        rfl

theorem cell23_646232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_646232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646232 prefixEnd_646232 := by exact prefixLift 646232
  have htrace : WordTrace (prefixWord ++ tailWord_646232) baseStart_646232 baseEnd_646232 := by
    simpa [prefixWord, tailWord_646232, baseEnd_646232] using wordTrace_append hprefix tailTrace_646232
  have hstable : (prefixWord ++ tailWord_646232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646232).length < 2 ^ (prefixWord ++ tailWord_646232).sum := by decide
  have hdescent : baseEnd_646232 < baseStart_646232 := by decide
  rcases family_descends (prefixWord ++ tailWord_646232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646236 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_646236 : Nat := 118140960795 + 646236 * 2 ^ 59
def prefixEnd_646236 : Nat := 4983230072969 + 3 ^ 40 * 646236 * 2
def baseEnd_646236 : Nat := 331829684239038832378021

theorem tailTrace_646236 : CollatzResearch.WordTrace tailWord_646236 prefixEnd_646236 331829684239038832378021 := by
  unfold tailWord_646236
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785081643402407583519281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15713442191203210111359041 11785081643402407583519281)
  ·
    refine ⟨8838811232551805687639461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11785081643402407583519281 8838811232551805687639461)
    ·
      refine ⟨1657277106103463566432399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8838811232551805687639461 1657277106103463566432399)
      ·
        refine ⟨2485915659155195349648599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657277106103463566432399 2485915659155195349648599)
        ·
          refine ⟨3728873488732793024472899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485915659155195349648599 3728873488732793024472899)
          ·
            refine ⟨5593310233099189536709349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728873488732793024472899 5593310233099189536709349)
            ·
              refine ⟨1048745668706098038133003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5593310233099189536709349 1048745668706098038133003)
              ·
                refine ⟨1573118503059147057199505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048745668706098038133003 1573118503059147057199505)
                ·
                  refine ⟨1179838877294360292899629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1573118503059147057199505 1179838877294360292899629)
                  ·
                    refine ⟨442439578985385109837361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1179838877294360292899629 442439578985385109837361)
                    ·
                      refine ⟨331829684239038832378021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442439578985385109837361 331829684239038832378021)
                      ·
                        rfl

theorem cell23_646236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_646236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646236 prefixEnd_646236 := by exact prefixLift 646236
  have htrace : WordTrace (prefixWord ++ tailWord_646236) baseStart_646236 baseEnd_646236 := by
    simpa [prefixWord, tailWord_646236, baseEnd_646236] using wordTrace_append hprefix tailTrace_646236
  have hstable : (prefixWord ++ tailWord_646236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646236).length < 2 ^ (prefixWord ++ tailWord_646236).sum := by decide
  have hdescent : baseEnd_646236 < baseStart_646236 := by decide
  rcases family_descends (prefixWord ++ tailWord_646236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646300 : List Nat := [2, 2, 3, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_646300 : Nat := 118140960795 + 646300 * 2 ^ 59
def prefixEnd_646300 : Nat := 4983230072969 + 3 ^ 40 * 646300 * 2
def baseEnd_646300 : Nat := 331862547000926581977727

theorem tailTrace_646300 : CollatzResearch.WordTrace tailWord_646300 prefixEnd_646300 331862547000926581977727 := by
  unfold tailWord_646300
  simp only [CollatzResearch.WordTrace]
  refine ⟨11786248779286477048684177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15714998372381969398245569 11786248779286477048684177)
  ·
    refine ⟨8839686584464857786513133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11786248779286477048684177 8839686584464857786513133)
    ·
      refine ⟨3314882469174321669942425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8839686584464857786513133 3314882469174321669942425)
      ·
        refine ⟨2486161851880741252456819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314882469174321669942425 2486161851880741252456819)
        ·
          refine ⟨3729242777821111878685229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486161851880741252456819 3729242777821111878685229)
          ·
            refine ⟨1398466041682916954506961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3729242777821111878685229 1398466041682916954506961)
            ·
              refine ⟨1048849531262187715880221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1398466041682916954506961 1048849531262187715880221)
              ·
                refine ⟨393318574223320393455083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1048849531262187715880221 393318574223320393455083)
                ·
                  refine ⟨589977861334980590182625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393318574223320393455083 589977861334980590182625)
                  ·
                    refine ⟨442483396001235442636969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 589977861334980590182625 442483396001235442636969)
                    ·
                      refine ⟨331862547000926581977727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442483396001235442636969 331862547000926581977727)
                      ·
                        rfl

theorem cell23_646300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_646300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646300 prefixEnd_646300 := by exact prefixLift 646300
  have htrace : WordTrace (prefixWord ++ tailWord_646300) baseStart_646300 baseEnd_646300 := by
    simpa [prefixWord, tailWord_646300, baseEnd_646300] using wordTrace_append hprefix tailTrace_646300
  have hstable : (prefixWord ++ tailWord_646300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646300).length < 2 ^ (prefixWord ++ tailWord_646300).sum := by decide
  have hdescent : baseEnd_646300 < baseStart_646300 := by decide
  rcases family_descends (prefixWord ++ tailWord_646300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646315 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 12]
def baseStart_646315 : Nat := 118140960795 + 646315 * 2 ^ 59
def prefixEnd_646315 : Nat := 4983230072969 + 3 ^ 40 * 646315 * 2
def baseEnd_646315 : Nat := 110623416403581341096719

theorem tailTrace_646315 : CollatzResearch.WordTrace tailWord_646315 prefixEnd_646315 110623416403581341096719 := by
  unfold tailWord_646315
  simp only [CollatzResearch.WordTrace]
  refine ⟨23573044653518611659164399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15715363102345741106109599 23573044653518611659164399)
  ·
    refine ⟨35359566980277917488746599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23573044653518611659164399 35359566980277917488746599)
    ·
      refine ⟨53039350470416876233119899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35359566980277917488746599 53039350470416876233119899)
      ·
        refine ⟨79559025705625314349679849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53039350470416876233119899 79559025705625314349679849)
        ·
          refine ⟨59669269279218985762259887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79559025705625314349679849 59669269279218985762259887)
          ·
            refine ⟨89503903918828478643389831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59669269279218985762259887 89503903918828478643389831)
            ·
              refine ⟨134255855878242717965084747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89503903918828478643389831 134255855878242717965084747)
              ·
                refine ⟨201383783817364076947627121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134255855878242717965084747 201383783817364076947627121)
                ·
                  refine ⟨151037837863023057710720341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201383783817364076947627121 151037837863023057710720341)
                  ·
                    refine ⟨110623416403581341096719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 151037837863023057710720341 110623416403581341096719)
                    ·
                      rfl

theorem cell23_646315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_646315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646315 prefixEnd_646315 := by exact prefixLift 646315
  have htrace : WordTrace (prefixWord ++ tailWord_646315) baseStart_646315 baseEnd_646315 := by
    simpa [prefixWord, tailWord_646315, baseEnd_646315] using wordTrace_append hprefix tailTrace_646315
  have hstable : (prefixWord ++ tailWord_646315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646315).length < 2 ^ (prefixWord ++ tailWord_646315).sum := by decide
  have hdescent : baseEnd_646315 < baseStart_646315 := by decide
  rcases family_descends (prefixWord ++ tailWord_646315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646339 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 1, 4, 2]
def baseStart_646339 : Nat := 118140960795 + 646339 * 2 ^ 59
def prefixEnd_646339 : Nat := 4983230072969 + 3 ^ 40 * 646339 * 2
def baseEnd_646339 : Nat := 331882572746451929390047

theorem tailTrace_646339 : CollatzResearch.WordTrace tailWord_646339 prefixEnd_646339 331882572746451929390047 := by
  unfold tailWord_646339
  simp only [CollatzResearch.WordTrace]
  refine ⟨23573920005431663758038071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15715946670287775838692047 23573920005431663758038071)
  ·
    refine ⟨35360880008147495637057107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23573920005431663758038071 35360880008147495637057107)
    ·
      refine ⟨53041320012221243455585661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35360880008147495637057107 53041320012221243455585661)
      ·
        refine ⟨19890495004582966295844623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53041320012221243455585661 19890495004582966295844623)
        ·
          refine ⟨29835742506874449443766935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19890495004582966295844623 29835742506874449443766935)
          ·
            refine ⟨44753613760311674165650403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29835742506874449443766935 44753613760311674165650403)
            ·
              refine ⟨67130420640467511248475605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44753613760311674165650403 67130420640467511248475605)
              ·
                refine ⟨1573369233760957294886147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67130420640467511248475605 1573369233760957294886147)
                ·
                  refine ⟨2360053850641435942329221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573369233760957294886147 2360053850641435942329221)
                  ·
                    refine ⟨442510096995269239186729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360053850641435942329221 442510096995269239186729)
                    ·
                      refine ⟨331882572746451929390047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442510096995269239186729 331882572746451929390047)
                      ·
                        rfl

theorem cell23_646339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_646339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646339 prefixEnd_646339 := by exact prefixLift 646339
  have htrace : WordTrace (prefixWord ++ tailWord_646339) baseStart_646339 baseEnd_646339 := by
    simpa [prefixWord, tailWord_646339, baseEnd_646339] using wordTrace_append hprefix tailTrace_646339
  have hstable : (prefixWord ++ tailWord_646339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646339).length < 2 ^ (prefixWord ++ tailWord_646339).sum := by decide
  have hdescent : baseEnd_646339 < baseStart_646339 := by decide
  rcases family_descends (prefixWord ++ tailWord_646339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646379 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 7]
def baseStart_646379 : Nat := 118140960795 + 646379 * 2 ^ 59
def prefixEnd_646379 : Nat := 4983230072969 + 3 ^ 40 * 646379 * 2
def baseEnd_646379 : Nat := 36878123552514641432207

theorem tailTrace_646379 : CollatzResearch.WordTrace tailWord_646379 prefixEnd_646379 36878123552514641432207 := by
  unfold tailWord_646379
  simp only [CollatzResearch.WordTrace]
  refine ⟨23575378925286750589494191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15716919283524500392996127 23575378925286750589494191)
  ·
    refine ⟨35363068387930125884241287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23575378925286750589494191 35363068387930125884241287)
    ·
      refine ⟨53044602581895188826361931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35363068387930125884241287 53044602581895188826361931)
      ·
        refine ⟨79566903872842783239542897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53044602581895188826361931 79566903872842783239542897)
        ·
          refine ⟨59675177904632087429657173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79566903872842783239542897 59675177904632087429657173)
          ·
            refine ⟨699318491069907274566295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 59675177904632087429657173 699318491069907274566295)
            ·
              refine ⟨1048977736604860911849443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699318491069907274566295 1048977736604860911849443)
              ·
                refine ⟨1573466604907291367774165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048977736604860911849443 1573466604907291367774165)
                ·
                  refine ⟨36878123552514641432207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1573466604907291367774165 36878123552514641432207)
                  ·
                    rfl

theorem cell23_646379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 7].length) (baseStart_646379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646379 prefixEnd_646379 := by exact prefixLift 646379
  have htrace : WordTrace (prefixWord ++ tailWord_646379) baseStart_646379 baseEnd_646379 := by
    simpa [prefixWord, tailWord_646379, baseEnd_646379] using wordTrace_append hprefix tailTrace_646379
  have hstable : (prefixWord ++ tailWord_646379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646379).length < 2 ^ (prefixWord ++ tailWord_646379).sum := by decide
  have hdescent : baseEnd_646379 < baseStart_646379 := by decide
  rcases family_descends (prefixWord ++ tailWord_646379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646409 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 2, 5]
def baseStart_646409 : Nat := 118140960795 + 646409 * 2 ^ 59
def prefixEnd_646409 : Nat := 4983230072969 + 3 ^ 40 * 646409 * 2
def baseEnd_646409 : Nat := 110639505464088885171575

theorem tailTrace_646409 : CollatzResearch.WordTrace tailWord_646409 prefixEnd_646409 110639505464088885171575 := by
  unfold tailWord_646409
  simp only [CollatzResearch.WordTrace]
  refine ⟨23576473115178065713086281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15717648743452043808724187 23576473115178065713086281)
  ·
    refine ⟨17682354836383549284814711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23576473115178065713086281 17682354836383549284814711)
    ·
      refine ⟨26523532254575323927222067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17682354836383549284814711 26523532254575323927222067)
      ·
        refine ⟨39785298381862985890833101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26523532254575323927222067 39785298381862985890833101)
        ·
          refine ⟨14919486893198619709062413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39785298381862985890833101 14919486893198619709062413)
          ·
            refine ⟨5594807584949482390898405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14919486893198619709062413 5594807584949482390898405)
            ·
              refine ⟨1049026422178027948293451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5594807584949482390898405 1049026422178027948293451)
              ·
                refine ⟨1573539633267041922440177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049026422178027948293451 1573539633267041922440177)
                ·
                  refine ⟨1180154724950281441830133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1573539633267041922440177 1180154724950281441830133)
                  ·
                    refine ⟨110639505464088885171575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1180154724950281441830133 110639505464088885171575)
                    ·
                      rfl

theorem cell23_646409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_646409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646409 prefixEnd_646409 := by exact prefixLift 646409
  have htrace : WordTrace (prefixWord ++ tailWord_646409) baseStart_646409 baseEnd_646409 := by
    simpa [prefixWord, tailWord_646409, baseEnd_646409] using wordTrace_append hprefix tailTrace_646409
  have hstable : (prefixWord ++ tailWord_646409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646409).length < 2 ^ (prefixWord ++ tailWord_646409).sum := by decide
  have hdescent : baseEnd_646409 < baseStart_646409 := by decide
  rcases family_descends (prefixWord ++ tailWord_646409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646430 : List Nat := [4, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_646430 : Nat := 118140960795 + 646430 * 2 ^ 59
def prefixEnd_646430 : Nat := 4983230072969 + 3 ^ 40 * 646430 * 2
def baseEnd_646430 : Nat := 36881033276223452594681

theorem tailTrace_646430 : CollatzResearch.WordTrace tailWord_646430 prefixEnd_646430 36881033276223452594681 := by
  unfold tailWord_646430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947154881012748287450093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15718159365401324199733829 2947154881012748287450093)
  ·
    refine ⟨1105183080379780607793785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2947154881012748287450093 1105183080379780607793785)
    ·
      refine ⟨828887310284835455845339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1105183080379780607793785 828887310284835455845339)
      ·
        refine ⟨1243330965427253183768009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828887310284835455845339 1243330965427253183768009)
        ·
          refine ⟨932498224070439887826007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1243330965427253183768009 932498224070439887826007)
          ·
            refine ⟨1398747336105659831739011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932498224070439887826007 1398747336105659831739011)
            ·
              refine ⟨2098121004158489747608517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398747336105659831739011 2098121004158489747608517)
              ·
                refine ⟨393397688279716827676597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2098121004158489747608517 393397688279716827676597)
                ·
                  refine ⟨36881033276223452594681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393397688279716827676597 36881033276223452594681)
                  ·
                    rfl

theorem cell23_646430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_646430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646430 prefixEnd_646430 := by exact prefixLift 646430
  have htrace : WordTrace (prefixWord ++ tailWord_646430) baseStart_646430 baseEnd_646430 := by
    simpa [prefixWord, tailWord_646430, baseEnd_646430] using wordTrace_append hprefix tailTrace_646430
  have hstable : (prefixWord ++ tailWord_646430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646430).length < 2 ^ (prefixWord ++ tailWord_646430).sum := by decide
  have hdescent : baseEnd_646430 < baseStart_646430 := by decide
  rcases family_descends (prefixWord ++ tailWord_646430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646503 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 6]
def baseStart_646503 : Nat := 118140960795 + 646503 * 2 ^ 59
def prefixEnd_646503 : Nat := 4983230072969 + 3 ^ 40 * 646503 * 2
def baseEnd_646503 : Nat := 36885198174865476415477

theorem tailTrace_646503 : CollatzResearch.WordTrace tailWord_646503 prefixEnd_646503 36885198174865476415477 := by
  unfold tailWord_646503
  simp only [CollatzResearch.WordTrace]
  refine ⟨23579901576837519767008163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15719934384558346511338775 23579901576837519767008163)
  ·
    refine ⟨35369852365256279650512245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23579901576837519767008163 35369852365256279650512245)
    ·
      refine ⟨3315923659242776217235523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35369852365256279650512245 3315923659242776217235523)
      ·
        refine ⟨4973885488864164325853285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315923659242776217235523 4973885488864164325853285)
        ·
          refine ⟨932603529162030811097491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4973885488864164325853285 932603529162030811097491)
          ·
            refine ⟨1398905293743046216646237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932603529162030811097491 1398905293743046216646237)
            ·
              refine ⟨524589485153642331242339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1398905293743046216646237 524589485153642331242339)
              ·
                refine ⟨786884227730463496863509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524589485153642331242339 786884227730463496863509)
                ·
                  refine ⟨36885198174865476415477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 786884227730463496863509 36885198174865476415477)
                  ·
                    rfl

theorem cell23_646503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 6].length) (baseStart_646503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646503 prefixEnd_646503 := by exact prefixLift 646503
  have htrace : WordTrace (prefixWord ++ tailWord_646503) baseStart_646503 baseEnd_646503 := by
    simpa [prefixWord, tailWord_646503, baseEnd_646503] using wordTrace_append hprefix tailTrace_646503
  have hstable : (prefixWord ++ tailWord_646503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646503).length < 2 ^ (prefixWord ++ tailWord_646503).sum := by decide
  have hdescent : baseEnd_646503 < baseStart_646503 := by decide
  rcases family_descends (prefixWord ++ tailWord_646503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646549 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_646549 : Nat := 118140960795 + 646549 * 2 ^ 59
def prefixEnd_646549 : Nat := 4983230072969 + 3 ^ 40 * 646549 * 2
def baseEnd_646549 : Nat := 331990403683896107764081

theorem tailTrace_646549 : CollatzResearch.WordTrace tailWord_646549 prefixEnd_646549 331990403683896107764081 := by
  unfold tailWord_646549
  simp only [CollatzResearch.WordTrace]
  refine ⟨23581579334670869623182701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15721052889780579748788467 23581579334670869623182701)
  ·
    refine ⟨8843092250501576108693513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23581579334670869623182701 8843092250501576108693513)
    ·
      refine ⟨6632319187876182081520135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8843092250501576108693513 6632319187876182081520135)
      ·
        refine ⟨9948478781814273122280203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6632319187876182081520135 9948478781814273122280203)
        ·
          refine ⟨14922718172721409683420305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9948478781814273122280203 14922718172721409683420305)
          ·
            refine ⟨11192038629541057262565229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14922718172721409683420305 11192038629541057262565229)
            ·
              refine ⟨4197014486077896473461961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11192038629541057262565229 4197014486077896473461961)
              ·
                refine ⟨3147760864558422355096471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4197014486077896473461961 3147760864558422355096471)
                ·
                  refine ⟨4721641296837633532644707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147760864558422355096471 4721641296837633532644707)
                  ·
                    refine ⟨7082461945256450298967061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4721641296837633532644707 7082461945256450298967061)
                    ·
                      refine ⟨331990403683896107764081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7082461945256450298967061 331990403683896107764081)
                      ·
                        rfl

theorem cell23_646549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_646549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646549 prefixEnd_646549 := by exact prefixLift 646549
  have htrace : WordTrace (prefixWord ++ tailWord_646549) baseStart_646549 baseEnd_646549 := by
    simpa [prefixWord, tailWord_646549, baseEnd_646549] using wordTrace_append hprefix tailTrace_646549
  have hstable : (prefixWord ++ tailWord_646549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646549).length < 2 ^ (prefixWord ++ tailWord_646549).sum := by decide
  have hdescent : baseEnd_646549 < baseStart_646549 := by decide
  rcases family_descends (prefixWord ++ tailWord_646549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646559 : List Nat := [1, 1, 2, 5, 1, 2, 1, 10]
def baseStart_646559 : Nat := 118140960795 + 646559 * 2 ^ 59
def prefixEnd_646559 : Nat := 4983230072969 + 3 ^ 40 * 646559 * 2
def baseEnd_646559 : Nat := 12296131055201521060705

theorem tailTrace_646559 : CollatzResearch.WordTrace tailWord_646559 prefixEnd_646559 12296131055201521060705 := by
  unfold tailWord_646559
  simp only [CollatzResearch.WordTrace]
  refine ⟨23581944064634641331046731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15721296043089760887364487 23581944064634641331046731)
  ·
    refine ⟨35372916096951961996570097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23581944064634641331046731 35372916096951961996570097)
    ·
      refine ⟨26529687072713971497427573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35372916096951961996570097 26529687072713971497427573)
      ·
        refine ⟨2487158163066934827883835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26529687072713971497427573 2487158163066934827883835)
        ·
          refine ⟨3730737244600402241825753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487158163066934827883835 3730737244600402241825753)
          ·
            refine ⟨2798052933450301681369315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3730737244600402241825753 2798052933450301681369315)
            ·
              refine ⟨4197079400175452522053973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798052933450301681369315 4197079400175452522053973)
              ·
                refine ⟨12296131055201521060705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4197079400175452522053973 12296131055201521060705)
                ·
                  rfl

theorem cell23_646559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 10].length) (baseStart_646559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646559 prefixEnd_646559 := by exact prefixLift 646559
  have htrace : WordTrace (prefixWord ++ tailWord_646559) baseStart_646559 baseEnd_646559 := by
    simpa [prefixWord, tailWord_646559, baseEnd_646559] using wordTrace_append hprefix tailTrace_646559
  have hstable : (prefixWord ++ tailWord_646559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646559).length < 2 ^ (prefixWord ++ tailWord_646559).sum := by decide
  have hdescent : baseEnd_646559 < baseStart_646559 := by decide
  rcases family_descends (prefixWord ++ tailWord_646559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646603 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 3]
def baseStart_646603 : Nat := 118140960795 + 646603 * 2 ^ 59
def prefixEnd_646603 : Nat := 4983230072969 + 3 ^ 40 * 646603 * 2
def baseEnd_646603 : Nat := 332018131639238896488833

theorem tailTrace_646603 : CollatzResearch.WordTrace tailWord_646603 prefixEnd_646603 332018131639238896488833 := by
  unfold tailWord_646603
  simp only [CollatzResearch.WordTrace]
  refine ⟨23583548876475236845648463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15722365917650157897098975 23583548876475236845648463)
  ·
    refine ⟨35375323314712855268472695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23583548876475236845648463 35375323314712855268472695)
    ·
      refine ⟨53062984972069282902709043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35375323314712855268472695 53062984972069282902709043)
      ·
        refine ⟨79594477458103924354063565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53062984972069282902709043 79594477458103924354063565)
        ·
          refine ⟨29847929046788971632773837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79594477458103924354063565 29847929046788971632773837)
          ·
            refine ⟨11192973392545864362290189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29847929046788971632773837 11192973392545864362290189)
            ·
              refine ⟨4197365022204699135858821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11192973392545864362290189 4197365022204699135858821)
              ·
                refine ⟨787005941663381087973529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4197365022204699135858821 787005941663381087973529)
                ·
                  refine ⟨590254456247535815980147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 787005941663381087973529 590254456247535815980147)
                  ·
                    refine ⟨885381684371303723970221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 590254456247535815980147 885381684371303723970221)
                    ·
                      refine ⟨332018131639238896488833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 885381684371303723970221 332018131639238896488833)
                      ·
                        rfl

theorem cell23_646603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 3].length) (baseStart_646603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646603 prefixEnd_646603 := by exact prefixLift 646603
  have htrace : WordTrace (prefixWord ++ tailWord_646603) baseStart_646603 baseEnd_646603 := by
    simpa [prefixWord, tailWord_646603, baseEnd_646603] using wordTrace_append hprefix tailTrace_646603
  have hstable : (prefixWord ++ tailWord_646603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646603).length < 2 ^ (prefixWord ++ tailWord_646603).sum := by decide
  have hdescent : baseEnd_646603 < baseStart_646603 := by decide
  rcases family_descends (prefixWord ++ tailWord_646603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646604 : List Nat := [2, 2, 1, 4, 2, 1, 4, 2, 1, 2, 2]
def baseStart_646604 : Nat := 118140960795 + 646604 * 2 ^ 59
def prefixEnd_646604 : Nat := 4983230072969 + 3 ^ 40 * 646604 * 2
def baseEnd_646604 : Nat := 332018645119893392576329

theorem tailTrace_646604 : CollatzResearch.WordTrace tailWord_646604 prefixEnd_646604 332018645119893392576329 := by
  unfold tailWord_646604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11791792674735807008217433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15722390232981076010956577 11791792674735807008217433)
  ·
    refine ⟨8843844506051855256163075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11791792674735807008217433 8843844506051855256163075)
    ·
      refine ⟨13265766759077782884244613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8843844506051855256163075 13265766759077782884244613)
      ·
        refine ⟨2487331267327084290795865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13265766759077782884244613 2487331267327084290795865)
        ·
          refine ⟨1865498450495313218096899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2487331267327084290795865 1865498450495313218096899)
          ·
            refine ⟨2798247675742969827145349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865498450495313218096899 2798247675742969827145349)
            ·
              refine ⟨524671439201806842589753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2798247675742969827145349 524671439201806842589753)
              ·
                refine ⟨393503579401355131942315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524671439201806842589753 393503579401355131942315)
                ·
                  refine ⟨590255369102032697913473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393503579401355131942315 590255369102032697913473)
                  ·
                    refine ⟨442691526826524523435105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 590255369102032697913473 442691526826524523435105)
                    ·
                      refine ⟨332018645119893392576329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442691526826524523435105 332018645119893392576329)
                      ·
                        rfl

theorem cell23_646604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_646604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646604 prefixEnd_646604 := by exact prefixLift 646604
  have htrace : WordTrace (prefixWord ++ tailWord_646604) baseStart_646604 baseEnd_646604 := by
    simpa [prefixWord, tailWord_646604, baseEnd_646604] using wordTrace_append hprefix tailTrace_646604
  have hstable : (prefixWord ++ tailWord_646604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646604).length < 2 ^ (prefixWord ++ tailWord_646604).sum := by decide
  have hdescent : baseEnd_646604 < baseStart_646604 := by decide
  rcases family_descends (prefixWord ++ tailWord_646604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646613 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_646613 : Nat := 118140960795 + 646613 * 2 ^ 59
def prefixEnd_646613 : Nat := 4983230072969 + 3 ^ 40 * 646613 * 2
def baseEnd_646613 : Nat := 332023266445783857363787

theorem tailTrace_646613 : CollatzResearch.WordTrace tailWord_646613 prefixEnd_646613 332023266445783857363787 := by
  unfold tailWord_646613
  simp only [CollatzResearch.WordTrace]
  refine ⟨23583913606439008553512493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15722609070959339035674995 23583913606439008553512493)
  ·
    refine ⟨8843967602414628207567185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23583913606439008553512493 8843967602414628207567185)
    ·
      refine ⟨6632975701810971155675389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8843967602414628207567185 6632975701810971155675389)
      ·
        refine ⟨2487365888179114183378271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6632975701810971155675389 2487365888179114183378271)
        ·
          refine ⟨3731048832268671275067407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487365888179114183378271 3731048832268671275067407)
          ·
            refine ⟨5596573248403006912601111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731048832268671275067407 5596573248403006912601111)
            ·
              refine ⟨8394859872604510368901667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5596573248403006912601111 8394859872604510368901667)
              ·
                refine ⟨12592289808906765553352501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8394859872604510368901667 12592289808906765553352501)
                ·
                  refine ⟨1180527169585009270626797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12592289808906765553352501 1180527169585009270626797)
                  ·
                    refine ⟨442697688594378476485049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180527169585009270626797 442697688594378476485049)
                    ·
                      refine ⟨332023266445783857363787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442697688594378476485049 332023266445783857363787)
                      ·
                        rfl

theorem cell23_646613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_646613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646613 prefixEnd_646613 := by exact prefixLift 646613
  have htrace : WordTrace (prefixWord ++ tailWord_646613) baseStart_646613 baseEnd_646613 := by
    simpa [prefixWord, tailWord_646613, baseEnd_646613] using wordTrace_append hprefix tailTrace_646613
  have hstable : (prefixWord ++ tailWord_646613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646613).length < 2 ^ (prefixWord ++ tailWord_646613).sum := by decide
  have hdescent : baseEnd_646613 < baseStart_646613 := by decide
  rcases family_descends (prefixWord ++ tailWord_646613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646649 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 11]
def baseStart_646649 : Nat := 118140960795 + 646649 * 2 ^ 59
def prefixEnd_646649 : Nat := 4983230072969 + 3 ^ 40 * 646649 * 2
def baseEnd_646649 : Nat := 36893527972149524057069

theorem tailTrace_646649 : CollatzResearch.WordTrace tailWord_646649 prefixEnd_646649 36893527972149524057069 := by
  unfold tailWord_646649
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585226634308586701823001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15723484422872391134548667 23585226634308586701823001)
  ·
    refine ⟨17688919975731440026367251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23585226634308586701823001 17688919975731440026367251)
    ·
      refine ⟨26533379963597160039550877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17688919975731440026367251 26533379963597160039550877)
      ·
        refine ⟨9950017486348935014831579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26533379963597160039550877 9950017486348935014831579)
        ·
          refine ⟨14925026229523402522247369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9950017486348935014831579 14925026229523402522247369)
          ·
            refine ⟨11193769672142551891685527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14925026229523402522247369 11193769672142551891685527)
            ·
              refine ⟨16790654508213827837528291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11193769672142551891685527 16790654508213827837528291)
              ·
                refine ⟨25185981762320741756292437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16790654508213827837528291 25185981762320741756292437)
                ·
                  refine ⟨36893527972149524057069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 25185981762320741756292437 36893527972149524057069)
                  ·
                    rfl

theorem cell23_646649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_646649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646649 prefixEnd_646649 := by exact prefixLift 646649
  have htrace : WordTrace (prefixWord ++ tailWord_646649) baseStart_646649 baseEnd_646649 := by
    simpa [prefixWord, tailWord_646649, baseEnd_646649] using wordTrace_append hprefix tailTrace_646649
  have hstable : (prefixWord ++ tailWord_646649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646649).length < 2 ^ (prefixWord ++ tailWord_646649).sum := by decide
  have hdescent : baseEnd_646649 < baseStart_646649 := by decide
  rcases family_descends (prefixWord ++ tailWord_646649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646659 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9]
def baseStart_646659 : Nat := 118140960795 + 646659 * 2 ^ 59
def prefixEnd_646659 : Nat := 4983230072969 + 3 ^ 40 * 646659 * 2
def baseEnd_646659 : Nat := 332046886555890677388575

theorem tailTrace_646659 : CollatzResearch.WordTrace tailWord_646659 prefixEnd_646659 332046886555890677388575 := by
  unfold tailWord_646659
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585591364272358409687031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15723727576181572273124687 23585591364272358409687031)
  ·
    refine ⟨35378387046408537614530547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23585591364272358409687031 35378387046408537614530547)
    ·
      refine ⟨53067580569612806421795821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35378387046408537614530547 53067580569612806421795821)
      ·
        refine ⟨19900342713604802408173433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53067580569612806421795821 19900342713604802408173433)
        ·
          refine ⟨14925257035203601806130075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19900342713604802408173433 14925257035203601806130075)
          ·
            refine ⟨22387885552805402709195113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14925257035203601806130075 22387885552805402709195113)
            ·
              refine ⟨16790914164604052031896335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22387885552805402709195113 16790914164604052031896335)
              ·
                refine ⟨25186371246906078047844503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16790914164604052031896335 25186371246906078047844503)
                ·
                  refine ⟨37779556870359117071766755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25186371246906078047844503 37779556870359117071766755)
                  ·
                    refine ⟨56669335305538675607650133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37779556870359117071766755 56669335305538675607650133)
                    ·
                      refine ⟨332046886555890677388575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 56669335305538675607650133 332046886555890677388575)
                      ·
                        rfl

theorem cell23_646659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_646659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646659 prefixEnd_646659 := by exact prefixLift 646659
  have htrace : WordTrace (prefixWord ++ tailWord_646659) baseStart_646659 baseEnd_646659 := by
    simpa [prefixWord, tailWord_646659, baseEnd_646659] using wordTrace_append hprefix tailTrace_646659
  have hstable : (prefixWord ++ tailWord_646659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646659).length < 2 ^ (prefixWord ++ tailWord_646659).sum := by decide
  have hdescent : baseEnd_646659 < baseStart_646659 := by decide
  rcases family_descends (prefixWord ++ tailWord_646659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646666 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 7]
def baseStart_646666 : Nat := 118140960795 + 646666 * 2 ^ 59
def prefixEnd_646666 : Nat := 4983230072969 + 3 ^ 40 * 646666 * 2
def baseEnd_646666 : Nat := 36894497880052461111227

theorem tailTrace_646666 : CollatzResearch.WordTrace tailWord_646666 prefixEnd_646666 36894497880052461111227 := by
  unfold tailWord_646666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896461668811749651297963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15723897783497999070127901 5896461668811749651297963)
  ·
    refine ⟨8844692503217624476946945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5896461668811749651297963 8844692503217624476946945)
    ·
      refine ⟨6633519377413218357710209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8844692503217624476946945 6633519377413218357710209)
      ·
        refine ⟨4975139533059913768282657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6633519377413218357710209 4975139533059913768282657)
        ·
          refine ⟨3731354649794935326211993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4975139533059913768282657 3731354649794935326211993)
          ·
            refine ⟨2798515987346201494658995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3731354649794935326211993 2798515987346201494658995)
            ·
              refine ⟨4197773981019302241988493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798515987346201494658995 4197773981019302241988493)
              ·
                refine ⟨1574165242882238340745685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4197773981019302241988493 1574165242882238340745685)
                ·
                  refine ⟨36894497880052461111227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1574165242882238340745685 36894497880052461111227)
                  ·
                    rfl

theorem cell23_646666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_646666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646666 prefixEnd_646666 := by exact prefixLift 646666
  have htrace : WordTrace (prefixWord ++ tailWord_646666) baseStart_646666 baseEnd_646666 := by
    simpa [prefixWord, tailWord_646666, baseEnd_646666] using wordTrace_append hprefix tailTrace_646666
  have hstable : (prefixWord ++ tailWord_646666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646666).length < 2 ^ (prefixWord ++ tailWord_646666).sum := by decide
  have hdescent : baseEnd_646666 < baseStart_646666 := by decide
  rcases family_descends (prefixWord ++ tailWord_646666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646706 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_646706 : Nat := 118140960795 + 646706 * 2 ^ 59
def prefixEnd_646706 : Nat := 4983230072969 + 3 ^ 40 * 646706 * 2
def baseEnd_646706 : Nat := 332071020146651993500859

theorem tailTrace_646706 : CollatzResearch.WordTrace tailWord_646706 prefixEnd_646706 332071020146651993500859 := by
  unfold tailWord_646706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896826398775521359161993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15724870396734723624431981 5896826398775521359161993)
  ·
    refine ⟨4422619799081641019371495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5896826398775521359161993 4422619799081641019371495)
    ·
      refine ⟨6633929698622461529057243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4422619799081641019371495 6633929698622461529057243)
      ·
        refine ⟨9950894547933692293585865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6633929698622461529057243 9950894547933692293585865)
        ·
          refine ⟨7463170910950269220189399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9950894547933692293585865 7463170910950269220189399)
          ·
            refine ⟨11194756366425403830284099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463170910950269220189399 11194756366425403830284099)
            ·
              refine ⟨16792134549638105745426149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11194756366425403830284099 16792134549638105745426149)
              ·
                refine ⟨3148525228057144827267403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16792134549638105745426149 3148525228057144827267403)
                ·
                  refine ⟨4722787842085717240901105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148525228057144827267403 4722787842085717240901105)
                  ·
                    refine ⟨3542090881564287930675829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4722787842085717240901105 3542090881564287930675829)
                    ·
                      refine ⟨332071020146651993500859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3542090881564287930675829 332071020146651993500859)
                      ·
                        rfl

theorem cell23_646706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_646706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646706 prefixEnd_646706 := by exact prefixLift 646706
  have htrace : WordTrace (prefixWord ++ tailWord_646706) baseStart_646706 baseEnd_646706 := by
    simpa [prefixWord, tailWord_646706, baseEnd_646706] using wordTrace_append hprefix tailTrace_646706
  have hstable : (prefixWord ++ tailWord_646706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646706).length < 2 ^ (prefixWord ++ tailWord_646706).sum := by decide
  have hdescent : baseEnd_646706 < baseStart_646706 := by decide
  rcases family_descends (prefixWord ++ tailWord_646706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646713 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 2, 5]
def baseStart_646713 : Nat := 118140960795 + 646713 * 2 ^ 59
def prefixEnd_646713 : Nat := 4983230072969 + 3 ^ 40 * 646713 * 2
def baseEnd_646713 : Nat := 110691538170411155371109

theorem tailTrace_646713 : CollatzResearch.WordTrace tailWord_646713 prefixEnd_646713 110691538170411155371109 := by
  unfold tailWord_646713
  simp only [CollatzResearch.WordTrace]
  refine ⟨23587560906076725632152793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15725040604051150421435195 23587560906076725632152793)
  ·
    refine ⟨17690670679557544224114595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23587560906076725632152793 17690670679557544224114595)
    ·
      refine ⟨26536006019336316336171893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17690670679557544224114595 26536006019336316336171893)
      ·
        refine ⟨2487750564312779656516115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26536006019336316336171893 2487750564312779656516115)
        ·
          refine ⟨3731625846469169484774173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487750564312779656516115 3731625846469169484774173)
          ·
            refine ⟨1399359692425938556790315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3731625846469169484774173 1399359692425938556790315)
            ·
              refine ⟨2099039538638907835185473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399359692425938556790315 2099039538638907835185473)
              ·
                refine ⟨1574279653979180876389105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099039538638907835185473 1574279653979180876389105)
                ·
                  refine ⟨1180709740484385657291829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1574279653979180876389105 1180709740484385657291829)
                  ·
                    refine ⟨110691538170411155371109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1180709740484385657291829 110691538170411155371109)
                    ·
                      rfl

theorem cell23_646713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_646713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646713 prefixEnd_646713 := by exact prefixLift 646713
  have htrace : WordTrace (prefixWord ++ tailWord_646713) baseStart_646713 baseEnd_646713 := by
    simpa [prefixWord, tailWord_646713, baseEnd_646713] using wordTrace_append hprefix tailTrace_646713
  have hstable : (prefixWord ++ tailWord_646713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646713).length < 2 ^ (prefixWord ++ tailWord_646713).sum := by decide
  have hdescent : baseEnd_646713 < baseStart_646713 := by decide
  rcases family_descends (prefixWord ++ tailWord_646713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646717 : List Nat := [1, 4, 1, 3, 3, 1, 3, 2, 5]
def baseStart_646717 : Nat := 118140960795 + 646717 * 2 ^ 59
def prefixEnd_646717 : Nat := 4983230072969 + 3 ^ 40 * 646717 * 2
def baseEnd_646717 : Nat := 36897407603761272273701

theorem tailTrace_646717 : CollatzResearch.WordTrace tailWord_646717 prefixEnd_646717 36897407603761272273701 := by
  unfold tailWord_646717
  simp only [CollatzResearch.WordTrace]
  refine ⟨23587706798062234315298405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15725137865374822876865603 23587706798062234315298405)
  ·
    refine ⟨4422695024636668934118451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23587706798062234315298405 4422695024636668934118451)
    ·
      refine ⟨6634042536955003401177677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4422695024636668934118451 6634042536955003401177677)
      ·
        refine ⟨2487765951358126275441629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6634042536955003401177677 2487765951358126275441629)
        ·
          refine ⟨932912231759297353290611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2487765951358126275441629 932912231759297353290611)
          ·
            refine ⟨1399368347638946029935917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932912231759297353290611 1399368347638946029935917)
            ·
              refine ⟨524763130364604761225969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1399368347638946029935917 524763130364604761225969)
              ·
                refine ⟨393572347773453570919477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524763130364604761225969 393572347773453570919477)
                ·
                  refine ⟨36897407603761272273701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393572347773453570919477 36897407603761272273701)
                  ·
                    rfl

theorem cell23_646717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_646717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646717 prefixEnd_646717 := by exact prefixLift 646717
  have htrace : WordTrace (prefixWord ++ tailWord_646717) baseStart_646717 baseEnd_646717 := by
    simpa [prefixWord, tailWord_646717, baseEnd_646717] using wordTrace_append hprefix tailTrace_646717
  have hstable : (prefixWord ++ tailWord_646717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646717).length < 2 ^ (prefixWord ++ tailWord_646717).sum := by decide
  have hdescent : baseEnd_646717 < baseStart_646717 := by decide
  rcases family_descends (prefixWord ++ tailWord_646717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646746 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_646746 : Nat := 118140960795 + 646746 * 2 ^ 59
def prefixEnd_646746 : Nat := 4983230072969 + 3 ^ 40 * 646746 * 2
def baseEnd_646746 : Nat := 332091559372831837000675

theorem tailTrace_646746 : CollatzResearch.WordTrace tailWord_646746 prefixEnd_646746 332091559372831837000675 := by
  unfold tailWord_646746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897191128739293067026023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15725843009971448178736061 5897191128739293067026023)
  ·
    refine ⟨8845786693108939600539035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5897191128739293067026023 8845786693108939600539035)
    ·
      refine ⟨13268680039663409400808553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8845786693108939600539035 13268680039663409400808553)
      ·
        refine ⟨9951510029747557050606415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13268680039663409400808553 9951510029747557050606415)
        ·
          refine ⟨14927265044621335575909623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9951510029747557050606415 14927265044621335575909623)
          ·
            refine ⟨22390897566932003363864435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14927265044621335575909623 22390897566932003363864435)
            ·
              refine ⟨33586346350398005045796653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22390897566932003363864435 33586346350398005045796653)
              ·
                refine ⟨12594879881399251892173745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33586346350398005045796653 12594879881399251892173745)
                ·
                  refine ⟨9446159911049438919130309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12594879881399251892173745 9446159911049438919130309)
                  ·
                    refine ⟨1771154983321769797336933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9446159911049438919130309 1771154983321769797336933)
                    ·
                      refine ⟨332091559372831837000675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1771154983321769797336933 332091559372831837000675)
                      ·
                        rfl

theorem cell23_646746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_646746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646746 prefixEnd_646746 := by exact prefixLift 646746
  have htrace : WordTrace (prefixWord ++ tailWord_646746) baseStart_646746 baseEnd_646746 := by
    simpa [prefixWord, tailWord_646746, baseEnd_646746] using wordTrace_append hprefix tailTrace_646746
  have hstable : (prefixWord ++ tailWord_646746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646746).length < 2 ^ (prefixWord ++ tailWord_646746).sum := by decide
  have hdescent : baseEnd_646746 < baseStart_646746 := by decide
  rcases family_descends (prefixWord ++ tailWord_646746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646770 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_646770 : Nat := 118140960795 + 646770 * 2 ^ 59
def prefixEnd_646770 : Nat := 4983230072969 + 3 ^ 40 * 646770 * 2
def baseEnd_646770 : Nat := 332103882908539743100565

theorem tailTrace_646770 : CollatzResearch.WordTrace tailWord_646770 prefixEnd_646770 332103882908539743100565 := by
  unfold tailWord_646770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897409966717556091744441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15726426577913482911318509 5897409966717556091744441)
  ·
    refine ⟨4423057475038167068808331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5897409966717556091744441 4423057475038167068808331)
    ·
      refine ⟨6634586212557250603212497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4423057475038167068808331 6634586212557250603212497)
      ·
        refine ⟨4975939659417937952409373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6634586212557250603212497 4975939659417937952409373)
        ·
          refine ⟨1865977372281726732153515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4975939659417937952409373 1865977372281726732153515)
          ·
            refine ⟨2798966058422590098230273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865977372281726732153515 2798966058422590098230273)
            ·
              refine ⟨2099224543816942573672705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2798966058422590098230273 2099224543816942573672705)
              ·
                refine ⟨1574418407862706930254529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099224543816942573672705 1574418407862706930254529)
                ·
                  refine ⟨1180813805897030197690897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1574418407862706930254529 1180813805897030197690897)
                  ·
                    refine ⟨885610354422772648268173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180813805897030197690897 885610354422772648268173)
                    ·
                      refine ⟨332103882908539743100565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 885610354422772648268173 332103882908539743100565)
                      ·
                        rfl

theorem cell23_646770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_646770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646770 prefixEnd_646770 := by exact prefixLift 646770
  have htrace : WordTrace (prefixWord ++ tailWord_646770) baseStart_646770 baseEnd_646770 := by
    simpa [prefixWord, tailWord_646770, baseEnd_646770] using wordTrace_append hprefix tailTrace_646770
  have hstable : (prefixWord ++ tailWord_646770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646770).length < 2 ^ (prefixWord ++ tailWord_646770).sum := by decide
  have hdescent : baseEnd_646770 < baseStart_646770 := by decide
  rcases family_descends (prefixWord ++ tailWord_646770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646796 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_646796 : Nat := 118140960795 + 646796 * 2 ^ 59
def prefixEnd_646796 : Nat := 4983230072969 + 3 ^ 40 * 646796 * 2
def baseEnd_646796 : Nat := 332117233405556641375445

theorem tailTrace_646796 : CollatzResearch.WordTrace tailWord_646796 prefixEnd_646796 332117233405556641375445 := by
  unfold tailWord_646796
  simp only [CollatzResearch.WordTrace]
  refine ⟨11795294082388015403712121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15727058776517353871616161 11795294082388015403712121)
  ·
    refine ⟨8846470561791011552784091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11795294082388015403712121 8846470561791011552784091)
    ·
      refine ⟨13269705842686517329176137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8846470561791011552784091 13269705842686517329176137)
      ·
        refine ⟨9952279382014887996882103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13269705842686517329176137 9952279382014887996882103)
        ·
          refine ⟨14928419073022331995323155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9952279382014887996882103 14928419073022331995323155)
          ·
            refine ⟨22392628609533497992984733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14928419073022331995323155 22392628609533497992984733)
            ·
              refine ⟨8397235728575061747369275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22392628609533497992984733 8397235728575061747369275)
              ·
                refine ⟨12595853592862592621053913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8397235728575061747369275 12595853592862592621053913)
                ·
                  refine ⟨9446890194646944465790435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12595853592862592621053913 9446890194646944465790435)
                  ·
                    refine ⟨14170335291970416698685653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9446890194646944465790435 14170335291970416698685653)
                    ·
                      refine ⟨332117233405556641375445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14170335291970416698685653 332117233405556641375445)
                      ·
                        rfl

theorem cell23_646796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_646796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646796 prefixEnd_646796 := by exact prefixLift 646796
  have htrace : WordTrace (prefixWord ++ tailWord_646796) baseStart_646796 baseEnd_646796 := by
    simpa [prefixWord, tailWord_646796, baseEnd_646796] using wordTrace_append hprefix tailTrace_646796
  have hstable : (prefixWord ++ tailWord_646796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646796).length < 2 ^ (prefixWord ++ tailWord_646796).sum := by decide
  have hdescent : baseEnd_646796 < baseStart_646796 := by decide
  rcases family_descends (prefixWord ++ tailWord_646796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646804 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_646804 : Nat := 118140960795 + 646804 * 2 ^ 59
def prefixEnd_646804 : Nat := 4983230072969 + 3 ^ 40 * 646804 * 2
def baseEnd_646804 : Nat := 332121341250792610075409

theorem tailTrace_646804 : CollatzResearch.WordTrace tailWord_646804 prefixEnd_646804 332121341250792610075409 := by
  unfold tailWord_646804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11795439974373524086857733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15727253299164698782476977 11795439974373524086857733)
  ·
    refine ⟨2211644995195035766285825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11795439974373524086857733 2211644995195035766285825)
    ·
      refine ⟨1658733746396276824714369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2211644995195035766285825 1658733746396276824714369)
      ·
        refine ⟨1244050309797207618535777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1658733746396276824714369 1244050309797207618535777)
        ·
          refine ⟨933037732347905713901833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244050309797207618535777 933037732347905713901833)
          ·
            refine ⟨699778299260929285426375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933037732347905713901833 699778299260929285426375)
            ·
              refine ⟨1049667448891393928139563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699778299260929285426375 1049667448891393928139563)
              ·
                refine ⟨1574501173337090892209345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049667448891393928139563 1574501173337090892209345)
                ·
                  refine ⟨1180875880002818169157009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1574501173337090892209345 1180875880002818169157009)
                  ·
                    refine ⟨885656910002113626867757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180875880002818169157009 885656910002113626867757)
                    ·
                      refine ⟨332121341250792610075409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 885656910002113626867757 332121341250792610075409)
                      ·
                        rfl

theorem cell23_646804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_646804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646804 prefixEnd_646804 := by exact prefixLift 646804
  have htrace : WordTrace (prefixWord ++ tailWord_646804) baseStart_646804 baseEnd_646804 := by
    simpa [prefixWord, tailWord_646804, baseEnd_646804] using wordTrace_append hprefix tailTrace_646804
  have hstable : (prefixWord ++ tailWord_646804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646804).length < 2 ^ (prefixWord ++ tailWord_646804).sum := by decide
  have hdescent : baseEnd_646804 < baseStart_646804 := by decide
  rcases family_descends (prefixWord ++ tailWord_646804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646820 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_646820 : Nat := 118140960795 + 646820 * 2 ^ 59
def prefixEnd_646820 : Nat := 4983230072969 + 3 ^ 40 * 646820 * 2
def baseEnd_646820 : Nat := 110709852313754849158445

theorem tailTrace_646820 : CollatzResearch.WordTrace tailWord_646820 prefixEnd_646820 110709852313754849158445 := by
  unfold tailWord_646820
  simp only [CollatzResearch.WordTrace]
  refine ⟨11795731758344541453148957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15727642344459388604198609 11795731758344541453148957)
  ·
    refine ⟨4423399409379203044930859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11795731758344541453148957 4423399409379203044930859)
    ·
      refine ⟨6635099114068804567396289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4423399409379203044930859 6635099114068804567396289)
      ·
        refine ⟨4976324335551603425547217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6635099114068804567396289 4976324335551603425547217)
        ·
          refine ⟨3732243251663702569160413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4976324335551603425547217 3732243251663702569160413)
          ·
            refine ⟨1399591219373888463435155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3732243251663702569160413 1399591219373888463435155)
            ·
              refine ⟨2099386829060832695152733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399591219373888463435155 2099386829060832695152733)
              ·
                refine ⟨787270060897812260682275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2099386829060832695152733 787270060897812260682275)
                ·
                  refine ⟨1180905091346718391023413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787270060897812260682275 1180905091346718391023413)
                  ·
                    refine ⟨110709852313754849158445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1180905091346718391023413 110709852313754849158445)
                    ·
                      rfl

theorem cell23_646820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_646820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646820 prefixEnd_646820 := by exact prefixLift 646820
  have htrace : WordTrace (prefixWord ++ tailWord_646820) baseStart_646820 baseEnd_646820 := by
    simpa [prefixWord, tailWord_646820, baseEnd_646820] using wordTrace_append hprefix tailTrace_646820
  have hstable : (prefixWord ++ tailWord_646820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646820).length < 2 ^ (prefixWord ++ tailWord_646820).sum := by decide
  have hdescent : baseEnd_646820 < baseStart_646820 := by decide
  rcases family_descends (prefixWord ++ tailWord_646820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646843 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 3]
def baseStart_646843 : Nat := 118140960795 + 646843 * 2 ^ 59
def prefixEnd_646843 : Nat := 4983230072969 + 3 ^ 40 * 646843 * 2
def baseEnd_646843 : Nat := 332141366996317957487729

theorem tailTrace_646843 : CollatzResearch.WordTrace tailWord_646843 prefixEnd_646843 332141366996317957487729 := by
  unfold tailWord_646843
  simp only [CollatzResearch.WordTrace]
  refine ⟨23592302395605757834385183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15728201597070505222923455 23592302395605757834385183)
  ·
    refine ⟨35388453593408636751577775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23592302395605757834385183 35388453593408636751577775)
    ·
      refine ⟨53082680390112955127366663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35388453593408636751577775 53082680390112955127366663)
      ·
        refine ⟨79624020585169432691049995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53082680390112955127366663 79624020585169432691049995)
        ·
          refine ⟨119436030877754149036574993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79624020585169432691049995 119436030877754149036574993)
          ·
            refine ⟨89577023158315611777431245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119436030877754149036574993 89577023158315611777431245)
            ·
              refine ⟨33591383684368354416536717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89577023158315611777431245 33591383684368354416536717)
              ·
                refine ⟨12596768881638132906201269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33591383684368354416536717 12596768881638132906201269)
                ·
                  refine ⟨1180947082653574959956369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12596768881638132906201269 1180947082653574959956369)
                  ·
                    refine ⟨885710311990181219967277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180947082653574959956369 885710311990181219967277)
                    ·
                      refine ⟨332141366996317957487729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 885710311990181219967277 332141366996317957487729)
                      ·
                        rfl

theorem cell23_646843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 3].length) (baseStart_646843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646843 prefixEnd_646843 := by exact prefixLift 646843
  have htrace : WordTrace (prefixWord ++ tailWord_646843) baseStart_646843 baseEnd_646843 := by
    simpa [prefixWord, tailWord_646843, baseEnd_646843] using wordTrace_append hprefix tailTrace_646843
  have hstable : (prefixWord ++ tailWord_646843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646843).length < 2 ^ (prefixWord ++ tailWord_646843).sum := by decide
  have hdescent : baseEnd_646843 < baseStart_646843 := by decide
  rcases family_descends (prefixWord ++ tailWord_646843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646854 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_646854 : Nat := 118140960795 + 646854 * 2 ^ 59
def prefixEnd_646854 : Nat := 4983230072969 + 3 ^ 40 * 646854 * 2
def baseEnd_646854 : Nat := 110715671761172471483393

theorem tailTrace_646854 : CollatzResearch.WordTrace tailWord_646854 prefixEnd_646854 110715671761172471483393 := by
  unfold tailWord_646854
  simp only [CollatzResearch.WordTrace]
  refine ⟨737271987455184584782363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15728469065710604475357077 737271987455184584782363)
  ·
    refine ⟨1105907981182776877173545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 737271987455184584782363 1105907981182776877173545)
    ·
      refine ⟨829430985887082657880159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1105907981182776877173545 829430985887082657880159)
      ·
        refine ⟨1244146478830623986820239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829430985887082657880159 1244146478830623986820239)
        ·
          refine ⟨1866219718245935980230359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244146478830623986820239 1866219718245935980230359)
          ·
            refine ⟨2799329577368903970345539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866219718245935980230359 2799329577368903970345539)
            ·
              refine ⟨4198994366053355955518309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799329577368903970345539 4198994366053355955518309)
              ·
                refine ⟨787311443635004241659683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4198994366053355955518309 787311443635004241659683)
                ·
                  refine ⟨1180967165452506362489525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787311443635004241659683 1180967165452506362489525)
                  ·
                    refine ⟨110715671761172471483393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1180967165452506362489525 110715671761172471483393)
                    ·
                      rfl

theorem cell23_646854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_646854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646854 prefixEnd_646854 := by exact prefixLift 646854
  have htrace : WordTrace (prefixWord ++ tailWord_646854) baseStart_646854 baseEnd_646854 := by
    simpa [prefixWord, tailWord_646854, baseEnd_646854] using wordTrace_append hprefix tailTrace_646854
  have hstable : (prefixWord ++ tailWord_646854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646854).length < 2 ^ (prefixWord ++ tailWord_646854).sum := by decide
  have hdescent : baseEnd_646854 < baseStart_646854 := by decide
  rcases family_descends (prefixWord ++ tailWord_646854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646918 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_646918 : Nat := 118140960795 + 646918 * 2 ^ 59
def prefixEnd_646918 : Nat := 4983230072969 + 3 ^ 40 * 646918 * 2
def baseEnd_646918 : Nat := 110726626015135054683295

theorem tailTrace_646918 : CollatzResearch.WordTrace tailWord_646918 prefixEnd_646918 110726626015135054683295 := by
  unfold tailWord_646918
  simp only [CollatzResearch.WordTrace]
  refine ⟨737344933447938926355169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15730025246889363762243605 737344933447938926355169)
  ·
    refine ⟨553008700085954194766377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 737344933447938926355169 553008700085954194766377)
    ·
      refine ⟨414756525064465646074783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 553008700085954194766377 414756525064465646074783)
      ·
        refine ⟨622134787596698469112175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414756525064465646074783 622134787596698469112175)
        ·
          refine ⟨933202181395047703668263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622134787596698469112175 933202181395047703668263)
          ·
            refine ⟨1399803272092571555502395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933202181395047703668263 1399803272092571555502395)
            ·
              refine ⟨2099704908138857333253593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399803272092571555502395 2099704908138857333253593)
              ·
                refine ⟨1574778681104142999940195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099704908138857333253593 1574778681104142999940195)
                ·
                  refine ⟨2362168021656214499910293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574778681104142999940195 2362168021656214499910293)
                  ·
                    refine ⟨110726626015135054683295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2362168021656214499910293 110726626015135054683295)
                    ·
                      rfl

theorem cell23_646918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_646918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646918 prefixEnd_646918 := by exact prefixLift 646918
  have htrace : WordTrace (prefixWord ++ tailWord_646918) baseStart_646918 baseEnd_646918 := by
    simpa [prefixWord, tailWord_646918, baseEnd_646918] using wordTrace_append hprefix tailTrace_646918
  have hstable : (prefixWord ++ tailWord_646918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646918).length < 2 ^ (prefixWord ++ tailWord_646918).sum := by decide
  have hdescent : baseEnd_646918 < baseStart_646918 := by decide
  rcases family_descends (prefixWord ++ tailWord_646918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646925 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_646925 : Nat := 118140960795 + 646925 * 2 ^ 59
def prefixEnd_646925 : Nat := 4983230072969 + 3 ^ 40 * 646925 * 2
def baseEnd_646925 : Nat := 332183472409986636662353

theorem tailTrace_646925 : CollatzResearch.WordTrace tailWord_646925 prefixEnd_646925 332183472409986636662353 := by
  unfold tailWord_646925
  simp only [CollatzResearch.WordTrace]
  refine ⟨23595293181308685838870229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15730195454205790559246819 23595293181308685838870229)
  ·
    refine ⟨553014683936922324348521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23595293181308685838870229 553014683936922324348521)
    ·
      refine ⟨414761012952691743261391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 553014683936922324348521 414761012952691743261391)
      ·
        refine ⟨622141519429037614892087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414761012952691743261391 622141519429037614892087)
        ·
          refine ⟨933212279143556422338131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622141519429037614892087 933212279143556422338131)
          ·
            refine ⟨1399818418715334633507197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933212279143556422338131 1399818418715334633507197)
            ·
              refine ⟨524931907018250487565199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1399818418715334633507197 524931907018250487565199)
              ·
                refine ⟨787397860527375731347799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524931907018250487565199 787397860527375731347799)
                ·
                  refine ⟨1181096790791063597021699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787397860527375731347799 1181096790791063597021699)
                  ·
                    refine ⟨1771645186186595395532549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1181096790791063597021699 1771645186186595395532549)
                    ·
                      refine ⟨332183472409986636662353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1771645186186595395532549 332183472409986636662353)
                      ·
                        rfl

theorem cell23_646925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_646925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646925 prefixEnd_646925 := by exact prefixLift 646925
  have htrace : WordTrace (prefixWord ++ tailWord_646925) baseStart_646925 baseEnd_646925 := by
    simpa [prefixWord, tailWord_646925, baseEnd_646925] using wordTrace_append hprefix tailTrace_646925
  have hstable : (prefixWord ++ tailWord_646925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646925).length < 2 ^ (prefixWord ++ tailWord_646925).sum := by decide
  have hdescent : baseEnd_646925 < baseStart_646925 := by decide
  rcases family_descends (prefixWord ++ tailWord_646925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646947 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 4, 2, 2]
def baseStart_646947 : Nat := 118140960795 + 646947 * 2 ^ 59
def prefixEnd_646947 : Nat := 4983230072969 + 3 ^ 40 * 646947 * 2
def baseEnd_646947 : Nat := 332194768984385550587251

theorem tailTrace_646947 : CollatzResearch.WordTrace tailWord_646947 prefixEnd_646947 332194768984385550587251 := by
  unfold tailWord_646947
  simp only [CollatzResearch.WordTrace]
  refine ⟨23596095587228983596171095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15730730391485989064114063 23596095587228983596171095)
  ·
    refine ⟨35394143380843475394256643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23596095587228983596171095 35394143380843475394256643)
    ·
      refine ⟨53091215071265213091384965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35394143380843475394256643 53091215071265213091384965)
      ·
        refine ⟨9954602825862227454634681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53091215071265213091384965 9954602825862227454634681)
        ·
          refine ⟨7465952119396670590976011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954602825862227454634681 7465952119396670590976011)
          ·
            refine ⟨11198928179095005886464017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7465952119396670590976011 11198928179095005886464017)
            ·
              refine ⟨8399196134321254414848013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11198928179095005886464017 8399196134321254414848013)
              ·
                refine ⟨3149698550370470405568005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8399196134321254414848013 3149698550370470405568005)
                ·
                  refine ⟨590568478194463201044001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3149698550370470405568005 590568478194463201044001)
                  ·
                    refine ⟨442926358645847400783001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 590568478194463201044001 442926358645847400783001)
                    ·
                      refine ⟨332194768984385550587251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442926358645847400783001 332194768984385550587251)
                      ·
                        rfl

theorem cell23_646947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_646947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646947 prefixEnd_646947 := by exact prefixLift 646947
  have htrace : WordTrace (prefixWord ++ tailWord_646947) baseStart_646947 baseEnd_646947 := by
    simpa [prefixWord, tailWord_646947, baseEnd_646947] using wordTrace_append hprefix tailTrace_646947
  have hstable : (prefixWord ++ tailWord_646947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646947).length < 2 ^ (prefixWord ++ tailWord_646947).sum := by decide
  have hdescent : baseEnd_646947 < baseStart_646947 := by decide
  rcases family_descends (prefixWord ++ tailWord_646947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646964 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_646964 : Nat := 118140960795 + 646964 * 2 ^ 59
def prefixEnd_646964 : Nat := 4983230072969 + 3 ^ 40 * 646964 * 2
def baseEnd_646964 : Nat := 332203498155511984074673

theorem tailTrace_646964 : CollatzResearch.WordTrace tailWord_646964 prefixEnd_646964 332203498155511984074673 := by
  unfold tailWord_646964
  simp only [CollatzResearch.WordTrace]
  refine ⟨11798357814083697749769973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15731143752111596999693297 11798357814083697749769973)
  ·
    refine ⟨1106096045070346664040935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11798357814083697749769973 1106096045070346664040935)
    ·
      refine ⟨1659144067605519996061403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106096045070346664040935 1659144067605519996061403)
      ·
        refine ⟨2488716101408279994092105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659144067605519996061403 2488716101408279994092105)
        ·
          refine ⟨1866537076056209995569079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2488716101408279994092105 1866537076056209995569079)
          ·
            refine ⟨2799805614084314993353619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866537076056209995569079 2799805614084314993353619)
            ·
              refine ⟨4199708421126472490030429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799805614084314993353619 4199708421126472490030429)
              ·
                refine ⟨1574890657922427183761411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4199708421126472490030429 1574890657922427183761411)
                ·
                  refine ⟨2362335986883640775642117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574890657922427183761411 2362335986883640775642117)
                  ·
                    refine ⟨442937997540682645432897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2362335986883640775642117 442937997540682645432897)
                    ·
                      refine ⟨332203498155511984074673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 442937997540682645432897 332203498155511984074673)
                      ·
                        rfl

theorem cell23_646964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_646964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646964 prefixEnd_646964 := by exact prefixLift 646964
  have htrace : WordTrace (prefixWord ++ tailWord_646964) baseStart_646964 baseEnd_646964 := by
    simpa [prefixWord, tailWord_646964, baseEnd_646964] using wordTrace_append hprefix tailTrace_646964
  have hstable : (prefixWord ++ tailWord_646964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646964).length < 2 ^ (prefixWord ++ tailWord_646964).sum := by decide
  have hdescent : baseEnd_646964 < baseStart_646964 := by decide
  rcases family_descends (prefixWord ++ tailWord_646964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646970 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 7]
def baseStart_646970 : Nat := 118140960795 + 646970 * 2 ^ 59
def prefixEnd_646970 : Nat := 4983230072969 + 3 ^ 40 * 646970 * 2
def baseEnd_646970 : Nat := 36911842115493217844405

theorem tailTrace_646970 : CollatzResearch.WordTrace tailWord_646970 prefixEnd_646970 36911842115493217844405 := by
  unfold tailWord_646970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899233616536414631064591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15731289644097105682838909 5899233616536414631064591)
  ·
    refine ⟨8848850424804621946596887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899233616536414631064591 8848850424804621946596887)
    ·
      refine ⟨13273275637206932919895331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8848850424804621946596887 13273275637206932919895331)
      ·
        refine ⟨19909913455810399379842997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13273275637206932919895331 19909913455810399379842997)
        ·
          refine ⟨1866554386482224941860281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19909913455810399379842997 1866554386482224941860281)
          ·
            refine ⟨1399915789861668706395211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1866554386482224941860281 1399915789861668706395211)
            ·
              refine ⟨2099873684792503059592817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399915789861668706395211 2099873684792503059592817)
              ·
                refine ⟨1574905263594377294694613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099873684792503059592817 1574905263594377294694613)
                ·
                  refine ⟨36911842115493217844405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1574905263594377294694613 36911842115493217844405)
                  ·
                    rfl

theorem cell23_646970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_646970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_646970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_646970 prefixEnd_646970 := by exact prefixLift 646970
  have htrace : WordTrace (prefixWord ++ tailWord_646970) baseStart_646970 baseEnd_646970 := by
    simpa [prefixWord, tailWord_646970, baseEnd_646970] using wordTrace_append hprefix tailTrace_646970
  have hstable : (prefixWord ++ tailWord_646970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646970).length < 2 ^ (prefixWord ++ tailWord_646970).sum := by decide
  have hdescent : baseEnd_646970 < baseStart_646970 := by decide
  rcases family_descends (prefixWord ++ tailWord_646970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647020 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_647020 : Nat := 118140960795 + 647020 * 2 ^ 59
def prefixEnd_647020 : Nat := 4983230072969 + 3 ^ 40 * 647020 * 2
def baseEnd_647020 : Nat := 332232253072163764974415

theorem tailTrace_647020 : CollatzResearch.WordTrace tailWord_647020 prefixEnd_647020 332232253072163764974415 := by
  unfold tailWord_647020
  simp only [CollatzResearch.WordTrace]
  refine ⟨11799379057982258531789257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15732505410643011375719009 11799379057982258531789257)
  ·
    refine ⟨8849534293486693898841943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11799379057982258531789257 8849534293486693898841943)
    ·
      refine ⟨13274301440230040848262915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8849534293486693898841943 13274301440230040848262915)
      ·
        refine ⟨19911452160345061272394373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13274301440230040848262915 19911452160345061272394373)
        ·
          refine ⟨3733397280064698988573945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19911452160345061272394373 3733397280064698988573945)
          ·
            refine ⟨2800047960048524241430459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733397280064698988573945 2800047960048524241430459)
            ·
              refine ⟨4200071940072786362145689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800047960048524241430459 4200071940072786362145689)
              ·
                refine ⟨3150053955054589771609267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4200071940072786362145689 3150053955054589771609267)
                ·
                  refine ⟨4725080932581884657413901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150053955054589771609267 4725080932581884657413901)
                  ·
                    refine ⟨1771905349718206746530213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4725080932581884657413901 1771905349718206746530213)
                    ·
                      refine ⟨332232253072163764974415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1771905349718206746530213 332232253072163764974415)
                      ·
                        rfl

theorem cell23_647020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_647020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647020 prefixEnd_647020 := by exact prefixLift 647020
  have htrace : WordTrace (prefixWord ++ tailWord_647020) baseStart_647020 baseEnd_647020 := by
    simpa [prefixWord, tailWord_647020, baseEnd_647020] using wordTrace_append hprefix tailTrace_647020
  have hstable : (prefixWord ++ tailWord_647020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647020).length < 2 ^ (prefixWord ++ tailWord_647020).sum := by decide
  have hdescent : baseEnd_647020 < baseStart_647020 := by decide
  rcases family_descends (prefixWord ++ tailWord_647020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647040 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3]
def baseStart_647040 : Nat := 118140960795 + 647040 * 2 ^ 59
def prefixEnd_647040 : Nat := 4983230072969 + 3 ^ 40 * 647040 * 2
def baseEnd_647040 : Nat := 332242522685253686724323

theorem tailTrace_647040 : CollatzResearch.WordTrace tailWord_647040 prefixEnd_647040 332242522685253686724323 := by
  unfold tailWord_647040
  simp only [CollatzResearch.WordTrace]
  refine ⟨11799743787946030239653287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15732991717261373652871049 11799743787946030239653287)
  ·
    refine ⟨17699615681919045359479931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11799743787946030239653287 17699615681919045359479931)
    ·
      refine ⟨26549423522878568039219897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17699615681919045359479931 26549423522878568039219897)
      ·
        refine ⟨19912067642158926029414923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26549423522878568039219897 19912067642158926029414923)
        ·
          refine ⟨29868101463238389044122385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19912067642158926029414923 29868101463238389044122385)
          ·
            refine ⟨22401076097428791783091789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29868101463238389044122385 22401076097428791783091789)
            ·
              refine ⟨8400403536535796918659421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22401076097428791783091789 8400403536535796918659421)
              ·
                refine ⟨3150151326200923844497283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8400403536535796918659421 3150151326200923844497283)
                ·
                  refine ⟨4725226989301385766745925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150151326200923844497283 4725226989301385766745925)
                  ·
                    refine ⟨885980060494009831264861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4725226989301385766745925 885980060494009831264861)
                    ·
                      refine ⟨332242522685253686724323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 885980060494009831264861 332242522685253686724323)
                      ·
                        rfl

theorem cell23_647040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_647040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647040 prefixEnd_647040 := by exact prefixLift 647040
  have htrace : WordTrace (prefixWord ++ tailWord_647040) baseStart_647040 baseEnd_647040 := by
    simpa [prefixWord, tailWord_647040, baseEnd_647040] using wordTrace_append hprefix tailTrace_647040
  have hstable : (prefixWord ++ tailWord_647040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647040).length < 2 ^ (prefixWord ++ tailWord_647040).sum := by decide
  have hdescent : baseEnd_647040 < baseStart_647040 := by decide
  rcases family_descends (prefixWord ++ tailWord_647040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647087 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 3]
def baseStart_647087 : Nat := 118140960795 + 647087 * 2 ^ 59
def prefixEnd_647087 : Nat := 4983230072969 + 3 ^ 40 * 647087 * 2
def baseEnd_647087 : Nat := 332266656276015002836607

theorem tailTrace_647087 : CollatzResearch.WordTrace tailWord_647087 prefixEnd_647087 332266656276015002836607 := by
  unfold tailWord_647087
  simp only [CollatzResearch.WordTrace]
  refine ⟨23601201806721787506267515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15734134537814525004178343 23601201806721787506267515)
  ·
    refine ⟨35401802710082681259401273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23601201806721787506267515 35401802710082681259401273)
    ·
      refine ⟨26551352032562010944550955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35401802710082681259401273 26551352032562010944550955)
      ·
        refine ⟨39827028048843016416826433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26551352032562010944550955 39827028048843016416826433)
        ·
          refine ⟨29870271036632262312619825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39827028048843016416826433 29870271036632262312619825)
          ·
            refine ⟨22402703277474196734464869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29870271036632262312619825 22402703277474196734464869)
            ·
              refine ⟨4200506864526411887712163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22402703277474196734464869 4200506864526411887712163)
              ·
                refine ⟨6300760296789617831568245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200506864526411887712163 6300760296789617831568245)
                ·
                  refine ⟨590696277824026671709523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6300760296789617831568245 590696277824026671709523)
                  ·
                    refine ⟨886044416736040007564285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 590696277824026671709523 886044416736040007564285)
                    ·
                      refine ⟨332266656276015002836607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886044416736040007564285 332266656276015002836607)
                      ·
                        rfl

theorem cell23_647087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 3].length) (baseStart_647087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647087 prefixEnd_647087 := by exact prefixLift 647087
  have htrace : WordTrace (prefixWord ++ tailWord_647087) baseStart_647087 baseEnd_647087 := by
    simpa [prefixWord, tailWord_647087, baseEnd_647087] using wordTrace_append hprefix tailTrace_647087
  have hstable : (prefixWord ++ tailWord_647087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647087).length < 2 ^ (prefixWord ++ tailWord_647087).sum := by decide
  have hdescent : baseEnd_647087 < baseStart_647087 := by decide
  rcases family_descends (prefixWord ++ tailWord_647087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647114 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_647114 : Nat := 118140960795 + 647114 * 2 ^ 59
def prefixEnd_647114 : Nat := 4983230072969 + 3 ^ 40 * 647114 * 2
def baseEnd_647114 : Nat := 332280520253686397198983

theorem tailTrace_647114 : CollatzResearch.WordTrace tailWord_647114 prefixEnd_647114 332280520253686397198983 := by
  unfold tailWord_647114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900546644405992779375099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15734791051749314078333597 5900546644405992779375099)
  ·
    refine ⟨8850819966608989169062649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5900546644405992779375099 8850819966608989169062649)
    ·
      refine ⟨6638114974956741876796987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8850819966608989169062649 6638114974956741876796987)
      ·
        refine ⟨9957172462435112815195481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638114974956741876796987 9957172462435112815195481)
        ·
          refine ⟨7467879346826334611396611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9957172462435112815195481 7467879346826334611396611)
          ·
            refine ⟨11201819020239501917094917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467879346826334611396611 11201819020239501917094917)
            ·
              refine ⟨2100341066294906609455297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11201819020239501917094917 2100341066294906609455297)
              ·
                refine ⟨1575255799721179957091473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100341066294906609455297 1575255799721179957091473)
                ·
                  refine ⟨1181441849790884967818605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575255799721179957091473 1181441849790884967818605)
                  ·
                    refine ⟨443040693671581862931977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1181441849790884967818605 443040693671581862931977)
                    ·
                      refine ⟨332280520253686397198983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443040693671581862931977 332280520253686397198983)
                      ·
                        rfl

theorem cell23_647114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_647114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647114 prefixEnd_647114 := by exact prefixLift 647114
  have htrace : WordTrace (prefixWord ++ tailWord_647114) baseStart_647114 baseEnd_647114 := by
    simpa [prefixWord, tailWord_647114, baseEnd_647114] using wordTrace_append hprefix tailTrace_647114
  have hstable : (prefixWord ++ tailWord_647114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647114).length < 2 ^ (prefixWord ++ tailWord_647114).sum := by decide
  have hdescent : baseEnd_647114 < baseStart_647114 := by decide
  rcases family_descends (prefixWord ++ tailWord_647114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647138 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_647138 : Nat := 118140960795 + 647138 * 2 ^ 59
def prefixEnd_647138 : Nat := 4983230072969 + 3 ^ 40 * 647138 * 2
def baseEnd_647138 : Nat := 332292843789394303298873

theorem tailTrace_647138 : CollatzResearch.WordTrace tailWord_647138 prefixEnd_647138 332292843789394303298873 := by
  unfold tailWord_647138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900765482384255804093517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15735374619691348810916045 5900765482384255804093517)
  ·
    refine ⟨2212787055894095926535069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5900765482384255804093517 2212787055894095926535069)
    ·
      refine ⟨829795145960285972450651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2212787055894095926535069 829795145960285972450651)
      ·
        refine ⟨1244692718940428958675977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829795145960285972450651 1244692718940428958675977)
        ·
          refine ⟨933519539205321719006983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244692718940428958675977 933519539205321719006983)
          ·
            refine ⟨1400279308807982578510475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933519539205321719006983 1400279308807982578510475)
            ·
              refine ⟨2100418963211973867765713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400279308807982578510475 2100418963211973867765713)
              ·
                refine ⟨1575314222408980400824285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100418963211973867765713 1575314222408980400824285)
                ·
                  refine ⟨590742833403367650309107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1575314222408980400824285 590742833403367650309107)
                  ·
                    refine ⟨886114250105051475463661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 590742833403367650309107 886114250105051475463661)
                    ·
                      refine ⟨332292843789394303298873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886114250105051475463661 332292843789394303298873)
                      ·
                        rfl

theorem cell23_647138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_647138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647138 prefixEnd_647138 := by exact prefixLift 647138
  have htrace : WordTrace (prefixWord ++ tailWord_647138) baseStart_647138 baseEnd_647138 := by
    simpa [prefixWord, tailWord_647138, baseEnd_647138] using wordTrace_append hprefix tailTrace_647138
  have hstable : (prefixWord ++ tailWord_647138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647138).length < 2 ^ (prefixWord ++ tailWord_647138).sum := by decide
  have hdescent : baseEnd_647138 < baseStart_647138 := by decide
  rcases family_descends (prefixWord ++ tailWord_647138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647158 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_647158 : Nat := 118140960795 + 647158 * 2 ^ 59
def prefixEnd_647158 : Nat := 4983230072969 + 3 ^ 40 * 647158 * 2
def baseEnd_647158 : Nat := 110767704467494741682927

theorem tailTrace_647158 : CollatzResearch.WordTrace tailWord_647158 prefixEnd_647158 110767704467494741682927 := by
  unfold tailWord_647158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475236961841535414506383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15735860926309711088068085 1475236961841535414506383)
  ·
    refine ⟨2212855442762303121759575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1475236961841535414506383 2212855442762303121759575)
    ·
      refine ⟨3319283164143454682639363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2212855442762303121759575 3319283164143454682639363)
      ·
        refine ⟨4978924746215182023959045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319283164143454682639363 4978924746215182023959045)
        ·
          refine ⟨933548389915346629492321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4978924746215182023959045 933548389915346629492321)
          ·
            refine ⟨700161292436509972119241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933548389915346629492321 700161292436509972119241)
            ·
              refine ⟨525120969327382479089431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700161292436509972119241 525120969327382479089431)
              ·
                refine ⟨787681453991073718634147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525120969327382479089431 787681453991073718634147)
                ·
                  refine ⟨1181522180986610577951221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787681453991073718634147 1181522180986610577951221)
                  ·
                    refine ⟨110767704467494741682927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1181522180986610577951221 110767704467494741682927)
                    ·
                      rfl

theorem cell23_647158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_647158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647158 prefixEnd_647158 := by exact prefixLift 647158
  have htrace : WordTrace (prefixWord ++ tailWord_647158) baseStart_647158 baseEnd_647158 := by
    simpa [prefixWord, tailWord_647158, baseEnd_647158] using wordTrace_append hprefix tailTrace_647158
  have hstable : (prefixWord ++ tailWord_647158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647158).length < 2 ^ (prefixWord ++ tailWord_647158).sum := by decide
  have hdescent : baseEnd_647158 < baseStart_647158 := by decide
  rcases family_descends (prefixWord ++ tailWord_647158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647161 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 1, 1, 4]
def baseStart_647161 : Nat := 118140960795 + 647161 * 2 ^ 59
def prefixEnd_647161 : Nat := 4983230072969 + 3 ^ 40 * 647161 * 2
def baseEnd_647161 : Nat := 332304653844447713311267

theorem tailTrace_647161 : CollatzResearch.WordTrace tailWord_647161 prefixEnd_647161 332304653844447713311267 := by
  unfold tailWord_647161
  simp only [CollatzResearch.WordTrace]
  refine ⟨23603900808453698144461337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15735933872302465429640891 23603900808453698144461337)
  ·
    refine ⟨17702925606340273608346003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23603900808453698144461337 17702925606340273608346003)
    ·
      refine ⟨26554388409510410412519005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17702925606340273608346003 26554388409510410412519005)
      ·
        refine ⟨9957895653566403904694627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26554388409510410412519005 9957895653566403904694627)
        ·
          refine ⟨14936843480349605857041941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9957895653566403904694627 14936843480349605857041941)
          ·
            refine ⟨700164538141387774548841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14936843480349605857041941 700164538141387774548841)
            ·
              refine ⟨525123403606040830911631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700164538141387774548841 525123403606040830911631)
              ·
                refine ⟨787685105409061246367447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525123403606040830911631 787685105409061246367447)
                ·
                  refine ⟨1181527658113591869551171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787685105409061246367447 1181527658113591869551171)
                  ·
                    refine ⟨1772291487170387804326757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1181527658113591869551171 1772291487170387804326757)
                    ·
                      refine ⟨332304653844447713311267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1772291487170387804326757 332304653844447713311267)
                      ·
                        rfl

theorem cell23_647161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_647161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647161 prefixEnd_647161 := by exact prefixLift 647161
  have htrace : WordTrace (prefixWord ++ tailWord_647161) baseStart_647161 baseEnd_647161 := by
    simpa [prefixWord, tailWord_647161, baseEnd_647161] using wordTrace_append hprefix tailTrace_647161
  have hstable : (prefixWord ++ tailWord_647161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647161).length < 2 ^ (prefixWord ++ tailWord_647161).sum := by decide
  have hdescent : baseEnd_647161 < baseStart_647161 := by decide
  rcases family_descends (prefixWord ++ tailWord_647161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647164 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_647164 : Nat := 118140960795 + 647164 * 2 ^ 59
def prefixEnd_647164 : Nat := 4983230072969 + 3 ^ 40 * 647164 * 2
def baseEnd_647164 : Nat := 332306194286411201573753

theorem tailTrace_647164 : CollatzResearch.WordTrace tailWord_647164 prefixEnd_647164 332306194286411201573753 := by
  unfold tailWord_647164
  simp only [CollatzResearch.WordTrace]
  refine ⟨11802005113721414828410273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15736006818295219771213697 11802005113721414828410273)
  ·
    refine ⟨8851503835291061121307705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11802005113721414828410273 8851503835291061121307705)
    ·
      refine ⟨6638627876468295840980779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8851503835291061121307705 6638627876468295840980779)
      ·
        refine ⟨9957941814702443761471169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638627876468295840980779 9957941814702443761471169)
        ·
          refine ⟨7468456361026832821103377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9957941814702443761471169 7468456361026832821103377)
          ·
            refine ⟨5601342270770124615827533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7468456361026832821103377 5601342270770124615827533)
            ·
              refine ⟨2100503351538796730935325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5601342270770124615827533 2100503351538796730935325)
              ·
                refine ⟨787688756827048774100747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2100503351538796730935325 787688756827048774100747)
                ·
                  refine ⟨1181533135240573161151121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787688756827048774100747 1181533135240573161151121)
                  ·
                    refine ⟨886149851430429870863341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1181533135240573161151121 886149851430429870863341)
                    ·
                      refine ⟨332306194286411201573753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886149851430429870863341 332306194286411201573753)
                      ·
                        rfl

theorem cell23_647164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_647164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647164 prefixEnd_647164 := by exact prefixLift 647164
  have htrace : WordTrace (prefixWord ++ tailWord_647164) baseStart_647164 baseEnd_647164 := by
    simpa [prefixWord, tailWord_647164, baseEnd_647164] using wordTrace_append hprefix tailTrace_647164
  have hstable : (prefixWord ++ tailWord_647164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647164).length < 2 ^ (prefixWord ++ tailWord_647164).sum := by decide
  have hdescent : baseEnd_647164 < baseStart_647164 := by decide
  rcases family_descends (prefixWord ++ tailWord_647164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647178 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_647178 : Nat := 118140960795 + 647178 * 2 ^ 59
def prefixEnd_647178 : Nat := 4983230072969 + 3 ^ 40 * 647178 * 2
def baseEnd_647178 : Nat := 332313383015574146798689

theorem tailTrace_647178 : CollatzResearch.WordTrace tailWord_647178 prefixEnd_647178 332313383015574146798689 := by
  unfold tailWord_647178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901130212348027511957547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15736347232928073365220125 5901130212348027511957547)
  ·
    refine ⟨8851695318522041267936321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5901130212348027511957547 8851695318522041267936321)
    ·
      refine ⟨6638771488891530950952241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8851695318522041267936321 6638771488891530950952241)
      ·
        refine ⟨4979078616668648213214181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6638771488891530950952241 4979078616668648213214181)
        ·
          refine ⟨933577240625371539977659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4979078616668648213214181 933577240625371539977659)
          ·
            refine ⟨1400365860938057309966489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933577240625371539977659 1400365860938057309966489)
            ·
              refine ⟨1050274395703542982474867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1400365860938057309966489 1050274395703542982474867)
              ·
                refine ⟨1575411593555314473712301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050274395703542982474867 1575411593555314473712301)
                ·
                  refine ⟨590779347583242927642113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1575411593555314473712301 590779347583242927642113)
                  ·
                    refine ⟨443084510687432195731585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 590779347583242927642113 443084510687432195731585)
                    ·
                      refine ⟨332313383015574146798689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443084510687432195731585 332313383015574146798689)
                      ·
                        rfl

theorem cell23_647178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_647178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647178 prefixEnd_647178 := by exact prefixLift 647178
  have htrace : WordTrace (prefixWord ++ tailWord_647178) baseStart_647178 baseEnd_647178 := by
    simpa [prefixWord, tailWord_647178, baseEnd_647178] using wordTrace_append hprefix tailTrace_647178
  have hstable : (prefixWord ++ tailWord_647178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647178).length < 2 ^ (prefixWord ++ tailWord_647178).sum := by decide
  have hdescent : baseEnd_647178 < baseStart_647178 := by decide
  rcases family_descends (prefixWord ++ tailWord_647178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647188 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_647188 : Nat := 118140960795 + 647188 * 2 ^ 59
def prefixEnd_647188 : Nat := 4983230072969 + 3 ^ 40 * 647188 * 2
def baseEnd_647188 : Nat := 110772839274039702557881

theorem tailTrace_647188 : CollatzResearch.WordTrace tailWord_647188 prefixEnd_647188 110772839274039702557881 := by
  unfold tailWord_647188
  simp only [CollatzResearch.WordTrace]
  refine ⟨11802442789677940877847109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15736590386237254503796145 11802442789677940877847109)
  ·
    refine ⟨2212958023064613914596333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11802442789677940877847109 2212958023064613914596333)
    ·
      refine ⟨829859258649230217973625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2212958023064613914596333 829859258649230217973625)
      ·
        refine ⟨622394443986922663480219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 829859258649230217973625 622394443986922663480219)
        ·
          refine ⟨933591665980383995220329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622394443986922663480219 933591665980383995220329)
          ·
            refine ⟨700193749485287996415247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933591665980383995220329 700193749485287996415247)
            ·
              refine ⟨1050290624227931994622871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700193749485287996415247 1050290624227931994622871)
              ·
                refine ⟨1575435936341897991934307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050290624227931994622871 1575435936341897991934307)
                ·
                  refine ⟨2363153904512846987901461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575435936341897991934307 2363153904512846987901461)
                  ·
                    refine ⟨110772839274039702557881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2363153904512846987901461 110772839274039702557881)
                    ·
                      rfl

theorem cell23_647188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_647188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647188 prefixEnd_647188 := by exact prefixLift 647188
  have htrace : WordTrace (prefixWord ++ tailWord_647188) baseStart_647188 baseEnd_647188 := by
    simpa [prefixWord, tailWord_647188, baseEnd_647188] using wordTrace_append hprefix tailTrace_647188
  have hstable : (prefixWord ++ tailWord_647188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647188).length < 2 ^ (prefixWord ++ tailWord_647188).sum := by decide
  have hdescent : baseEnd_647188 < baseStart_647188 := by decide
  rcases family_descends (prefixWord ++ tailWord_647188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647191 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_647191 : Nat := 118140960795 + 647191 * 2 ^ 59
def prefixEnd_647191 : Nat := 4983230072969 + 3 ^ 40 * 647191 * 2
def baseEnd_647191 : Nat := 332320058264082595936129

theorem tailTrace_647191 : CollatzResearch.WordTrace tailWord_647191 prefixEnd_647191 332320058264082595936129 := by
  unfold tailWord_647191
  simp only [CollatzResearch.WordTrace]
  refine ⟨23604994998345013268053427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15736663332230008845368951 23604994998345013268053427)
  ·
    refine ⟨35407492497517519902080141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23604994998345013268053427 35407492497517519902080141)
    ·
      refine ⟨13277809686569069963280053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35407492497517519902080141 13277809686569069963280053)
      ·
        refine ⟨1244794658115850309057505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13277809686569069963280053 1244794658115850309057505)
        ·
          refine ⟨933595993586887731793129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244794658115850309057505 933595993586887731793129)
          ·
            refine ⟨700196995190165798844847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933595993586887731793129 700196995190165798844847)
            ·
              refine ⟨1050295492785248698267271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700196995190165798844847 1050295492785248698267271)
              ·
                refine ⟨1575443239177873047400907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050295492785248698267271 1575443239177873047400907)
                ·
                  refine ⟨2363164858766809571101361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575443239177873047400907 2363164858766809571101361)
                  ·
                    refine ⟨1772373644075107178326021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2363164858766809571101361 1772373644075107178326021)
                    ·
                      refine ⟨332320058264082595936129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1772373644075107178326021 332320058264082595936129)
                      ·
                        rfl

theorem cell23_647191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_647191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647191 prefixEnd_647191 := by exact prefixLift 647191
  have htrace : WordTrace (prefixWord ++ tailWord_647191) baseStart_647191 baseEnd_647191 := by
    simpa [prefixWord, tailWord_647191, baseEnd_647191] using wordTrace_append hprefix tailTrace_647191
  have hstable : (prefixWord ++ tailWord_647191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647191).length < 2 ^ (prefixWord ++ tailWord_647191).sum := by decide
  have hdescent : baseEnd_647191 < baseStart_647191 := by decide
  rcases family_descends (prefixWord ++ tailWord_647191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647194 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_647194 : Nat := 118140960795 + 647194 * 2 ^ 59
def prefixEnd_647194 : Nat := 4983230072969 + 3 ^ 40 * 647194 * 2
def baseEnd_647194 : Nat := 332321598706046084198615

theorem tailTrace_647194 : CollatzResearch.WordTrace tailWord_647194 prefixEnd_647194 332321598706046084198615 := by
  unfold tailWord_647194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901276104333536195103159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15736736278222763186941757 5901276104333536195103159)
  ·
    refine ⟨8851914156500304292654739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5901276104333536195103159 8851914156500304292654739)
    ·
      refine ⟨13277871234750456438982109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8851914156500304292654739 13277871234750456438982109)
      ·
        refine ⟨4979201713031421164618291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13277871234750456438982109 4979201713031421164618291)
        ·
          refine ⟨7468802569547131746927437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4979201713031421164618291 7468802569547131746927437)
          ·
            refine ⟨2800800963580174405097789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7468802569547131746927437 2800800963580174405097789)
            ·
              refine ⟨1050300361342565401911671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2800800963580174405097789 1050300361342565401911671)
              ·
                refine ⟨1575450542013848102867507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050300361342565401911671 1575450542013848102867507)
                ·
                  refine ⟨2363175813020772154301261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575450542013848102867507 2363175813020772154301261)
                  ·
                    refine ⟨886190929882789557862973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363175813020772154301261 886190929882789557862973)
                    ·
                      refine ⟨332321598706046084198615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886190929882789557862973 332321598706046084198615)
                      ·
                        rfl

theorem cell23_647194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_647194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647194 prefixEnd_647194 := by exact prefixLift 647194
  have htrace : WordTrace (prefixWord ++ tailWord_647194) baseStart_647194 baseEnd_647194 := by
    simpa [prefixWord, tailWord_647194, baseEnd_647194] using wordTrace_append hprefix tailTrace_647194
  have hstable : (prefixWord ++ tailWord_647194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647194).length < 2 ^ (prefixWord ++ tailWord_647194).sum := by decide
  have hdescent : baseEnd_647194 < baseStart_647194 := by decide
  rcases family_descends (prefixWord ++ tailWord_647194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647201 : List Nat := [1, 2, 3, 2, 5, 1, 2, 7]
def baseStart_647201 : Nat := 118140960795 + 647201 * 2 ^ 59
def prefixEnd_647201 : Nat := 4983230072969 + 3 ^ 40 * 647201 * 2
def baseEnd_647201 : Nat := 12308340484097316918929

theorem tailTrace_647201 : CollatzResearch.WordTrace tailWord_647201 prefixEnd_647201 12308340484097316918929 := by
  unfold tailWord_647201
  simp only [CollatzResearch.WordTrace]
  refine ⟨23605359728308784975917457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15736906485539189983944971 23605359728308784975917457)
  ·
    refine ⟨17704019796231588731938093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23605359728308784975917457 17704019796231588731938093)
    ·
      refine ⟨6639007423586845774476785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17704019796231588731938093 6639007423586845774476785)
      ·
        refine ⟨4979255567690134330857589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6639007423586845774476785 4979255567690134330857589)
        ·
          refine ⟨466805209470950093517899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4979255567690134330857589 466805209470950093517899)
          ·
            refine ⟨700207814206425140276849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466805209470950093517899 700207814206425140276849)
            ·
              refine ⟨525155860654818855207637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700207814206425140276849 525155860654818855207637)
              ·
                refine ⟨12308340484097316918929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 525155860654818855207637 12308340484097316918929)
                ·
                  rfl

theorem cell23_647201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 7].length) (baseStart_647201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647201 prefixEnd_647201 := by exact prefixLift 647201
  have htrace : WordTrace (prefixWord ++ tailWord_647201) baseStart_647201 baseEnd_647201 := by
    simpa [prefixWord, tailWord_647201, baseEnd_647201] using wordTrace_append hprefix tailTrace_647201
  have hstable : (prefixWord ++ tailWord_647201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647201).length < 2 ^ (prefixWord ++ tailWord_647201).sum := by decide
  have hdescent : baseEnd_647201 < baseStart_647201 := by decide
  rcases family_descends (prefixWord ++ tailWord_647201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647221 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_647221 : Nat := 118140960795 + 647221 * 2 ^ 59
def prefixEnd_647221 : Nat := 4983230072969 + 3 ^ 40 * 647221 * 2
def baseEnd_647221 : Nat := 332335462683717478560991

theorem tailTrace_647221 : CollatzResearch.WordTrace tailWord_647221 prefixEnd_647221 332335462683717478560991 := by
  unfold tailWord_647221
  simp only [CollatzResearch.WordTrace]
  refine ⟨23606089188236328391645517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15737392792157552261097011 23606089188236328391645517)
  ·
    refine ⟨8852283445588623146867069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23606089188236328391645517 8852283445588623146867069)
    ·
      refine ⟨3319606292095733680075151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8852283445588623146867069 3319606292095733680075151)
      ·
        refine ⟨4979409438143600520112727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319606292095733680075151 4979409438143600520112727)
        ·
          refine ⟨7469114157215400780169091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4979409438143600520112727 7469114157215400780169091)
          ·
            refine ⟨11203671235823101170253637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7469114157215400780169091 11203671235823101170253637)
            ·
              refine ⟨2100688356716831469422557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11203671235823101170253637 2100688356716831469422557)
              ·
                refine ⟨787758133768811801033459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2100688356716831469422557 787758133768811801033459)
                ·
                  refine ⟨1181637200653217701550189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787758133768811801033459 1181637200653217701550189)
                  ·
                    refine ⟨443113950244956638081321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1181637200653217701550189 443113950244956638081321)
                    ·
                      refine ⟨332335462683717478560991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443113950244956638081321 332335462683717478560991)
                      ·
                        rfl

theorem cell23_647221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_647221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647221 prefixEnd_647221 := by exact prefixLift 647221
  have htrace : WordTrace (prefixWord ++ tailWord_647221) baseStart_647221 baseEnd_647221 := by
    simpa [prefixWord, tailWord_647221, baseEnd_647221] using wordTrace_append hprefix tailTrace_647221
  have hstable : (prefixWord ++ tailWord_647221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647221).length < 2 ^ (prefixWord ++ tailWord_647221).sum := by decide
  have hdescent : baseEnd_647221 < baseStart_647221 := by decide
  rcases family_descends (prefixWord ++ tailWord_647221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647237 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_647237 : Nat := 118140960795 + 647237 * 2 ^ 59
def prefixEnd_647237 : Nat := 4983230072969 + 3 ^ 40 * 647237 * 2
def baseEnd_647237 : Nat := 332343678374189415960917

theorem tailTrace_647237 : CollatzResearch.WordTrace tailWord_647237 prefixEnd_647237 332343678374189415960917 := by
  unfold tailWord_647237
  simp only [CollatzResearch.WordTrace]
  refine ⟨23606672756178363124227965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15737781837452242082818643 23606672756178363124227965)
  ·
    refine ⟨8852502283566886171585487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23606672756178363124227965 8852502283566886171585487)
    ·
      refine ⟨13278753425350329257378231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8852502283566886171585487 13278753425350329257378231)
      ·
        refine ⟨19918130138025493886067347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13278753425350329257378231 19918130138025493886067347)
        ·
          refine ⟨29877195207038240829101021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19918130138025493886067347 29877195207038240829101021)
          ·
            refine ⟨11203948202639340310912883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29877195207038240829101021 11203948202639340310912883)
            ·
              refine ⟨16805922303959010466369325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11203948202639340310912883 16805922303959010466369325)
              ·
                refine ⟨6302220863984628924888497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16805922303959010466369325 6302220863984628924888497)
                ·
                  refine ⟨4726665647988471693666373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302220863984628924888497 4726665647988471693666373)
                  ·
                    refine ⟨886249808997838442562445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4726665647988471693666373 886249808997838442562445)
                    ·
                      refine ⟨332343678374189415960917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886249808997838442562445 332343678374189415960917)
                      ·
                        rfl

theorem cell23_647237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_647237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647237 prefixEnd_647237 := by exact prefixLift 647237
  have htrace : WordTrace (prefixWord ++ tailWord_647237) baseStart_647237 baseEnd_647237 := by
    simpa [prefixWord, tailWord_647237, baseEnd_647237] using wordTrace_append hprefix tailTrace_647237
  have hstable : (prefixWord ++ tailWord_647237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647237).length < 2 ^ (prefixWord ++ tailWord_647237).sum := by decide
  have hdescent : baseEnd_647237 < baseStart_647237 := by decide
  rcases family_descends (prefixWord ++ tailWord_647237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647238 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_647238 : Nat := 118140960795 + 647238 * 2 ^ 59
def prefixEnd_647238 : Nat := 4983230072969 + 3 ^ 40 * 647238 * 2
def baseEnd_647238 : Nat := 332344191854843912048413

theorem tailTrace_647238 : CollatzResearch.WordTrace tailWord_647238 prefixEnd_647238 332344191854843912048413 := by
  unfold tailWord_647238
  simp only [CollatzResearch.WordTrace]
  refine ⟨737709663411710634219199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15737806152783160196676245 737709663411710634219199)
  ·
    refine ⟨1106564495117565951328799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 737709663411710634219199 1106564495117565951328799)
    ·
      refine ⟨1659846742676348926993199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106564495117565951328799 1659846742676348926993199)
      ·
        refine ⟨2489770114014523390489799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659846742676348926993199 2489770114014523390489799)
        ·
          refine ⟨3734655171021785085734699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2489770114014523390489799 3734655171021785085734699)
          ·
            refine ⟨5601982756532677628602049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734655171021785085734699 5601982756532677628602049)
            ·
              refine ⟨4201487067399508221451537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5601982756532677628602049 4201487067399508221451537)
              ·
                refine ⟨3151115300549631166088653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4201487067399508221451537 3151115300549631166088653)
                ·
                  refine ⟨1181668237706111687283245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3151115300549631166088653 1181668237706111687283245)
                  ·
                    refine ⟨443125589139791882731217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1181668237706111687283245 443125589139791882731217)
                    ·
                      refine ⟨332344191854843912048413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443125589139791882731217 332344191854843912048413)
                      ·
                        rfl

theorem cell23_647238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_647238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647238 prefixEnd_647238 := by exact prefixLift 647238
  have htrace : WordTrace (prefixWord ++ tailWord_647238) baseStart_647238 baseEnd_647238 := by
    simpa [prefixWord, tailWord_647238, baseEnd_647238] using wordTrace_append hprefix tailTrace_647238
  have hstable : (prefixWord ++ tailWord_647238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647238).length < 2 ^ (prefixWord ++ tailWord_647238).sum := by decide
  have hdescent : baseEnd_647238 < baseStart_647238 := by decide
  rcases family_descends (prefixWord ++ tailWord_647238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647324 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_647324 : Nat := 118140960795 + 647324 * 2 ^ 59
def prefixEnd_647324 : Nat := 4983230072969 + 3 ^ 40 * 647324 * 2
def baseEnd_647324 : Nat := 332388351191130575573017

theorem tailTrace_647324 : CollatzResearch.WordTrace tailWord_647324 prefixEnd_647324 332388351191130575573017 := by
  unfold tailWord_647324
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804922953431588491322513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15739897271242117988430017 11804922953431588491322513)
  ·
    refine ⟨8853692215073691368491885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11804922953431588491322513 8853692215073691368491885)
    ·
      refine ⟨3320134580652634263184457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8853692215073691368491885 3320134580652634263184457)
      ·
        refine ⟨2490100935489475697388343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3320134580652634263184457 2490100935489475697388343)
        ·
          refine ⟨3735151403234213546082515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490100935489475697388343 3735151403234213546082515)
          ·
            refine ⟨5602727104851320319123773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735151403234213546082515 5602727104851320319123773)
            ·
              refine ⟨2101022664319245119671415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5602727104851320319123773 2101022664319245119671415)
              ·
                refine ⟨3151533996478867679507123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101022664319245119671415 3151533996478867679507123)
                ·
                  refine ⟨4727300994718301519260685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151533996478867679507123 4727300994718301519260685)
                  ·
                    refine ⟨1772737873019363069722757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4727300994718301519260685 1772737873019363069722757)
                    ·
                      refine ⟨332388351191130575573017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1772737873019363069722757 332388351191130575573017)
                      ·
                        rfl

theorem cell23_647324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_647324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647324 prefixEnd_647324 := by exact prefixLift 647324
  have htrace : WordTrace (prefixWord ++ tailWord_647324) baseStart_647324 baseEnd_647324 := by
    simpa [prefixWord, tailWord_647324, baseEnd_647324] using wordTrace_append hprefix tailTrace_647324
  have hstable : (prefixWord ++ tailWord_647324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647324).length < 2 ^ (prefixWord ++ tailWord_647324).sum := by decide
  have hdescent : baseEnd_647324 < baseStart_647324 := by decide
  rcases family_descends (prefixWord ++ tailWord_647324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647351 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 3, 4]
def baseStart_647351 : Nat := 118140960795 + 647351 * 2 ^ 59
def prefixEnd_647351 : Nat := 4983230072969 + 3 ^ 40 * 647351 * 2
def baseEnd_647351 : Nat := 110800738389600656645131

theorem tailTrace_647351 : CollatzResearch.WordTrace tailWord_647351 prefixEnd_647351 110800738389600656645131 := by
  unfold tailWord_647351
  simp only [CollatzResearch.WordTrace]
  refine ⟨23610830677765360593877907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15740553785176907062585271 23610830677765360593877907)
  ·
    refine ⟨35416246016648040890816861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23610830677765360593877907 35416246016648040890816861)
    ·
      refine ⟨13281092256243015334056323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35416246016648040890816861 13281092256243015334056323)
      ·
        refine ⟨19921638384364523001084485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13281092256243015334056323 19921638384364523001084485)
        ·
          refine ⟨3735307197068348062703341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19921638384364523001084485 3735307197068348062703341)
          ·
            refine ⟨1400740198900630523513753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3735307197068348062703341 1400740198900630523513753)
            ·
              refine ⟨1050555149175472892635315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1400740198900630523513753 1050555149175472892635315)
              ·
                refine ⟨1575832723763209338952973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050555149175472892635315 1575832723763209338952973)
                ·
                  refine ⟨590937271411203502107365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1575832723763209338952973 590937271411203502107365)
                  ·
                    refine ⟨110800738389600656645131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 590937271411203502107365 110800738389600656645131)
                    ·
                      rfl

theorem cell23_647351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_647351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647351 prefixEnd_647351 := by exact prefixLift 647351
  have htrace : WordTrace (prefixWord ++ tailWord_647351) baseStart_647351 baseEnd_647351 := by
    simpa [prefixWord, tailWord_647351, baseEnd_647351] using wordTrace_append hprefix tailTrace_647351
  have hstable : (prefixWord ++ tailWord_647351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647351).length < 2 ^ (prefixWord ++ tailWord_647351).sum := by decide
  have hdescent : baseEnd_647351 < baseStart_647351 := by decide
  rcases family_descends (prefixWord ++ tailWord_647351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647387 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5]
def baseStart_647387 : Nat := 118140960795 + 647387 * 2 ^ 59
def prefixEnd_647387 : Nat := 4983230072969 + 3 ^ 40 * 647387 * 2
def baseEnd_647387 : Nat := 332420700472363829085227

theorem tailTrace_647387 : CollatzResearch.WordTrace tailWord_647387 prefixEnd_647387 332420700472363829085227 := by
  unfold tailWord_647387
  simp only [CollatzResearch.WordTrace]
  refine ⟨23612143705634938742188415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15741429137089959161458943 23612143705634938742188415)
  ·
    refine ⟨35418215558452408113282623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23612143705634938742188415 35418215558452408113282623)
    ·
      refine ⟨53127323337678612169923935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35418215558452408113282623 53127323337678612169923935)
      ·
        refine ⟨79690985006517918254885903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53127323337678612169923935 79690985006517918254885903)
        ·
          refine ⟨119536477509776877382328855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79690985006517918254885903 119536477509776877382328855)
          ·
            refine ⟨179304716264665316073493283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119536477509776877382328855 179304716264665316073493283)
            ·
              refine ⟨268957074396997974110239925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179304716264665316073493283 268957074396997974110239925)
              ·
                refine ⟨25214725724718560072834993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268957074396997974110239925 25214725724718560072834993)
                ·
                  refine ⟨18911044293538920054626245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25214725724718560072834993 18911044293538920054626245)
                  ·
                    refine ⟨3545820805038547510242421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18911044293538920054626245 3545820805038547510242421)
                    ·
                      refine ⟨332420700472363829085227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3545820805038547510242421 332420700472363829085227)
                      ·
                        rfl

theorem cell23_647387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_647387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647387 prefixEnd_647387 := by exact prefixLift 647387
  have htrace : WordTrace (prefixWord ++ tailWord_647387) baseStart_647387 baseEnd_647387 := by
    simpa [prefixWord, tailWord_647387, baseEnd_647387] using wordTrace_append hprefix tailTrace_647387
  have hstable : (prefixWord ++ tailWord_647387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647387).length < 2 ^ (prefixWord ++ tailWord_647387).sum := by decide
  have hdescent : baseEnd_647387 < baseStart_647387 := by decide
  rcases family_descends (prefixWord ++ tailWord_647387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647401 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 2, 3, 2]
def baseStart_647401 : Nat := 118140960795 + 647401 * 2 ^ 59
def prefixEnd_647401 : Nat := 4983230072969 + 3 ^ 40 * 647401 * 2
def baseEnd_647401 : Nat := 332427889201526774310163

theorem tailTrace_647401 : CollatzResearch.WordTrace tailWord_647401 prefixEnd_647401 332427889201526774310163 := by
  unfold tailWord_647401
  simp only [CollatzResearch.WordTrace]
  refine ⟨23612654327584219133198057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15741769551722812755465371 23612654327584219133198057)
  ·
    refine ⟨17709490745688164349898543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23612654327584219133198057 17709490745688164349898543)
    ·
      refine ⟨26564236118532246524847815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17709490745688164349898543 26564236118532246524847815)
      ·
        refine ⟨39846354177798369787271723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26564236118532246524847815 39846354177798369787271723)
        ·
          refine ⟨59769531266697554680907585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39846354177798369787271723 59769531266697554680907585)
          ·
            refine ⟨44827148450023166010680689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59769531266697554680907585 44827148450023166010680689)
            ·
              refine ⟨33620361337517374508010517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44827148450023166010680689 33620361337517374508010517)
              ·
                refine ⟨1575954437696126930062993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33620361337517374508010517 1575954437696126930062993)
                ·
                  refine ⟨1181965828272095197547245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575954437696126930062993 1181965828272095197547245)
                  ·
                    refine ⟨443237185602035699080217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1181965828272095197547245 443237185602035699080217)
                    ·
                      refine ⟨332427889201526774310163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443237185602035699080217 332427889201526774310163)
                      ·
                        rfl

theorem cell23_647401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 3, 2].length) (baseStart_647401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647401 prefixEnd_647401 := by exact prefixLift 647401
  have htrace : WordTrace (prefixWord ++ tailWord_647401) baseStart_647401 baseEnd_647401 := by
    simpa [prefixWord, tailWord_647401, baseEnd_647401] using wordTrace_append hprefix tailTrace_647401
  have hstable : (prefixWord ++ tailWord_647401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647401).length < 2 ^ (prefixWord ++ tailWord_647401).sum := by decide
  have hdescent : baseEnd_647401 < baseStart_647401 := by decide
  rcases family_descends (prefixWord ++ tailWord_647401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647408 : List Nat := [2, 1, 1, 1, 3, 1, 1, 8, 1, 1, 3]
def baseStart_647408 : Nat := 118140960795 + 647408 * 2 ^ 59
def prefixEnd_647408 : Nat := 4983230072969 + 3 ^ 40 * 647408 * 2
def baseEnd_647408 : Nat := 332431483566108246922631

theorem tailTrace_647408 : CollatzResearch.WordTrace tailWord_647408 prefixEnd_647408 332431483566108246922631 := by
  unfold tailWord_647408
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806454819279429664351439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15741939759039239552468585 11806454819279429664351439)
  ·
    refine ⟨17709682228919144496527159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11806454819279429664351439 17709682228919144496527159)
    ·
      refine ⟨26564523343378716744790739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17709682228919144496527159 26564523343378716744790739)
      ·
        refine ⟨39846785015068075117186109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26564523343378716744790739 39846785015068075117186109)
        ·
          refine ⟨14942544380650528168944791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39846785015068075117186109 14942544380650528168944791)
          ·
            refine ⟨22413816570975792253417187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14942544380650528168944791 22413816570975792253417187)
            ·
              refine ⟨33620724856463688380125781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22413816570975792253417187 33620724856463688380125781)
              ·
                refine ⟨393992869411683848204599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 33620724856463688380125781 393992869411683848204599)
                ·
                  refine ⟨590989304117525772306899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393992869411683848204599 590989304117525772306899)
                  ·
                    refine ⟨886483956176288658460349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 590989304117525772306899 886483956176288658460349)
                    ·
                      refine ⟨332431483566108246922631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886483956176288658460349 332431483566108246922631)
                      ·
                        rfl

theorem cell23_647408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 1, 3].length) (baseStart_647408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647408 prefixEnd_647408 := by exact prefixLift 647408
  have htrace : WordTrace (prefixWord ++ tailWord_647408) baseStart_647408 baseEnd_647408 := by
    simpa [prefixWord, tailWord_647408, baseEnd_647408] using wordTrace_append hprefix tailTrace_647408
  have hstable : (prefixWord ++ tailWord_647408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647408).length < 2 ^ (prefixWord ++ tailWord_647408).sum := by decide
  have hdescent : baseEnd_647408 < baseStart_647408 := by decide
  rcases family_descends (prefixWord ++ tailWord_647408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647434 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_647434 : Nat := 118140960795 + 647434 * 2 ^ 59
def prefixEnd_647434 : Nat := 4983230072969 + 3 ^ 40 * 647434 * 2
def baseEnd_647434 : Nat := 332444834063125145197511

theorem tailTrace_647434 : CollatzResearch.WordTrace tailWord_647434 prefixEnd_647434 332444834063125145197511 := by
  unfold tailWord_647434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5903464484116166442287339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15742571957643110512766237 5903464484116166442287339)
  ·
    refine ⟨8855196726174249663431009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5903464484116166442287339 8855196726174249663431009)
    ·
      refine ⟨6641397544630687247573257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8855196726174249663431009 6641397544630687247573257)
      ·
        refine ⟨4981048158473015435679943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6641397544630687247573257 4981048158473015435679943)
        ·
          refine ⟨7471572237709523153519915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981048158473015435679943 7471572237709523153519915)
          ·
            refine ⟨11207358356564284730279873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471572237709523153519915 11207358356564284730279873)
            ·
              refine ⟨8405518767423213547709905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11207358356564284730279873 8405518767423213547709905)
              ·
                refine ⟨6304139075567410160782429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8405518767423213547709905 6304139075567410160782429)
                ·
                  refine ⟨2364052153337778810293411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6304139075567410160782429 2364052153337778810293411)
                  ·
                    refine ⟨3546078230006668215440117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2364052153337778810293411 3546078230006668215440117)
                    ·
                      refine ⟨332444834063125145197511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3546078230006668215440117 332444834063125145197511)
                      ·
                        rfl

theorem cell23_647434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_647434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647434 prefixEnd_647434 := by exact prefixLift 647434
  have htrace : WordTrace (prefixWord ++ tailWord_647434) baseStart_647434 baseEnd_647434 := by
    simpa [prefixWord, tailWord_647434, baseEnd_647434] using wordTrace_append hprefix tailTrace_647434
  have hstable : (prefixWord ++ tailWord_647434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647434).length < 2 ^ (prefixWord ++ tailWord_647434).sum := by decide
  have hdescent : baseEnd_647434 < baseStart_647434 := by decide
  rcases family_descends (prefixWord ++ tailWord_647434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647448 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 1, 1, 4]
def baseStart_647448 : Nat := 118140960795 + 647448 * 2 ^ 59
def prefixEnd_647448 : Nat := 4983230072969 + 3 ^ 40 * 647448 * 2
def baseEnd_647448 : Nat := 332452022792288090422447

theorem tailTrace_647448 : CollatzResearch.WordTrace tailWord_647448 prefixEnd_647448 332452022792288090422447 := by
  unfold tailWord_647448
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807184279206973080079499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15742912372275964106772665 11807184279206973080079499)
  ·
    refine ⟨17710776418810459620119249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11807184279206973080079499 17710776418810459620119249)
    ·
      refine ⟨13283082314107844715089437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17710776418810459620119249 13283082314107844715089437)
      ·
        refine ⟨4981155867790441768158539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13283082314107844715089437 4981155867790441768158539)
        ·
          refine ⟨7471733801685662652237809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981155867790441768158539 7471733801685662652237809)
          ·
            refine ⟨5603800351264246989178357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471733801685662652237809 5603800351264246989178357)
            ·
              refine ⟨525356282931023155235471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5603800351264246989178357 525356282931023155235471)
              ·
                refine ⟨788034424396534732853207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525356282931023155235471 788034424396534732853207)
                ·
                  refine ⟨1182051636594802099279811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788034424396534732853207 1182051636594802099279811)
                  ·
                    refine ⟨1773077454892203148919717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1182051636594802099279811 1773077454892203148919717)
                    ·
                      refine ⟨332452022792288090422447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1773077454892203148919717 332452022792288090422447)
                      ·
                        rfl

theorem cell23_647448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_647448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647448 prefixEnd_647448 := by exact prefixLift 647448
  have htrace : WordTrace (prefixWord ++ tailWord_647448) baseStart_647448 baseEnd_647448 := by
    simpa [prefixWord, tailWord_647448, baseEnd_647448] using wordTrace_append hprefix tailTrace_647448
  have hstable : (prefixWord ++ tailWord_647448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647448).length < 2 ^ (prefixWord ++ tailWord_647448).sum := by decide
  have hdescent : baseEnd_647448 < baseStart_647448 := by decide
  rcases family_descends (prefixWord ++ tailWord_647448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647451 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 3]
def baseStart_647451 : Nat := 118140960795 + 647451 * 2 ^ 59
def prefixEnd_647451 : Nat := 4983230072969 + 3 ^ 40 * 647451 * 2
def baseEnd_647451 : Nat := 332453563234251578684933

theorem tailTrace_647451 : CollatzResearch.WordTrace tailWord_647451 prefixEnd_647451 332453563234251578684933 := by
  unfold tailWord_647451
  simp only [CollatzResearch.WordTrace]
  refine ⟨23614477977403077672518207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15742985318268718448345471 23614477977403077672518207)
  ·
    refine ⟨35421716966104616508777311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23614477977403077672518207 35421716966104616508777311)
    ·
      refine ⟨53132575449156924763165967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35421716966104616508777311 53132575449156924763165967)
      ·
        refine ⟨79698863173735387144748951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53132575449156924763165967 79698863173735387144748951)
        ·
          refine ⟨119548294760603080717123427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79698863173735387144748951 119548294760603080717123427)
          ·
            refine ⟨179322442140904621075685141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119548294760603080717123427 179322442140904621075685141)
            ·
              refine ⟨8405739475354904112922741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179322442140904621075685141 8405739475354904112922741)
              ·
                refine ⟨788038075814522260586507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8405739475354904112922741 788038075814522260586507)
                ·
                  refine ⟨1182057113721783390879761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788038075814522260586507 1182057113721783390879761)
                  ·
                    refine ⟨886542835291337543159821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182057113721783390879761 886542835291337543159821)
                    ·
                      refine ⟨332453563234251578684933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886542835291337543159821 332453563234251578684933)
                      ·
                        rfl

theorem cell23_647451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 3].length) (baseStart_647451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647451 prefixEnd_647451 := by exact prefixLift 647451
  have htrace : WordTrace (prefixWord ++ tailWord_647451) baseStart_647451 baseEnd_647451 := by
    simpa [prefixWord, tailWord_647451, baseEnd_647451] using wordTrace_append hprefix tailTrace_647451
  have hstable : (prefixWord ++ tailWord_647451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647451).length < 2 ^ (prefixWord ++ tailWord_647451).sum := by decide
  have hdescent : baseEnd_647451 < baseStart_647451 := by decide
  rcases family_descends (prefixWord ++ tailWord_647451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647458 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_647458 : Nat := 118140960795 + 647458 * 2 ^ 59
def prefixEnd_647458 : Nat := 4983230072969 + 3 ^ 40 * 647458 * 2
def baseEnd_647458 : Nat := 110819052532944350432467

theorem tailTrace_647458 : CollatzResearch.WordTrace tailWord_647458 prefixEnd_647458 110819052532944350432467 := by
  unfold tailWord_647458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5903683322094429467005757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15743155525585145245348685 5903683322094429467005757)
  ·
    refine ⟨2213881245785411050127159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5903683322094429467005757 2213881245785411050127159)
    ·
      refine ⟨3320821868678116575190739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213881245785411050127159 3320821868678116575190739)
      ·
        refine ⟨4981232803017174862786109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3320821868678116575190739 4981232803017174862786109)
        ·
          refine ⟨1867962301131440573544791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4981232803017174862786109 1867962301131440573544791)
          ·
            refine ⟨2801943451697160860317187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867962301131440573544791 2801943451697160860317187)
            ·
              refine ⟨4202915177545741290475781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801943451697160860317187 4202915177545741290475781)
              ·
                refine ⟨788046595789826491964209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4202915177545741290475781 788046595789826491964209)
                ·
                  refine ⟨591034946842369868973157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788046595789826491964209 591034946842369868973157)
                  ·
                    refine ⟨110819052532944350432467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591034946842369868973157 110819052532944350432467)
                    ·
                      rfl

theorem cell23_647458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_647458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647458 prefixEnd_647458 := by exact prefixLift 647458
  have htrace : WordTrace (prefixWord ++ tailWord_647458) baseStart_647458 baseEnd_647458 := by
    simpa [prefixWord, tailWord_647458, baseEnd_647458] using wordTrace_append hprefix tailTrace_647458
  have hstable : (prefixWord ++ tailWord_647458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647458).length < 2 ^ (prefixWord ++ tailWord_647458).sum := by decide
  have hdescent : baseEnd_647458 < baseStart_647458 := by decide
  rcases family_descends (prefixWord ++ tailWord_647458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647484 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_647484 : Nat := 118140960795 + 647484 * 2 ^ 59
def prefixEnd_647484 : Nat := 4983230072969 + 3 ^ 40 * 647484 * 2
def baseEnd_647484 : Nat := 110823502698616649857427

theorem tailTrace_647484 : CollatzResearch.WordTrace tailWord_647484 prefixEnd_647484 110823502698616649857427 := by
  unfold tailWord_647484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807840793141762154234753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15743787724189016205646337 11807840793141762154234753)
  ·
    refine ⟨8855880594856321615676065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11807840793141762154234753 8855880594856321615676065)
    ·
      refine ⟨6641910446142241211757049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8855880594856321615676065 6641910446142241211757049)
      ·
        refine ⟨4981432834606680908817787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6641910446142241211757049 4981432834606680908817787)
        ·
          refine ⟨7472149251910021363226681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981432834606680908817787 7472149251910021363226681)
          ·
            refine ⟨5604111938932516022420011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7472149251910021363226681 5604111938932516022420011)
            ·
              refine ⟨8406167908398774033630017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604111938932516022420011 8406167908398774033630017)
              ·
                refine ⟨6304625931299080525222513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8406167908398774033630017 6304625931299080525222513)
                ·
                  refine ⟨4728469448474310393916885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6304625931299080525222513 4728469448474310393916885)
                  ·
                    refine ⟨110823502698616649857427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4728469448474310393916885 110823502698616649857427)
                    ·
                      rfl

theorem cell23_647484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_647484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647484 prefixEnd_647484 := by exact prefixLift 647484
  have htrace : WordTrace (prefixWord ++ tailWord_647484) baseStart_647484 baseEnd_647484 := by
    simpa [prefixWord, tailWord_647484, baseEnd_647484] using wordTrace_append hprefix tailTrace_647484
  have hstable : (prefixWord ++ tailWord_647484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647484).length < 2 ^ (prefixWord ++ tailWord_647484).sum := by decide
  have hdescent : baseEnd_647484 < baseStart_647484 := by decide
  rcases family_descends (prefixWord ++ tailWord_647484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647521 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_647521 : Nat := 118140960795 + 647521 * 2 ^ 59
def prefixEnd_647521 : Nat := 4983230072969 + 3 ^ 40 * 647521 * 2
def baseEnd_647521 : Nat := 332489506880066304809611

theorem tailTrace_647521 : CollatzResearch.WordTrace tailWord_647521 prefixEnd_647521 332489506880066304809611 := by
  unfold tailWord_647521
  simp only [CollatzResearch.WordTrace]
  refine ⟨23617031087149479627566417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15744687391432986418377611 23617031087149479627566417)
  ·
    refine ⟨17712773315362109720674813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23617031087149479627566417 17712773315362109720674813)
    ·
      refine ⟨6642289993260791145253055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17712773315362109720674813 6642289993260791145253055)
      ·
        refine ⟨9963434989891186717879583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6642289993260791145253055 9963434989891186717879583)
        ·
          refine ⟨14945152484836780076819375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9963434989891186717879583 14945152484836780076819375)
          ·
            refine ⟨22417728727255170115229063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14945152484836780076819375 22417728727255170115229063)
            ·
              refine ⟨33626593090882755172843595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22417728727255170115229063 33626593090882755172843595)
              ·
                refine ⟨50439889636324132759265393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33626593090882755172843595 50439889636324132759265393)
                ·
                  refine ⟨37829917227243099569449045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50439889636324132759265393 37829917227243099569449045)
                  ·
                    refine ⟨443319342506755073079481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37829917227243099569449045 443319342506755073079481)
                    ·
                      refine ⟨332489506880066304809611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443319342506755073079481 332489506880066304809611)
                      ·
                        rfl

theorem cell23_647521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_647521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647521 prefixEnd_647521 := by exact prefixLift 647521
  have htrace : WordTrace (prefixWord ++ tailWord_647521) baseStart_647521 baseEnd_647521 := by
    simpa [prefixWord, tailWord_647521, baseEnd_647521] using wordTrace_append hprefix tailTrace_647521
  have hstable : (prefixWord ++ tailWord_647521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647521).length < 2 ^ (prefixWord ++ tailWord_647521).sum := by decide
  have hdescent : baseEnd_647521 < baseStart_647521 := by decide
  rcases family_descends (prefixWord ++ tailWord_647521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647532 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 3]
def baseStart_647532 : Nat := 118140960795 + 647532 * 2 ^ 59
def prefixEnd_647532 : Nat := 4983230072969 + 3 ^ 40 * 647532 * 2
def baseEnd_647532 : Nat := 332495155167265761772061

theorem tailTrace_647532 : CollatzResearch.WordTrace tailWord_647532 prefixEnd_647532 332495155167265761772061 := by
  unfold tailWord_647532
  simp only [CollatzResearch.WordTrace]
  refine ⟨11808716145054814253108425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15744954860073085670811233 11808716145054814253108425)
  ·
    refine ⟨8856537108791110689831319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11808716145054814253108425 8856537108791110689831319)
    ·
      refine ⟨13284805663186666034746979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8856537108791110689831319 13284805663186666034746979)
      ·
        refine ⟨19927208494779999052120469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13284805663186666034746979 19927208494779999052120469)
        ·
          refine ⟨934087898192812455568147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19927208494779999052120469 934087898192812455568147)
          ·
            refine ⟨1401131847289218683352221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934087898192812455568147 1401131847289218683352221)
            ·
              refine ⟨525424442733457006257083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1401131847289218683352221 525424442733457006257083)
              ·
                refine ⟨788136664100185509385625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525424442733457006257083 788136664100185509385625)
                ·
                  refine ⟨591102498075139132039219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788136664100185509385625 591102498075139132039219)
                  ·
                    refine ⟨886653747112708698058829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 591102498075139132039219 886653747112708698058829)
                    ·
                      refine ⟨332495155167265761772061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886653747112708698058829 332495155167265761772061)
                      ·
                        rfl

theorem cell23_647532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_647532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647532 prefixEnd_647532 := by exact prefixLift 647532
  have htrace : WordTrace (prefixWord ++ tailWord_647532) baseStart_647532 baseEnd_647532 := by
    simpa [prefixWord, tailWord_647532, baseEnd_647532] using wordTrace_append hprefix tailTrace_647532
  have hstable : (prefixWord ++ tailWord_647532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647532).length < 2 ^ (prefixWord ++ tailWord_647532).sum := by decide
  have hdescent : baseEnd_647532 < baseStart_647532 := by decide
  rcases family_descends (prefixWord ++ tailWord_647532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647578 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 7]
def baseStart_647578 : Nat := 118140960795 + 647578 * 2 ^ 59
def prefixEnd_647578 : Nat := 4983230072969 + 3 ^ 40 * 647578 * 2
def baseEnd_647578 : Nat := 36946530586374731310761

theorem tailTrace_647578 : CollatzResearch.WordTrace tailWord_647578 prefixEnd_647578 36946530586374731310761 := by
  unfold tailWord_647578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904777511985744590597847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15746073365295318908260925 5904777511985744590597847)
  ·
    refine ⟨8857166267978616885896771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5904777511985744590597847 8857166267978616885896771)
    ·
      refine ⟨13285749401967925328845157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8857166267978616885896771 13285749401967925328845157)
      ·
        refine ⟨2491078012868985999158467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13285749401967925328845157 2491078012868985999158467)
        ·
          refine ⟨3736617019303478998737701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491078012868985999158467 3736617019303478998737701)
          ·
            refine ⟨700615691119402312263319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3736617019303478998737701 700615691119402312263319)
            ·
              refine ⟨1050923536679103468394979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700615691119402312263319 1050923536679103468394979)
              ·
                refine ⟨1576385305018655202592469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050923536679103468394979 1576385305018655202592469)
                ·
                  refine ⟨36946530586374731310761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1576385305018655202592469 36946530586374731310761)
                  ·
                    rfl

theorem cell23_647578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_647578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647578 prefixEnd_647578 := by exact prefixLift 647578
  have htrace : WordTrace (prefixWord ++ tailWord_647578) baseStart_647578 baseEnd_647578 := by
    simpa [prefixWord, tailWord_647578, baseEnd_647578] using wordTrace_append hprefix tailTrace_647578
  have hstable : (prefixWord ++ tailWord_647578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647578).length < 2 ^ (prefixWord ++ tailWord_647578).sum := by decide
  have hdescent : baseEnd_647578 < baseStart_647578 := by decide
  rcases family_descends (prefixWord ++ tailWord_647578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647631 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 3]
def baseStart_647631 : Nat := 118140960795 + 647631 * 2 ^ 59
def prefixEnd_647631 : Nat := 4983230072969 + 3 ^ 40 * 647631 * 2
def baseEnd_647631 : Nat := 332545989752060874434105

theorem tailTrace_647631 : CollatzResearch.WordTrace tailWord_647631 prefixEnd_647631 332545989752060874434105 := by
  unfold tailWord_647631
  simp only [CollatzResearch.WordTrace]
  refine ⟨23621043116750968414070747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15747362077833978942713831 23621043116750968414070747)
  ·
    refine ⟨35431564675126452621106121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23621043116750968414070747 35431564675126452621106121)
    ·
      refine ⟨26573673506344839465829591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35431564675126452621106121 26573673506344839465829591)
      ·
        refine ⟨39860510259517259198744387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26573673506344839465829591 39860510259517259198744387)
        ·
          refine ⟨59790765389275888798116581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39860510259517259198744387 59790765389275888798116581)
          ·
            refine ⟨11210768510489229149646859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59790765389275888798116581 11210768510489229149646859)
            ·
              refine ⟨16816152765733843724470289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11210768510489229149646859 16816152765733843724470289)
              ·
                refine ⟨12612114574300382793352717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16816152765733843724470289 12612114574300382793352717)
                ·
                  refine ⟨4729542965362643547507269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12612114574300382793352717 4729542965362643547507269)
                  ·
                    refine ⟨886789306005495665157613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4729542965362643547507269 886789306005495665157613)
                    ·
                      refine ⟨332545989752060874434105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886789306005495665157613 332545989752060874434105)
                      ·
                        rfl

theorem cell23_647631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_647631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647631 prefixEnd_647631 := by exact prefixLift 647631
  have htrace : WordTrace (prefixWord ++ tailWord_647631) baseStart_647631 baseEnd_647631 := by
    simpa [prefixWord, tailWord_647631, baseEnd_647631] using wordTrace_append hprefix tailTrace_647631
  have hstable : (prefixWord ++ tailWord_647631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647631).length < 2 ^ (prefixWord ++ tailWord_647631).sum := by decide
  have hdescent : baseEnd_647631 < baseStart_647631 := by decide
  rcases family_descends (prefixWord ++ tailWord_647631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647645 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_647645 : Nat := 118140960795 + 647645 * 2 ^ 59
def prefixEnd_647645 : Nat := 4983230072969 + 3 ^ 40 * 647645 * 2
def baseEnd_647645 : Nat := 332553178481223819659041

theorem tailTrace_647645 : CollatzResearch.WordTrace tailWord_647645 prefixEnd_647645 332553178481223819659041 := by
  unfold tailWord_647645
  simp only [CollatzResearch.WordTrace]
  refine ⟨23621553738700248805080389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15747702492466832536720259 23621553738700248805080389)
  ·
    refine ⟨4429041326006296650952573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23621553738700248805080389 4429041326006296650952573)
    ·
      refine ⟨1660890497252361244107215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4429041326006296650952573 1660890497252361244107215)
      ·
        refine ⟨2491335745878541866160823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660890497252361244107215 2491335745878541866160823)
        ·
          refine ⟨3737003618817812799241235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491335745878541866160823 3737003618817812799241235)
          ·
            refine ⟨5605505428226719198861853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737003618817812799241235 5605505428226719198861853)
            ·
              refine ⟨2102064535585019699573195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5605505428226719198861853 2102064535585019699573195)
              ·
                refine ⟨3153096803377529549359793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102064535585019699573195 3153096803377529549359793)
                ·
                  refine ⟨2364822602533147162019845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153096803377529549359793 2364822602533147162019845)
                  ·
                    refine ⟨443404237974965092878721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364822602533147162019845 443404237974965092878721)
                    ·
                      refine ⟨332553178481223819659041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443404237974965092878721 332553178481223819659041)
                      ·
                        rfl

theorem cell23_647645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_647645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647645 prefixEnd_647645 := by exact prefixLift 647645
  have htrace : WordTrace (prefixWord ++ tailWord_647645) baseStart_647645 baseEnd_647645 := by
    simpa [prefixWord, tailWord_647645, baseEnd_647645] using wordTrace_append hprefix tailTrace_647645
  have hstable : (prefixWord ++ tailWord_647645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647645).length < 2 ^ (prefixWord ++ tailWord_647645).sum := by decide
  have hdescent : baseEnd_647645 < baseStart_647645 := by decide
  rcases family_descends (prefixWord ++ tailWord_647645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647715 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 1, 5]
def baseStart_647715 : Nat := 118140960795 + 647715 * 2 ^ 59
def prefixEnd_647715 : Nat := 4983230072969 + 3 ^ 40 * 647715 * 2
def baseEnd_647715 : Nat := 110863040709012848594573

theorem tailTrace_647715 : CollatzResearch.WordTrace tailWord_647715 prefixEnd_647715 110863040709012848594573 := by
  unfold tailWord_647715
  simp only [CollatzResearch.WordTrace]
  refine ⟨23624106848446650760128599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15749404565631100506752399 23624106848446650760128599)
  ·
    refine ⟨35436160272669976140192899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23624106848446650760128599 35436160272669976140192899)
    ·
      refine ⟨53154240409004964210289349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35436160272669976140192899 53154240409004964210289349)
      ·
        refine ⟨9966420076688430789429253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53154240409004964210289349 9966420076688430789429253)
        ·
          refine ⟨1868703764379080773017985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9966420076688430789429253 1868703764379080773017985)
          ·
            refine ⟨1401527823284310579763489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1868703764379080773017985 1401527823284310579763489)
            ·
              refine ⟨1051145867463232934822617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401527823284310579763489 1051145867463232934822617)
              ·
                refine ⟨788359400597424701116963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051145867463232934822617 788359400597424701116963)
                ·
                  refine ⟨1182539100896137051675445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788359400597424701116963 1182539100896137051675445)
                  ·
                    refine ⟨110863040709012848594573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1182539100896137051675445 110863040709012848594573)
                    ·
                      rfl

theorem cell23_647715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 5].length) (baseStart_647715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647715 prefixEnd_647715 := by exact prefixLift 647715
  have htrace : WordTrace (prefixWord ++ tailWord_647715) baseStart_647715 baseEnd_647715 := by
    simpa [prefixWord, tailWord_647715, baseEnd_647715] using wordTrace_append hprefix tailTrace_647715
  have hstable : (prefixWord ++ tailWord_647715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647715).length < 2 ^ (prefixWord ++ tailWord_647715).sum := by decide
  have hdescent : baseEnd_647715 < baseStart_647715 := by decide
  rcases family_descends (prefixWord ++ tailWord_647715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647728 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 4, 4]
def baseStart_647728 : Nat := 118140960795 + 647728 * 2 ^ 59
def prefixEnd_647728 : Nat := 4983230072969 + 3 ^ 40 * 647728 * 2
def baseEnd_647728 : Nat := 110865265791848998307053

theorem tailTrace_647728 : CollatzResearch.WordTrace tailWord_647728 prefixEnd_647728 110865265791848998307053 := by
  unfold tailWord_647728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11812290498699776990175919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15749720664933035986901225 11812290498699776990175919)
  ·
    refine ⟨17718435748049665485263879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11812290498699776990175919 17718435748049665485263879)
    ·
      refine ⟨26577653622074498227895819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17718435748049665485263879 26577653622074498227895819)
      ·
        refine ⟨39866480433111747341843729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26577653622074498227895819 39866480433111747341843729)
        ·
          refine ⟨29899860324833810506382797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39866480433111747341843729 29899860324833810506382797)
          ·
            refine ⟨11212447621812678939893549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29899860324833810506382797 11212447621812678939893549)
            ·
              refine ⟨4204667858179754602460081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11212447621812678939893549 4204667858179754602460081)
              ·
                refine ⟨3153500893634815951845061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204667858179754602460081 3153500893634815951845061)
                ·
                  refine ⟨591281417556527990970949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3153500893634815951845061 591281417556527990970949)
                  ·
                    refine ⟨110865265791848998307053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591281417556527990970949 110865265791848998307053)
                    ·
                      rfl

theorem cell23_647728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_647728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647728 prefixEnd_647728 := by exact prefixLift 647728
  have htrace : WordTrace (prefixWord ++ tailWord_647728) baseStart_647728 baseEnd_647728 := by
    simpa [prefixWord, tailWord_647728, baseEnd_647728] using wordTrace_append hprefix tailTrace_647728
  have hstable : (prefixWord ++ tailWord_647728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647728).length < 2 ^ (prefixWord ++ tailWord_647728).sum := by decide
  have hdescent : baseEnd_647728 < baseStart_647728 := by decide
  rcases family_descends (prefixWord ++ tailWord_647728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647738 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_647738 : Nat := 118140960795 + 647738 * 2 ^ 59
def prefixEnd_647738 : Nat := 4983230072969 + 3 ^ 40 * 647738 * 2
def baseEnd_647738 : Nat := 332600932182091955796113

theorem tailTrace_647738 : CollatzResearch.WordTrace tailWord_647738 prefixEnd_647738 332600932182091955796113 := by
  unfold tailWord_647738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906236431840831422053967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15749963818242217125477245 5906236431840831422053967)
  ·
    refine ⟨8859354647761247133080951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5906236431840831422053967 8859354647761247133080951)
    ·
      refine ⟨13289031971641870699621427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8859354647761247133080951 13289031971641870699621427)
      ·
        refine ⟨19933547957462806049432141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289031971641870699621427 19933547957462806049432141)
        ·
          refine ⟨7475080484048552268537053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19933547957462806049432141 7475080484048552268537053)
          ·
            refine ⟨2803155181518207100701395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7475080484048552268537053 2803155181518207100701395)
            ·
              refine ⟨4204732772277310651052093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803155181518207100701395 4204732772277310651052093)
              ·
                refine ⟨1576774789603991494144535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4204732772277310651052093 1576774789603991494144535)
                ·
                  refine ⟨2365162184405987241216803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576774789603991494144535 2365162184405987241216803)
                  ·
                    refine ⟨3547743276608980861825205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2365162184405987241216803 3547743276608980861825205)
                    ·
                      refine ⟨332600932182091955796113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3547743276608980861825205 332600932182091955796113)
                      ·
                        rfl

theorem cell23_647738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_647738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647738 prefixEnd_647738 := by exact prefixLift 647738
  have htrace : WordTrace (prefixWord ++ tailWord_647738) baseStart_647738 baseEnd_647738 := by
    simpa [prefixWord, tailWord_647738, baseEnd_647738] using wordTrace_append hprefix tailTrace_647738
  have hstable : (prefixWord ++ tailWord_647738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647738).length < 2 ^ (prefixWord ++ tailWord_647738).sum := by decide
  have hdescent : baseEnd_647738 < baseStart_647738 := by decide
  rcases family_descends (prefixWord ++ tailWord_647738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647745 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 4, 4]
def baseStart_647745 : Nat := 118140960795 + 647745 * 2 ^ 59
def prefixEnd_647745 : Nat := 4983230072969 + 3 ^ 40 * 647745 * 2
def baseEnd_647745 : Nat := 110868175515557809469527

theorem tailTrace_647745 : CollatzResearch.WordTrace tailWord_647745 prefixEnd_647745 110868175515557809469527 := by
  unfold tailWord_647745
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625201038337965883720689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15750134025558643922480459 23625201038337965883720689)
  ·
    refine ⟨17718900778753474412790517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23625201038337965883720689 17718900778753474412790517)
    ·
      refine ⟨1661146948008138226199111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17718900778753474412790517 1661146948008138226199111)
      ·
        refine ⟨2491720422012207339298667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661146948008138226199111 2491720422012207339298667)
        ·
          refine ⟨3737580633018311008948001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491720422012207339298667 3737580633018311008948001)
          ·
            refine ⟨2803185474763733256711001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3737580633018311008948001 2803185474763733256711001)
            ·
              refine ⟨2102389106072799942533251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803185474763733256711001 2102389106072799942533251)
              ·
                refine ⟨3153583659109199913799877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102389106072799942533251 3153583659109199913799877)
                ·
                  refine ⟨591296936082974983837477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3153583659109199913799877 591296936082974983837477)
                  ·
                    refine ⟨110868175515557809469527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591296936082974983837477 110868175515557809469527)
                    ·
                      rfl

theorem cell23_647745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_647745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647745 prefixEnd_647745 := by exact prefixLift 647745
  have htrace : WordTrace (prefixWord ++ tailWord_647745) baseStart_647745 baseEnd_647745 := by
    simpa [prefixWord, tailWord_647745, baseEnd_647745] using wordTrace_append hprefix tailTrace_647745
  have hstable : (prefixWord ++ tailWord_647745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647745).length < 2 ^ (prefixWord ++ tailWord_647745).sum := by decide
  have hdescent : baseEnd_647745 < baseStart_647745 := by decide
  rcases family_descends (prefixWord ++ tailWord_647745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647772 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_647772 : Nat := 118140960795 + 647772 * 2 ^ 59
def prefixEnd_647772 : Nat := 4983230072969 + 3 ^ 40 * 647772 * 2
def baseEnd_647772 : Nat := 332618390524344822770957

theorem tailTrace_647772 : CollatzResearch.WordTrace tailWord_647772 prefixEnd_647772 332618390524344822770957 := by
  unfold tailWord_647772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813092904620074747476785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15750790539493432996635713 11813092904620074747476785)
  ·
    refine ⟨8859819678465056060607589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11813092904620074747476785 8859819678465056060607589)
    ·
      refine ⟨1661216189712198011363923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8859819678465056060607589 1661216189712198011363923)
      ·
        refine ⟨2491824284568297017045885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661216189712198011363923 2491824284568297017045885)
        ·
          refine ⟨934434106713111381392207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2491824284568297017045885 934434106713111381392207)
          ·
            refine ⟨1401651160069667072088311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934434106713111381392207 1401651160069667072088311)
            ·
              refine ⟨2102476740104500608132467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401651160069667072088311 2102476740104500608132467)
              ·
                refine ⟨3153715110156750912198701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102476740104500608132467 3153715110156750912198701)
                ·
                  refine ⟨1182643166308781592074513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3153715110156750912198701 1182643166308781592074513)
                  ·
                    refine ⟨886982374731586194055885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182643166308781592074513 886982374731586194055885)
                    ·
                      refine ⟨332618390524344822770957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 886982374731586194055885 332618390524344822770957)
                      ·
                        rfl

theorem cell23_647772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_647772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647772 prefixEnd_647772 := by exact prefixLift 647772
  have htrace : WordTrace (prefixWord ++ tailWord_647772) baseStart_647772 baseEnd_647772 := by
    simpa [prefixWord, tailWord_647772, baseEnd_647772] using wordTrace_append hprefix tailTrace_647772
  have hstable : (prefixWord ++ tailWord_647772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647772).length < 2 ^ (prefixWord ++ tailWord_647772).sum := by decide
  have hdescent : baseEnd_647772 < baseStart_647772 := by decide
  rcases family_descends (prefixWord ++ tailWord_647772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647789 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_647789 : Nat := 118140960795 + 647789 * 2 ^ 59
def prefixEnd_647789 : Nat := 4983230072969 + 3 ^ 40 * 647789 * 2
def baseEnd_647789 : Nat := 332627119695471256258379

theorem tailTrace_647789 : CollatzResearch.WordTrace tailWord_647789 prefixEnd_647789 332627119695471256258379 := by
  unfold tailWord_647789
  simp only [CollatzResearch.WordTrace]
  refine ⟨23626805850178561398322421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15751203900119040932214947 23626805850178561398322421)
  ·
    refine ⟨2215013048454240131092727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23626805850178561398322421 2215013048454240131092727)
    ·
      refine ⟨3322519572681360196639091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215013048454240131092727 3322519572681360196639091)
      ·
        refine ⟨4983779359022040294958637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3322519572681360196639091 4983779359022040294958637)
        ·
          refine ⟨1868917259633265110609489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4983779359022040294958637 1868917259633265110609489)
          ·
            refine ⟨1401687944724948832957117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1868917259633265110609489 1401687944724948832957117)
            ·
              refine ⟨525632979271855812358919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1401687944724948832957117 525632979271855812358919)
              ·
                refine ⟨788449468907783718538379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525632979271855812358919 788449468907783718538379)
                ·
                  refine ⟨1182674203361675577807569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788449468907783718538379 1182674203361675577807569)
                  ·
                    refine ⟨887005652521256683355677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182674203361675577807569 887005652521256683355677)
                    ·
                      refine ⟨332627119695471256258379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 887005652521256683355677 332627119695471256258379)
                      ·
                        rfl

theorem cell23_647789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_647789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647789 prefixEnd_647789 := by exact prefixLift 647789
  have htrace : WordTrace (prefixWord ++ tailWord_647789) baseStart_647789 baseEnd_647789 := by
    simpa [prefixWord, tailWord_647789, baseEnd_647789] using wordTrace_append hprefix tailTrace_647789
  have hstable : (prefixWord ++ tailWord_647789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647789).length < 2 ^ (prefixWord ++ tailWord_647789).sum := by decide
  have hdescent : baseEnd_647789 < baseStart_647789 := by decide
  rcases family_descends (prefixWord ++ tailWord_647789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647808 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_647808 : Nat := 118140960795 + 647808 * 2 ^ 59
def prefixEnd_647808 : Nat := 4983230072969 + 3 ^ 40 * 647808 * 2
def baseEnd_647808 : Nat := 332636875827906681920791

theorem tailTrace_647808 : CollatzResearch.WordTrace tailWord_647808 prefixEnd_647808 332636875827906681920791 := by
  unfold tailWord_647808
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813749418554863821632039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15751665891406485095509385 11813749418554863821632039)
  ·
    refine ⟨17720624127832295732448059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11813749418554863821632039 17720624127832295732448059)
    ·
      refine ⟨26580936191748443598672089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17720624127832295732448059 26580936191748443598672089)
      ·
        refine ⟨19935702143811332699004067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26580936191748443598672089 19935702143811332699004067)
        ·
          refine ⟨29903553215716999048506101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19935702143811332699004067 29903553215716999048506101)
          ·
            refine ⟨2803458113973468660797447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29903553215716999048506101 2803458113973468660797447)
            ·
              refine ⟨4205187170960202991196171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803458113973468660797447 4205187170960202991196171)
              ·
                refine ⟨6307780756440304486794257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4205187170960202991196171 6307780756440304486794257)
                ·
                  refine ⟨4730835567330228365095693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6307780756440304486794257 4730835567330228365095693)
                  ·
                    refine ⟨1774063337748835636910885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4730835567330228365095693 1774063337748835636910885)
                    ·
                      refine ⟨332636875827906681920791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1774063337748835636910885 332636875827906681920791)
                      ·
                        rfl

theorem cell23_647808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_647808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647808 prefixEnd_647808 := by exact prefixLift 647808
  have htrace : WordTrace (prefixWord ++ tailWord_647808) baseStart_647808 baseEnd_647808 := by
    simpa [prefixWord, tailWord_647808, baseEnd_647808] using wordTrace_append hprefix tailTrace_647808
  have hstable : (prefixWord ++ tailWord_647808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647808).length < 2 ^ (prefixWord ++ tailWord_647808).sum := by decide
  have hdescent : baseEnd_647808 < baseStart_647808 := by decide
  rcases family_descends (prefixWord ++ tailWord_647808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647812 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_647812 : Nat := 118140960795 + 647812 * 2 ^ 59
def prefixEnd_647812 : Nat := 4983230072969 + 3 ^ 40 * 647812 * 2
def baseEnd_647812 : Nat := 332638929750524666270773

theorem tailTrace_647812 : CollatzResearch.WordTrace tailWord_647812 prefixEnd_647812 332638929750524666270773 := by
  unfold tailWord_647812
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813822364547618163204845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15751763152730157550939793 11813822364547618163204845)
  ·
    refine ⟨4430183386705356811201817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11813822364547618163204845 4430183386705356811201817)
    ·
      refine ⟨3322637540029017608401363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4430183386705356811201817 3322637540029017608401363)
      ·
        refine ⟨4983956310043526412602045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3322637540029017608401363 4983956310043526412602045)
        ·
          refine ⟨1868983616266322404725767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4983956310043526412602045 1868983616266322404725767)
          ·
            refine ⟨2803475424399483607088651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868983616266322404725767 2803475424399483607088651)
            ·
              refine ⟨4205213136599225410632977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803475424399483607088651 4205213136599225410632977)
              ·
                refine ⟨3153909852449419057974733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205213136599225410632977 3153909852449419057974733)
                ·
                  refine ⟨1182716194668532146740525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3153909852449419057974733 1182716194668532146740525)
                  ·
                    refine ⟨443518573000699555027697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1182716194668532146740525 443518573000699555027697)
                    ·
                      refine ⟨332638929750524666270773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443518573000699555027697 332638929750524666270773)
                      ·
                        rfl

theorem cell23_647812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_647812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647812 prefixEnd_647812 := by exact prefixLift 647812
  have htrace : WordTrace (prefixWord ++ tailWord_647812) baseStart_647812 baseEnd_647812 := by
    simpa [prefixWord, tailWord_647812, baseEnd_647812] using wordTrace_append hprefix tailTrace_647812
  have hstable : (prefixWord ++ tailWord_647812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647812).length < 2 ^ (prefixWord ++ tailWord_647812).sum := by decide
  have hdescent : baseEnd_647812 < baseStart_647812 := by decide
  rcases family_descends (prefixWord ++ tailWord_647812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647859 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 2, 2, 2]
def baseStart_647859 : Nat := 118140960795 + 647859 * 2 ^ 59
def prefixEnd_647859 : Nat := 4983230072969 + 3 ^ 40 * 647859 * 2
def baseEnd_647859 : Nat := 332663063341285982383057

theorem tailTrace_647859 : CollatzResearch.WordTrace tailWord_647859 prefixEnd_647859 332663063341285982383057 := by
  unfold tailWord_647859
  simp only [CollatzResearch.WordTrace]
  refine ⟨23629358959924963353370631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15752905973283308902247087 23629358959924963353370631)
  ·
    refine ⟨35444038439887445030055947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23629358959924963353370631 35444038439887445030055947)
    ·
      refine ⟨53166057659831167545083921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35444038439887445030055947 53166057659831167545083921)
      ·
        refine ⟨39874543244873375658812941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53166057659831167545083921 39874543244873375658812941)
        ·
          refine ⟨14952953716827515872054853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39874543244873375658812941 14952953716827515872054853)
          ·
            refine ⟨2803678821905159226010285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14952953716827515872054853 2803678821905159226010285)
            ·
              refine ⟨1051379558214434709753857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2803678821905159226010285 1051379558214434709753857)
              ·
                refine ⟨788534668660826032315393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051379558214434709753857 788534668660826032315393)
                ·
                  refine ⟨591401001495619524236545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788534668660826032315393 591401001495619524236545)
                  ·
                    refine ⟨443550751121714643177409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 591401001495619524236545 443550751121714643177409)
                    ·
                      refine ⟨332663063341285982383057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443550751121714643177409 332663063341285982383057)
                      ·
                        rfl

theorem cell23_647859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 2, 2].length) (baseStart_647859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647859 prefixEnd_647859 := by exact prefixLift 647859
  have htrace : WordTrace (prefixWord ++ tailWord_647859) baseStart_647859 baseEnd_647859 := by
    simpa [prefixWord, tailWord_647859, baseEnd_647859] using wordTrace_append hprefix tailTrace_647859
  have hstable : (prefixWord ++ tailWord_647859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647859).length < 2 ^ (prefixWord ++ tailWord_647859).sum := by decide
  have hdescent : baseEnd_647859 < baseStart_647859 := by decide
  rcases family_descends (prefixWord ++ tailWord_647859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647912 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 2, 5]
def baseStart_647912 : Nat := 118140960795 + 647912 * 2 ^ 59
def prefixEnd_647912 : Nat := 4983230072969 + 3 ^ 40 * 647912 * 2
def baseEnd_647912 : Nat := 110896759271991425006771

theorem tailTrace_647912 : CollatzResearch.WordTrace tailWord_647912 prefixEnd_647912 110896759271991425006771 := by
  unfold tailWord_647912
  simp only [CollatzResearch.WordTrace]
  refine ⟨11815646014366476702524995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15754194685821968936699993 11815646014366476702524995)
  ·
    refine ⟨17723469021549715053787493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11815646014366476702524995 17723469021549715053787493)
    ·
      refine ⟨3323150441540571572585155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17723469021549715053787493 3323150441540571572585155)
      ·
        refine ⟨4984725662310857358877733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3323150441540571572585155 4984725662310857358877733)
        ·
          refine ⟨934636061683285754789575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4984725662310857358877733 934636061683285754789575)
          ·
            refine ⟨1401954092524928632184363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934636061683285754789575 1401954092524928632184363)
            ·
              refine ⟨2102931138787392948276545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401954092524928632184363 2102931138787392948276545)
              ·
                refine ⟨1577198354090544711207409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102931138787392948276545 1577198354090544711207409)
                ·
                  refine ⟨1182898765567908533405557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1577198354090544711207409 1182898765567908533405557)
                  ·
                    refine ⟨110896759271991425006771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1182898765567908533405557 110896759271991425006771)
                    ·
                      rfl

theorem cell23_647912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_647912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647912 prefixEnd_647912 := by exact prefixLift 647912
  have htrace : WordTrace (prefixWord ++ tailWord_647912) baseStart_647912 baseEnd_647912 := by
    simpa [prefixWord, tailWord_647912, baseEnd_647912] using wordTrace_append hprefix tailTrace_647912
  have hstable : (prefixWord ++ tailWord_647912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647912).length < 2 ^ (prefixWord ++ tailWord_647912).sum := by decide
  have hdescent : baseEnd_647912 < baseStart_647912 := by decide
  rcases family_descends (prefixWord ++ tailWord_647912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647935 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 3]
def baseStart_647935 : Nat := 118140960795 + 647935 * 2 ^ 59
def prefixEnd_647935 : Nat := 4983230072969 + 3 ^ 40 * 647935 * 2
def baseEnd_647935 : Nat := 332702087871027685032707

theorem tailTrace_647935 : CollatzResearch.WordTrace tailWord_647935 prefixEnd_647935 332702087871027685032707 := by
  unfold tailWord_647935
  simp only [CollatzResearch.WordTrace]
  refine ⟨23632130907649628333137259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15754753938433085555424839 23632130907649628333137259)
  ·
    refine ⟨35448196361474442499705889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23632130907649628333137259 35448196361474442499705889)
    ·
      refine ⟨26586147271105831874779417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35448196361474442499705889 26586147271105831874779417)
      ·
        refine ⟨19939610453329373906084563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26586147271105831874779417 19939610453329373906084563)
        ·
          refine ⟨29909415679994060859126845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19939610453329373906084563 29909415679994060859126845)
          ·
            refine ⟨11216030879997772822172567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29909415679994060859126845 11216030879997772822172567)
            ·
              refine ⟨16824046319996659233258851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11216030879997772822172567 16824046319996659233258851)
              ·
                refine ⟨25236069479994988849888277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16824046319996659233258851 25236069479994988849888277)
                ·
                  refine ⟨1182940756874765102338513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25236069479994988849888277 1182940756874765102338513)
                  ·
                    refine ⟨887205567656073826753885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182940756874765102338513 887205567656073826753885)
                    ·
                      refine ⟨332702087871027685032707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 887205567656073826753885 332702087871027685032707)
                      ·
                        rfl

theorem cell23_647935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_647935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647935 prefixEnd_647935 := by exact prefixLift 647935
  have htrace : WordTrace (prefixWord ++ tailWord_647935) baseStart_647935 baseEnd_647935 := by
    simpa [prefixWord, tailWord_647935, baseEnd_647935] using wordTrace_append hprefix tailTrace_647935
  have hstable : (prefixWord ++ tailWord_647935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647935).length < 2 ^ (prefixWord ++ tailWord_647935).sum := by decide
  have hdescent : baseEnd_647935 < baseStart_647935 := by decide
  rcases family_descends (prefixWord ++ tailWord_647935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647985 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 5, 5]
def baseStart_647985 : Nat := 118140960795 + 647985 * 2 ^ 59
def prefixEnd_647985 : Nat := 4983230072969 + 3 ^ 40 * 647985 * 2
def baseEnd_647985 : Nat := 110909253967917496469159

theorem tailTrace_647985 : CollatzResearch.WordTrace tailWord_647985 prefixEnd_647985 110909253967917496469159 := by
  unfold tailWord_647985
  simp only [CollatzResearch.WordTrace]
  refine ⟨23633954557468486872457409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15755969704978991248304939 23633954557468486872457409)
  ·
    refine ⟨17725465918101365154343057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23633954557468486872457409 17725465918101365154343057)
    ·
      refine ⟨13294099438576023865757293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17725465918101365154343057 13294099438576023865757293)
      ·
        refine ⟨4985287289466008949658985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13294099438576023865757293 4985287289466008949658985)
        ·
          refine ⟨3738965467099506712244239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4985287289466008949658985 3738965467099506712244239)
          ·
            refine ⟨5608448200649260068366359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738965467099506712244239 5608448200649260068366359)
            ·
              refine ⟨8412672300973890102549539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608448200649260068366359 8412672300973890102549539)
              ·
                refine ⟨12619008451460835153824309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412672300973890102549539 12619008451460835153824309)
                ·
                  refine ⟨1183032042324453295671029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12619008451460835153824309 1183032042324453295671029)
                  ·
                    refine ⟨110909253967917496469159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1183032042324453295671029 110909253967917496469159)
                    ·
                      rfl

theorem cell23_647985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_647985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647985 prefixEnd_647985 := by exact prefixLift 647985
  have htrace : WordTrace (prefixWord ++ tailWord_647985) baseStart_647985 baseEnd_647985 := by
    simpa [prefixWord, tailWord_647985, baseEnd_647985] using wordTrace_append hprefix tailTrace_647985
  have hstable : (prefixWord ++ tailWord_647985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647985).length < 2 ^ (prefixWord ++ tailWord_647985).sum := by decide
  have hdescent : baseEnd_647985 < baseStart_647985 := by decide
  rcases family_descends (prefixWord ++ tailWord_647985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647992 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 1, 5, 2]
def baseStart_647992 : Nat := 118140960795 + 647992 * 2 ^ 59
def prefixEnd_647992 : Nat := 4983230072969 + 3 ^ 40 * 647992 * 2
def baseEnd_647992 : Nat := 332731356268333962019945

theorem tailTrace_647992 : CollatzResearch.WordTrace tailWord_647992 prefixEnd_647992 332731356268333962019945 := by
  unfold tailWord_647992
  simp only [CollatzResearch.WordTrace]
  refine ⟨11817104934221563533981115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15756139912295418045308153 11817104934221563533981115)
  ·
    refine ⟨17725657401332345300971673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11817104934221563533981115 17725657401332345300971673)
    ·
      refine ⟨13294243050999258975728755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17725657401332345300971673 13294243050999258975728755)
      ·
        refine ⟨19941364576498888463593133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294243050999258975728755 19941364576498888463593133)
        ·
          refine ⟨7478011716187083173847425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19941364576498888463593133 7478011716187083173847425)
          ·
            refine ⟨5608508787140312380385569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7478011716187083173847425 5608508787140312380385569)
            ·
              refine ⟨4206381590355234285289177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5608508787140312380385569 4206381590355234285289177)
              ·
                refine ⟨3154786192766425713966883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206381590355234285289177 3154786192766425713966883)
                ·
                  refine ⟨4732179289149638570950325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154786192766425713966883 4732179289149638570950325)
                  ·
                    refine ⟨443641808357778616026593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4732179289149638570950325 443641808357778616026593)
                    ·
                      refine ⟨332731356268333962019945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443641808357778616026593 332731356268333962019945)
                      ·
                        rfl

theorem cell23_647992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_647992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647992 prefixEnd_647992 := by exact prefixLift 647992
  have htrace : WordTrace (prefixWord ++ tailWord_647992) baseStart_647992 baseEnd_647992 := by
    simpa [prefixWord, tailWord_647992, baseEnd_647992] using wordTrace_append hprefix tailTrace_647992
  have hstable : (prefixWord ++ tailWord_647992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647992).length < 2 ^ (prefixWord ++ tailWord_647992).sum := by decide
  have hdescent : baseEnd_647992 < baseStart_647992 := by decide
  rcases family_descends (prefixWord ++ tailWord_647992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647999 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 3]
def baseStart_647999 : Nat := 118140960795 + 647999 * 2 ^ 59
def prefixEnd_647999 : Nat := 4983230072969 + 3 ^ 40 * 647999 * 2
def baseEnd_647999 : Nat := 332734950632915434632413

theorem tailTrace_647999 : CollatzResearch.WordTrace tailWord_647999 prefixEnd_647999 332734950632915434632413 := by
  unfold tailWord_647999
  simp only [CollatzResearch.WordTrace]
  refine ⟨23634465179417767263467051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15756310119611844842311367 23634465179417767263467051)
  ·
    refine ⟨35451697769126650895200577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23634465179417767263467051 35451697769126650895200577)
    ·
      refine ⟨26588773326844988171400433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35451697769126650895200577 26588773326844988171400433)
      ·
        refine ⟨19941579995133741128550325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26588773326844988171400433 19941579995133741128550325)
        ·
          refine ⟨1869523124543788230801593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19941579995133741128550325 1869523124543788230801593)
          ·
            refine ⟨1402142343407841173101195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1869523124543788230801593 1402142343407841173101195)
            ·
              refine ⟨2103213515111761759651793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402142343407841173101195 2103213515111761759651793)
              ·
                refine ⟨1577410136333821319738845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103213515111761759651793 1577410136333821319738845)
                ·
                  refine ⟨591528801125182994902067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1577410136333821319738845 591528801125182994902067)
                  ·
                    refine ⟨887293201687774492353101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 591528801125182994902067 887293201687774492353101)
                    ·
                      refine ⟨332734950632915434632413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 887293201687774492353101 332734950632915434632413)
                      ·
                        rfl

theorem cell23_647999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_647999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_647999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_647999 prefixEnd_647999 := by exact prefixLift 647999
  have htrace : WordTrace (prefixWord ++ tailWord_647999) baseStart_647999 baseEnd_647999 := by
    simpa [prefixWord, tailWord_647999, baseEnd_647999] using wordTrace_append hprefix tailTrace_647999
  have hstable : (prefixWord ++ tailWord_647999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647999).length < 2 ^ (prefixWord ++ tailWord_647999).sum := by decide
  have hdescent : baseEnd_647999 < baseStart_647999 := by decide
  rcases family_descends (prefixWord ++ tailWord_647999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648009 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 2, 3, 2]
def baseStart_648009 : Nat := 118140960795 + 648009 * 2 ^ 59
def prefixEnd_648009 : Nat := 4983230072969 + 3 ^ 40 * 648009 * 2
def baseEnd_648009 : Nat := 332740085439460395507367

theorem tailTrace_648009 : CollatzResearch.WordTrace tailWord_648009 prefixEnd_648009 332740085439460395507367 := by
  unfold tailWord_648009
  simp only [CollatzResearch.WordTrace]
  refine ⟨23634829909381538971331081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15756553272921025980887387 23634829909381538971331081)
  ·
    refine ⟨17726122432036154228498311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23634829909381538971331081 17726122432036154228498311)
    ·
      refine ⟨26589183648054231342747467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17726122432036154228498311 26589183648054231342747467)
      ·
        refine ⟨39883775472081347014121201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26589183648054231342747467 39883775472081347014121201)
        ·
          refine ⟨29912831604061010260590901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39883775472081347014121201 29912831604061010260590901)
          ·
            refine ⟨2804327962880719711930397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29912831604061010260590901 2804327962880719711930397)
            ·
              refine ⟨1051622986080269891973899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2804327962880719711930397 1051622986080269891973899)
              ·
                refine ⟨1577434479120404837960849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051622986080269891973899 1577434479120404837960849)
                ·
                  refine ⟨1183075859340303628470637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1577434479120404837960849 1183075859340303628470637)
                  ·
                    refine ⟨443653447252613860676489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183075859340303628470637 443653447252613860676489)
                    ·
                      refine ⟨332740085439460395507367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443653447252613860676489 332740085439460395507367)
                      ·
                        rfl

theorem cell23_648009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 3, 2].length) (baseStart_648009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648009 prefixEnd_648009 := by exact prefixLift 648009
  have htrace : WordTrace (prefixWord ++ tailWord_648009) baseStart_648009 baseEnd_648009 := by
    simpa [prefixWord, tailWord_648009, baseEnd_648009] using wordTrace_append hprefix tailTrace_648009
  have hstable : (prefixWord ++ tailWord_648009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648009).length < 2 ^ (prefixWord ++ tailWord_648009).sum := by decide
  have hdescent : baseEnd_648009 < baseStart_648009 := by decide
  rcases family_descends (prefixWord ++ tailWord_648009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648032 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 4, 4]
def baseStart_648032 : Nat := 118140960795 + 648032 * 2 ^ 59
def prefixEnd_648032 : Nat := 4983230072969 + 3 ^ 40 * 648032 * 2
def baseEnd_648032 : Nat := 110917298498171268506587

theorem tailTrace_648032 : CollatzResearch.WordTrace tailWord_648032 prefixEnd_648032 110917298498171268506587 := by
  unfold tailWord_648032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11817834394149106949709175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15757112525532142599612233 11817834394149106949709175)
  ·
    refine ⟨17726751591223660424563763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11817834394149106949709175 17726751591223660424563763)
    ·
      refine ⟨26590127386835490636845645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17726751591223660424563763 26590127386835490636845645)
      ·
        refine ⟨9971297770063308988817117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26590127386835490636845645 9971297770063308988817117)
        ·
          refine ⟨3739236663773740870806419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9971297770063308988817117 3739236663773740870806419)
          ·
            refine ⟨5608854995660611306209629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739236663773740870806419 5608854995660611306209629)
            ·
              refine ⟨2103320623372729239828611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5608854995660611306209629 2103320623372729239828611)
              ·
                refine ⟨3154980935059093859742917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103320623372729239828611 3154980935059093859742917)
                ·
                  refine ⟨591558925323580098701797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3154980935059093859742917 591558925323580098701797)
                  ·
                    refine ⟨110917298498171268506587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591558925323580098701797 110917298498171268506587)
                    ·
                      rfl

theorem cell23_648032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_648032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648032 prefixEnd_648032 := by exact prefixLift 648032
  have htrace : WordTrace (prefixWord ++ tailWord_648032) baseStart_648032 baseEnd_648032 := by
    simpa [prefixWord, tailWord_648032, baseEnd_648032] using wordTrace_append hprefix tailTrace_648032
  have hstable : (prefixWord ++ tailWord_648032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648032).length < 2 ^ (prefixWord ++ tailWord_648032).sum := by decide
  have hdescent : baseEnd_648032 < baseStart_648032 := by decide
  rcases family_descends (prefixWord ++ tailWord_648032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648045 : List Nat := [1, 5, 1, 1, 1, 1, 1, 12]
def baseStart_648045 : Nat := 118140960795 + 648045 * 2 ^ 59
def prefixEnd_648045 : Nat := 4983230072969 + 3 ^ 40 * 648045 * 2
def baseEnd_648045 : Nat := 12324391509000824246563

theorem tailTrace_648045 : CollatzResearch.WordTrace tailWord_648045 prefixEnd_648045 12324391509000824246563 := by
  unfold tailWord_648045
  simp only [CollatzResearch.WordTrace]
  refine ⟨23636142937251117119641589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15757428624834078079761059 23636142937251117119641589)
  ·
    refine ⟨2215888400367292229966399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23636142937251117119641589 2215888400367292229966399)
    ·
      refine ⟨3323832600550938344949599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215888400367292229966399 3323832600550938344949599)
      ·
        refine ⟨4985748900826407517424399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3323832600550938344949599 4985748900826407517424399)
        ·
          refine ⟨7478623351239611276136599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4985748900826407517424399 7478623351239611276136599)
          ·
            refine ⟨11217935026859416914204899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7478623351239611276136599 11217935026859416914204899)
            ·
              refine ⟨16826902540289125371307349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11217935026859416914204899 16826902540289125371307349)
              ·
                refine ⟨12324391509000824246563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 16826902540289125371307349 12324391509000824246563)
                ·
                  rfl

theorem cell23_648045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 12].length) (baseStart_648045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648045 prefixEnd_648045 := by exact prefixLift 648045
  have htrace : WordTrace (prefixWord ++ tailWord_648045) baseStart_648045 baseEnd_648045 := by
    simpa [prefixWord, tailWord_648045, baseEnd_648045] using wordTrace_append hprefix tailTrace_648045
  have hstable : (prefixWord ++ tailWord_648045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648045).length < 2 ^ (prefixWord ++ tailWord_648045).sum := by decide
  have hdescent : baseEnd_648045 < baseStart_648045 := by decide
  rcases family_descends (prefixWord ++ tailWord_648045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648073 : List Nat := [1, 2, 1, 1, 5, 2, 3, 3, 1, 2, 2]
def baseStart_648073 : Nat := 118140960795 + 648073 * 2 ^ 59
def prefixEnd_648073 : Nat := 4983230072969 + 3 ^ 40 * 648073 * 2
def baseEnd_648073 : Nat := 332772948201348145107073

theorem tailTrace_648073 : CollatzResearch.WordTrace tailWord_648073 prefixEnd_648073 332772948201348145107073 := by
  unfold tailWord_648073
  simp only [CollatzResearch.WordTrace]
  refine ⟨23637164181149677901660873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15758109454099785267773915 23637164181149677901660873)
  ·
    refine ⟨17727873135862258426245655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23637164181149677901660873 17727873135862258426245655)
    ·
      refine ⟨26591809703793387639368483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17727873135862258426245655 26591809703793387639368483)
      ·
        refine ⟨39887714555690081459052725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26591809703793387639368483 39887714555690081459052725)
        ·
          refine ⟨3739473239595945136786193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39887714555690081459052725 3739473239595945136786193)
          ·
            refine ⟨2804604929696958852589645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3739473239595945136786193 2804604929696958852589645)
            ·
              refine ⟨1051726848636359569721117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2804604929696958852589645 1051726848636359569721117)
              ·
                refine ⟨394397568238634838645419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1051726848636359569721117 394397568238634838645419)
                ·
                  refine ⟨591596352357952257968129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394397568238634838645419 591596352357952257968129)
                  ·
                    refine ⟨443697264268464193476097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 591596352357952257968129 443697264268464193476097)
                    ·
                      refine ⟨332772948201348145107073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443697264268464193476097 332772948201348145107073)
                      ·
                        rfl

theorem cell23_648073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 2, 2].length) (baseStart_648073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648073 prefixEnd_648073 := by exact prefixLift 648073
  have htrace : WordTrace (prefixWord ++ tailWord_648073) baseStart_648073 baseEnd_648073 := by
    simpa [prefixWord, tailWord_648073, baseEnd_648073] using wordTrace_append hprefix tailTrace_648073
  have hstable : (prefixWord ++ tailWord_648073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648073).length < 2 ^ (prefixWord ++ tailWord_648073).sum := by decide
  have hdescent : baseEnd_648073 < baseStart_648073 := by decide
  rcases family_descends (prefixWord ++ tailWord_648073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648086 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_648086 : Nat := 118140960795 + 648086 * 2 ^ 59
def prefixEnd_648086 : Nat := 4983230072969 + 3 ^ 40 * 648086 * 2
def baseEnd_648086 : Nat := 332779623449856594244513

theorem tailTrace_648086 : CollatzResearch.WordTrace tailWord_648086 prefixEnd_648086 332779623449856594244513 := by
  unfold tailWord_648086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477352395631411320117757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15758425553401720747922741 1477352395631411320117757)
  ·
    refine ⟨554007148361779245044159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1477352395631411320117757 554007148361779245044159)
    ·
      refine ⟨831010722542668867566239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554007148361779245044159 831010722542668867566239)
      ·
        refine ⟨1246516083814003301349359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831010722542668867566239 1246516083814003301349359)
        ·
          refine ⟨1869774125721004952024039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246516083814003301349359 1869774125721004952024039)
          ·
            refine ⟨2804661188581507428036059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869774125721004952024039 2804661188581507428036059)
            ·
              refine ⟨4206991782872261142054089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804661188581507428036059 4206991782872261142054089)
              ·
                refine ⟨3155243837154195856540567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206991782872261142054089 3155243837154195856540567)
                ·
                  refine ⟨4732865755731293784810851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155243837154195856540567 4732865755731293784810851)
                  ·
                    refine ⟨7099298633596940677216277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4732865755731293784810851 7099298633596940677216277)
                    ·
                      refine ⟨332779623449856594244513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7099298633596940677216277 332779623449856594244513)
                      ·
                        rfl

theorem cell23_648086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_648086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648086 prefixEnd_648086 := by exact prefixLift 648086
  have htrace : WordTrace (prefixWord ++ tailWord_648086) baseStart_648086 baseEnd_648086 := by
    simpa [prefixWord, tailWord_648086, baseEnd_648086] using wordTrace_append hprefix tailTrace_648086
  have hstable : (prefixWord ++ tailWord_648086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648086).length < 2 ^ (prefixWord ++ tailWord_648086).sum := by decide
  have hdescent : baseEnd_648086 < baseStart_648086 := by decide
  rcases family_descends (prefixWord ++ tailWord_648086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648089 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 3]
def baseStart_648089 : Nat := 118140960795 + 648089 * 2 ^ 59
def prefixEnd_648089 : Nat := 4983230072969 + 3 ^ 40 * 648089 * 2
def baseEnd_648089 : Nat := 332781163891820082506999

theorem tailTrace_648089 : CollatzResearch.WordTrace tailWord_648089 prefixEnd_648089 332781163891820082506999 := by
  unfold tailWord_648089
  simp only [CollatzResearch.WordTrace]
  refine ⟨23637747749091712634243321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15758498499394475089495547 23637747749091712634243321)
  ·
    refine ⟨17728310811818784475682491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23637747749091712634243321 17728310811818784475682491)
    ·
      refine ⟨26592466217728176713523737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17728310811818784475682491 26592466217728176713523737)
      ·
        refine ⟨19944349663296132535142803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26592466217728176713523737 19944349663296132535142803)
        ·
          refine ⟨29916524494944198802714205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19944349663296132535142803 29916524494944198802714205)
          ·
            refine ⟨11218696685604074551017827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29916524494944198802714205 11218696685604074551017827)
            ·
              refine ⟨16828045028406111826526741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11218696685604074551017827 16828045028406111826526741)
              ·
                refine ⟨788814610706536491868441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16828045028406111826526741 788814610706536491868441)
                ·
                  refine ⟨591610958029902368901331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788814610706536491868441 591610958029902368901331)
                  ·
                    refine ⟨887416437044853553351997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 591610958029902368901331 887416437044853553351997)
                    ·
                      refine ⟨332781163891820082506999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 887416437044853553351997 332781163891820082506999)
                      ·
                        rfl

theorem cell23_648089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_648089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648089 prefixEnd_648089 := by exact prefixLift 648089
  have htrace : WordTrace (prefixWord ++ tailWord_648089) baseStart_648089 baseEnd_648089 := by
    simpa [prefixWord, tailWord_648089, baseEnd_648089] using wordTrace_append hprefix tailTrace_648089
  have hstable : (prefixWord ++ tailWord_648089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648089).length < 2 ^ (prefixWord ++ tailWord_648089).sum := by decide
  have hdescent : baseEnd_648089 < baseStart_648089 := by decide
  rcases family_descends (prefixWord ++ tailWord_648089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648090 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2]
def baseStart_648090 : Nat := 118140960795 + 648090 * 2 ^ 59
def prefixEnd_648090 : Nat := 4983230072969 + 3 ^ 40 * 648090 * 2
def baseEnd_648090 : Nat := 332781677372474578594495

theorem tailTrace_648090 : CollatzResearch.WordTrace tailWord_648090 prefixEnd_648090 332781677372474578594495 := by
  unfold tailWord_648090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909446055522022451257431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15758522814725393203353149 5909446055522022451257431)
  ·
    refine ⟨8864169083283033676886147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5909446055522022451257431 8864169083283033676886147)
    ·
      refine ⟨13296253624924550515329221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8864169083283033676886147 13296253624924550515329221)
      ·
        refine ⟨2493047554673353221624229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13296253624924550515329221 2493047554673353221624229)
        ·
          refine ⟨467446416501253729054543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2493047554673353221624229 467446416501253729054543)
          ·
            refine ⟨701169624751880593581815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467446416501253729054543 701169624751880593581815)
            ·
              refine ⟨1051754437127820890372723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701169624751880593581815 1051754437127820890372723)
              ·
                refine ⟨1577631655691731335559085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051754437127820890372723 1577631655691731335559085)
                ·
                  refine ⟨591611870884399250834657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1577631655691731335559085 591611870884399250834657)
                  ·
                    refine ⟨443708903163299438125993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 591611870884399250834657 443708903163299438125993)
                    ·
                      refine ⟨332781677372474578594495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443708903163299438125993 332781677372474578594495)
                      ·
                        rfl

theorem cell23_648090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_648090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648090 prefixEnd_648090 := by exact prefixLift 648090
  have htrace : WordTrace (prefixWord ++ tailWord_648090) baseStart_648090 baseEnd_648090 := by
    simpa [prefixWord, tailWord_648090, baseEnd_648090] using wordTrace_append hprefix tailTrace_648090
  have hstable : (prefixWord ++ tailWord_648090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648090).length < 2 ^ (prefixWord ++ tailWord_648090).sum := by decide
  have hdescent : baseEnd_648090 < baseStart_648090 := by decide
  rcases family_descends (prefixWord ++ tailWord_648090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648105 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 1, 8]
def baseStart_648105 : Nat := 118140960795 + 648105 * 2 ^ 59
def prefixEnd_648105 : Nat := 4983230072969 + 3 ^ 40 * 648105 * 2
def baseEnd_648105 : Nat := 110929793194097339968975

theorem tailTrace_648105 : CollatzResearch.WordTrace tailWord_648105 prefixEnd_648105 110929793194097339968975 := by
  unfold tailWord_648105
  simp only [CollatzResearch.WordTrace]
  refine ⟨23638331317033747366825769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15758887544689164911217179 23638331317033747366825769)
  ·
    refine ⟨17728748487775310525119327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23638331317033747366825769 17728748487775310525119327)
    ·
      refine ⟨26593122731662965787678991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17728748487775310525119327 26593122731662965787678991)
      ·
        refine ⟨39889684097494448681518487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26593122731662965787678991 39889684097494448681518487)
        ·
          refine ⟨59834526146241673022277731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39889684097494448681518487 59834526146241673022277731)
          ·
            refine ⟨89751789219362509533416597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59834526146241673022277731 89751789219362509533416597)
            ·
              refine ⟨4207115119657617634378903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89751789219362509533416597 4207115119657617634378903)
              ·
                refine ⟨6310672679486426451568355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207115119657617634378903 6310672679486426451568355)
                ·
                  refine ⟨9466009019229639677352533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310672679486426451568355 9466009019229639677352533)
                  ·
                    refine ⟨110929793194097339968975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9466009019229639677352533 110929793194097339968975)
                    ·
                      rfl

theorem cell23_648105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_648105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648105 prefixEnd_648105 := by exact prefixLift 648105
  have htrace : WordTrace (prefixWord ++ tailWord_648105) baseStart_648105 baseEnd_648105 := by
    simpa [prefixWord, tailWord_648105, baseEnd_648105] using wordTrace_append hprefix tailTrace_648105
  have hstable : (prefixWord ++ tailWord_648105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648105).length < 2 ^ (prefixWord ++ tailWord_648105).sum := by decide
  have hdescent : baseEnd_648105 < baseStart_648105 := by decide
  rcases family_descends (prefixWord ++ tailWord_648105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648159 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_648159 : Nat := 118140960795 + 648159 * 2 ^ 59
def prefixEnd_648159 : Nat := 4983230072969 + 3 ^ 40 * 648159 * 2
def baseEnd_648159 : Nat := 332817107537634808631677

theorem tailTrace_648159 : CollatzResearch.WordTrace tailWord_648159 prefixEnd_648159 332817107537634808631677 := by
  unfold tailWord_648159
  simp only [CollatzResearch.WordTrace]
  refine ⟨23640300858838114589291531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15760200572558743059527687 23640300858838114589291531)
  ·
    refine ⟨35460451288257171883937297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23640300858838114589291531 35460451288257171883937297)
    ·
      refine ⟨26595338466192878912952973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35460451288257171883937297 26595338466192878912952973)
      ·
        refine ⟨9973251924822329592357365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26595338466192878912952973 9973251924822329592357365)
        ·
          refine ⟨934992367952093399283503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9973251924822329592357365 934992367952093399283503)
          ·
            refine ⟨1402488551928140098925255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934992367952093399283503 1402488551928140098925255)
            ·
              refine ⟨2103732827892210148387883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402488551928140098925255 2103732827892210148387883)
              ·
                refine ⟨3155599241838315222581825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103732827892210148387883 3155599241838315222581825)
                ·
                  refine ⟨2366699431378736416936369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155599241838315222581825 2366699431378736416936369)
                  ·
                    refine ⟨1775024573534052312702277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2366699431378736416936369 1775024573534052312702277)
                    ·
                      refine ⟨332817107537634808631677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1775024573534052312702277 332817107537634808631677)
                      ·
                        rfl

theorem cell23_648159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_648159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648159 prefixEnd_648159 := by exact prefixLift 648159
  have htrace : WordTrace (prefixWord ++ tailWord_648159) baseStart_648159 baseEnd_648159 := by
    simpa [prefixWord, tailWord_648159, baseEnd_648159] using wordTrace_append hprefix tailTrace_648159
  have hstable : (prefixWord ++ tailWord_648159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648159).length < 2 ^ (prefixWord ++ tailWord_648159).sum := by decide
  have hdescent : baseEnd_648159 < baseStart_648159 := by decide
  rcases family_descends (prefixWord ++ tailWord_648159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648229 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_648229 : Nat := 118140960795 + 648229 * 2 ^ 59
def prefixEnd_648229 : Nat := 4983230072969 + 3 ^ 40 * 648229 * 2
def baseEnd_648229 : Nat := 110951017061149844918785

theorem tailTrace_648229 : CollatzResearch.WordTrace tailWord_648229 prefixEnd_648229 110951017061149844918785 := by
  unfold tailWord_648229
  simp only [CollatzResearch.WordTrace]
  refine ⟨23642853968584516544339741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15761902645723011029559827 23642853968584516544339741)
  ·
    refine ⟨8866070238219193704127403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23642853968584516544339741 8866070238219193704127403)
    ·
      refine ⟨13299105357328790556191105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8866070238219193704127403 13299105357328790556191105)
      ·
        refine ⟨9974329017996592917143329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13299105357328790556191105 9974329017996592917143329)
        ·
          refine ⟨7480746763497444687857497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9974329017996592917143329 7480746763497444687857497)
          ·
            refine ⟨5610560072623083515893123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7480746763497444687857497 5610560072623083515893123)
            ·
              refine ⟨8415840108934625273839685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610560072623083515893123 8415840108934625273839685)
              ·
                refine ⟨1577970020425242238844941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8415840108934625273839685 1577970020425242238844941)
                ·
                  refine ⟨591738757659465839566853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1577970020425242238844941 591738757659465839566853)
                  ·
                    refine ⟨110951017061149844918785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591738757659465839566853 110951017061149844918785)
                    ·
                      rfl

theorem cell23_648229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_648229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648229 prefixEnd_648229 := by exact prefixLift 648229
  have htrace : WordTrace (prefixWord ++ tailWord_648229) baseStart_648229 baseEnd_648229 := by
    simpa [prefixWord, tailWord_648229, baseEnd_648229] using wordTrace_append hprefix tailTrace_648229
  have hstable : (prefixWord ++ tailWord_648229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648229).length < 2 ^ (prefixWord ++ tailWord_648229).sum := by decide
  have hdescent : baseEnd_648229 < baseStart_648229 := by decide
  rcases family_descends (prefixWord ++ tailWord_648229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648242 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 10]
def baseStart_648242 : Nat := 118140960795 + 648242 * 2 ^ 59
def prefixEnd_648242 : Nat := 4983230072969 + 3 ^ 40 * 648242 * 2
def baseEnd_648242 : Nat := 36984414047995331543755

theorem tailTrace_648242 : CollatzResearch.WordTrace tailWord_648242 prefixEnd_648242 36984414047995331543755 := by
  unfold tailWord_648242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910832029384354941140745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15762218745024946509708653 5910832029384354941140745)
  ·
    refine ⟨4433124022038266205855559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5910832029384354941140745 4433124022038266205855559)
    ·
      refine ⟨6649686033057399308783339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4433124022038266205855559 6649686033057399308783339)
      ·
        refine ⟨9974529049586098963175009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6649686033057399308783339 9974529049586098963175009)
        ·
          refine ⟨7480896787189574222381257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9974529049586098963175009 7480896787189574222381257)
          ·
            refine ⟨5610672590392180666785943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7480896787189574222381257 5610672590392180666785943)
            ·
              refine ⟨8416008885588271000178915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610672590392180666785943 8416008885588271000178915)
              ·
                refine ⟨12624013328382406500268373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416008885588271000178915 12624013328382406500268373)
                ·
                  refine ⟨36984414047995331543755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 12624013328382406500268373 36984414047995331543755)
                  ·
                    rfl

theorem cell23_648242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_648242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648242 prefixEnd_648242 := by exact prefixLift 648242
  have htrace : WordTrace (prefixWord ++ tailWord_648242) baseStart_648242 baseEnd_648242 := by
    simpa [prefixWord, tailWord_648242, baseEnd_648242] using wordTrace_append hprefix tailTrace_648242
  have hstable : (prefixWord ++ tailWord_648242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648242).length < 2 ^ (prefixWord ++ tailWord_648242).sum := by decide
  have hdescent : baseEnd_648242 < baseStart_648242 := by decide
  rcases family_descends (prefixWord ++ tailWord_648242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648276 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 6]
def baseStart_648276 : Nat := 118140960795 + 648276 * 2 ^ 59
def prefixEnd_648276 : Nat := 4983230072969 + 3 ^ 40 * 648276 * 2
def baseEnd_648276 : Nat := 36986353863801205652071

theorem tailTrace_648276 : CollatzResearch.WordTrace tailWord_648276 prefixEnd_648276 36986353863801205652071 := by
  unfold tailWord_648276
  simp only [CollatzResearch.WordTrace]
  refine ⟨11822284099707121785650341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15763045466276162380867121 11822284099707121785650341)
  ·
    refine ⟨2216678268695085334809439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11822284099707121785650341 2216678268695085334809439)
    ·
      refine ⟨3325017403042628002214159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2216678268695085334809439 3325017403042628002214159)
      ·
        refine ⟨4987526104563942003321239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325017403042628002214159 4987526104563942003321239)
        ·
          refine ⟨7481289156845913004981859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987526104563942003321239 7481289156845913004981859)
          ·
            refine ⟨11221933735268869507472789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7481289156845913004981859 11221933735268869507472789)
            ·
              refine ⟨526028143840728258162787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11221933735268869507472789 526028143840728258162787)
              ·
                refine ⟨789042215761092387244181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526028143840728258162787 789042215761092387244181)
                ·
                  refine ⟨36986353863801205652071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 789042215761092387244181 36986353863801205652071)
                  ·
                    rfl

theorem cell23_648276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_648276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648276 prefixEnd_648276 := by exact prefixLift 648276
  have htrace : WordTrace (prefixWord ++ tailWord_648276) baseStart_648276 baseEnd_648276 := by
    simpa [prefixWord, tailWord_648276, baseEnd_648276] using wordTrace_append hprefix tailTrace_648276
  have hstable : (prefixWord ++ tailWord_648276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648276).length < 2 ^ (prefixWord ++ tailWord_648276).sum := by decide
  have hdescent : baseEnd_648276 < baseStart_648276 := by decide
  rcases family_descends (prefixWord ++ tailWord_648276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648282 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_648282 : Nat := 118140960795 + 648282 * 2 ^ 59
def prefixEnd_648282 : Nat := 4983230072969 + 3 ^ 40 * 648282 * 2
def baseEnd_648282 : Nat := 332880265658137827393611

theorem tailTrace_648282 : CollatzResearch.WordTrace tailWord_648282 prefixEnd_648282 332880265658137827393611 := by
  unfold tailWord_648282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911196759348126649004775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15763191358261671064012733 5911196759348126649004775)
  ·
    refine ⟨8866795139022189973507163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5911196759348126649004775 8866795139022189973507163)
    ·
      refine ⟨13300192708533284960260745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8866795139022189973507163 13300192708533284960260745)
      ·
        refine ⟨9975144531399963720195559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13300192708533284960260745 9975144531399963720195559)
        ·
          refine ⟨14962716797099945580293339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9975144531399963720195559 14962716797099945580293339)
          ·
            refine ⟨22444075195649918370440009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14962716797099945580293339 22444075195649918370440009)
            ·
              refine ⟨16833056396737438777830007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22444075195649918370440009 16833056396737438777830007)
              ·
                refine ⟨25249584595106158166745011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16833056396737438777830007 25249584595106158166745011)
                ·
                  refine ⟨37874376892659237250117517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25249584595106158166745011 37874376892659237250117517)
                  ·
                    refine ⟨14202891334747213968794069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37874376892659237250117517 14202891334747213968794069)
                    ·
                      refine ⟨332880265658137827393611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14202891334747213968794069 332880265658137827393611)
                      ·
                        rfl

theorem cell23_648282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_648282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648282 prefixEnd_648282 := by exact prefixLift 648282
  have htrace : WordTrace (prefixWord ++ tailWord_648282) baseStart_648282 baseEnd_648282 := by
    simpa [prefixWord, tailWord_648282, baseEnd_648282] using wordTrace_append hprefix tailTrace_648282
  have hstable : (prefixWord ++ tailWord_648282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648282).length < 2 ^ (prefixWord ++ tailWord_648282).sum := by decide
  have hdescent : baseEnd_648282 < baseStart_648282 := by decide
  rcases family_descends (prefixWord ++ tailWord_648282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648303 : List Nat := [1, 1, 2, 1, 3, 3, 2, 5, 1, 1, 3]
def baseStart_648303 : Nat := 118140960795 + 648303 * 2 ^ 59
def prefixEnd_648303 : Nat := 4983230072969 + 3 ^ 40 * 648303 * 2
def baseEnd_648303 : Nat := 332891048751882245231015

theorem tailTrace_648303 : CollatzResearch.WordTrace tailWord_648303 prefixEnd_648303 332891048751882245231015 := by
  unfold tailWord_648303
  simp only [CollatzResearch.WordTrace]
  refine ⟨23645552970316427182533563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15763701980210951455022375 23645552970316427182533563)
  ·
    refine ⟨35468329455474640773800345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23645552970316427182533563 35468329455474640773800345)
    ·
      refine ⟨26601247091605980580350259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35468329455474640773800345 26601247091605980580350259)
      ·
        refine ⟨39901870637408970870525389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26601247091605980580350259 39901870637408970870525389)
        ·
          refine ⟨14963201489028364076447021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39901870637408970870525389 14963201489028364076447021)
          ·
            refine ⟨5611200558385636528667633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14963201489028364076447021 5611200558385636528667633)
            ·
              refine ⟨4208400418789227396500725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5611200558385636528667633 4208400418789227396500725)
              ·
                refine ⟨394537539261490068421943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4208400418789227396500725 394537539261490068421943)
                ·
                  refine ⟨591806308892235102632915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394537539261490068421943 591806308892235102632915)
                  ·
                    refine ⟨887709463338352653949373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 591806308892235102632915 887709463338352653949373)
                    ·
                      refine ⟨332891048751882245231015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 887709463338352653949373 332891048751882245231015)
                      ·
                        rfl

theorem cell23_648303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 1, 3].length) (baseStart_648303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648303 prefixEnd_648303 := by exact prefixLift 648303
  have htrace : WordTrace (prefixWord ++ tailWord_648303) baseStart_648303 baseEnd_648303 := by
    simpa [prefixWord, tailWord_648303, baseEnd_648303] using wordTrace_append hprefix tailTrace_648303
  have hstable : (prefixWord ++ tailWord_648303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648303).length < 2 ^ (prefixWord ++ tailWord_648303).sum := by decide
  have hdescent : baseEnd_648303 < baseStart_648303 := by decide
  rcases family_descends (prefixWord ++ tailWord_648303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648320 : List Nat := [2, 1, 1, 2, 1, 3, 6, 2, 1, 1, 3]
def baseStart_648320 : Nat := 118140960795 + 648320 * 2 ^ 59
def prefixEnd_648320 : Nat := 4983230072969 + 3 ^ 40 * 648320 * 2
def baseEnd_648320 : Nat := 332899777923008678718437

theorem tailTrace_648320 : CollatzResearch.WordTrace tailWord_648320 prefixEnd_648320 332899777923008678718437 := by
  unfold tailWord_648320
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823086505627419542951207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15764115340836559390601609 11823086505627419542951207)
  ·
    refine ⟨17734629758441129314426811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11823086505627419542951207 17734629758441129314426811)
    ·
      refine ⟨26601944637661693971640217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17734629758441129314426811 26601944637661693971640217)
      ·
        refine ⟨19951458478246270478730163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26601944637661693971640217 19951458478246270478730163)
        ·
          refine ⟨29927187717369405718095245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19951458478246270478730163 29927187717369405718095245)
          ·
            refine ⟨11222695394013527144285717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29927187717369405718095245 11222695394013527144285717)
            ·
              refine ⟨526063846594384084888393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11222695394013527144285717 526063846594384084888393)
              ·
                refine ⟨394547884945788063666295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526063846594384084888393 394547884945788063666295)
                ·
                  refine ⟨591821827418682095499443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394547884945788063666295 591821827418682095499443)
                  ·
                    refine ⟨887732741128023143249165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 591821827418682095499443 887732741128023143249165)
                    ·
                      refine ⟨332899777923008678718437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 887732741128023143249165 332899777923008678718437)
                      ·
                        rfl

theorem cell23_648320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_648320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648320 prefixEnd_648320 := by exact prefixLift 648320
  have htrace : WordTrace (prefixWord ++ tailWord_648320) baseStart_648320 baseEnd_648320 := by
    simpa [prefixWord, tailWord_648320, baseEnd_648320] using wordTrace_append hprefix tailTrace_648320
  have hstable : (prefixWord ++ tailWord_648320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648320).length < 2 ^ (prefixWord ++ tailWord_648320).sum := by decide
  have hdescent : baseEnd_648320 < baseStart_648320 := by decide
  rcases family_descends (prefixWord ++ tailWord_648320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648339 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4]
def baseStart_648339 : Nat := 118140960795 + 648339 * 2 ^ 59
def prefixEnd_648339 : Nat := 4983230072969 + 3 ^ 40 * 648339 * 2
def baseEnd_648339 : Nat := 332909534055444104380849

theorem tailTrace_648339 : CollatzResearch.WordTrace tailWord_648339 prefixEnd_648339 332909534055444104380849 := by
  unfold tailWord_648339
  simp only [CollatzResearch.WordTrace]
  refine ⟨23646865998186005330844071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15764577332124003553896047 23646865998186005330844071)
  ·
    refine ⟨35470298997279007996266107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23646865998186005330844071 35470298997279007996266107)
    ·
      refine ⟨53205448495918511994399161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35470298997279007996266107 53205448495918511994399161)
      ·
        refine ⟨39904086371938883995799371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53205448495918511994399161 39904086371938883995799371)
        ·
          refine ⟨59856129557908325993699057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39904086371938883995799371 59856129557908325993699057)
          ·
            refine ⟨44892097168431244495274293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59856129557908325993699057 44892097168431244495274293)
            ·
              refine ⟨4208634109540429171431965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44892097168431244495274293 4208634109540429171431965)
              ·
                refine ⟨1578237791077660939286987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4208634109540429171431965 1578237791077660939286987)
                ·
                  refine ⟨2367356686616491408930481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578237791077660939286987 2367356686616491408930481)
                  ·
                    refine ⟨1775517514962368556697861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2367356686616491408930481 1775517514962368556697861)
                    ·
                      refine ⟨332909534055444104380849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1775517514962368556697861 332909534055444104380849)
                      ·
                        rfl

theorem cell23_648339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_648339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648339 prefixEnd_648339 := by exact prefixLift 648339
  have htrace : WordTrace (prefixWord ++ tailWord_648339) baseStart_648339 baseEnd_648339 := by
    simpa [prefixWord, tailWord_648339, baseEnd_648339] using wordTrace_append hprefix tailTrace_648339
  have hstable : (prefixWord ++ tailWord_648339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648339).length < 2 ^ (prefixWord ++ tailWord_648339).sum := by decide
  have hdescent : baseEnd_648339 < baseStart_648339 := by decide
  rcases family_descends (prefixWord ++ tailWord_648339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648343 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 5, 2, 2]
def baseStart_648343 : Nat := 118140960795 + 648343 * 2 ^ 59
def prefixEnd_648343 : Nat := 4983230072969 + 3 ^ 40 * 648343 * 2
def baseEnd_648343 : Nat := 332911587978062088730831

theorem tailTrace_648343 : CollatzResearch.WordTrace tailWord_648343 prefixEnd_648343 332911587978062088730831 := by
  unfold tailWord_648343
  simp only [CollatzResearch.WordTrace]
  refine ⟨23647011890171514013989683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15764674593447676009326455 23647011890171514013989683)
  ·
    refine ⟨35470517835257271020984525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23647011890171514013989683 35470517835257271020984525)
    ·
      refine ⟨13301444188221476632869197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35470517835257271020984525 13301444188221476632869197)
      ·
        refine ⟨4988041570583053737325949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13301444188221476632869197 4988041570583053737325949)
        ·
          refine ⟨1870515588968645151497231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4988041570583053737325949 1870515588968645151497231)
          ·
            refine ⟨2805773383452967727245847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870515588968645151497231 2805773383452967727245847)
            ·
              refine ⟨4208660075179451590868771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805773383452967727245847 4208660075179451590868771)
              ·
                refine ⟨6312990112769177386303157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208660075179451590868771 6312990112769177386303157)
                ·
                  refine ⟨591842823072110379965921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6312990112769177386303157 591842823072110379965921)
                  ·
                    refine ⟨443882117304082784974441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 591842823072110379965921 443882117304082784974441)
                    ·
                      refine ⟨332911587978062088730831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 443882117304082784974441 332911587978062088730831)
                      ·
                        rfl

theorem cell23_648343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_648343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648343 prefixEnd_648343 := by exact prefixLift 648343
  have htrace : WordTrace (prefixWord ++ tailWord_648343) baseStart_648343 baseEnd_648343 := by
    simpa [prefixWord, tailWord_648343, baseEnd_648343] using wordTrace_append hprefix tailTrace_648343
  have hstable : (prefixWord ++ tailWord_648343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648343).length < 2 ^ (prefixWord ++ tailWord_648343).sum := by decide
  have hdescent : baseEnd_648343 < baseStart_648343 := by decide
  rcases family_descends (prefixWord ++ tailWord_648343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648356 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_648356 : Nat := 118140960795 + 648356 * 2 ^ 59
def prefixEnd_648356 : Nat := 4983230072969 + 3 ^ 40 * 648356 * 2
def baseEnd_648356 : Nat := 332918263226570537868271

theorem tailTrace_648356 : CollatzResearch.WordTrace tailWord_648356 prefixEnd_648356 332918263226570537868271 := by
  unfold tailWord_648356
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823743019562208617106461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15764990692749611489475281 11823743019562208617106461)
  ·
    refine ⟨4433903632335828231414923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11823743019562208617106461 4433903632335828231414923)
    ·
      refine ⟨6650855448503742347122385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4433903632335828231414923 6650855448503742347122385)
      ·
        refine ⟨4988141586377806760341789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6650855448503742347122385 4988141586377806760341789)
        ·
          refine ⟨1870553094891677535128171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4988141586377806760341789 1870553094891677535128171)
          ·
            refine ⟨2805829642337516302692257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870553094891677535128171 2805829642337516302692257)
            ·
              refine ⟨2104372231753137227019193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805829642337516302692257 2104372231753137227019193)
              ·
                refine ⟨1578279173814852920264395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104372231753137227019193 1578279173814852920264395)
                ·
                  refine ⟨2367418760722279380396593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578279173814852920264395 2367418760722279380396593)
                  ·
                    refine ⟨1775564070541709535297445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2367418760722279380396593 1775564070541709535297445)
                    ·
                      refine ⟨332918263226570537868271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1775564070541709535297445 332918263226570537868271)
                      ·
                        rfl

theorem cell23_648356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_648356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648356 prefixEnd_648356 := by exact prefixLift 648356
  have htrace : WordTrace (prefixWord ++ tailWord_648356) baseStart_648356 baseEnd_648356 := by
    simpa [prefixWord, tailWord_648356, baseEnd_648356] using wordTrace_append hprefix tailTrace_648356
  have hstable : (prefixWord ++ tailWord_648356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648356).length < 2 ^ (prefixWord ++ tailWord_648356).sum := by decide
  have hdescent : baseEnd_648356 < baseStart_648356 := by decide
  rcases family_descends (prefixWord ++ tailWord_648356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648444 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_648444 : Nat := 118140960795 + 648444 * 2 ^ 59
def prefixEnd_648444 : Nat := 4983230072969 + 3 ^ 40 * 648444 * 2
def baseEnd_648444 : Nat := 332963449524166193567867

theorem tailTrace_648444 : CollatzResearch.WordTrace tailWord_648444 prefixEnd_648444 332963449524166193567867 := by
  unfold tailWord_648444
  simp only [CollatzResearch.WordTrace]
  refine ⟨11825347831402804131708193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15767130441870405508944257 11825347831402804131708193)
  ·
    refine ⟨8869010873552103098781145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11825347831402804131708193 8869010873552103098781145)
    ·
      refine ⟨6651758155164077324085859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8869010873552103098781145 6651758155164077324085859)
      ·
        refine ⟨9977637232746115986128789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6651758155164077324085859 9977637232746115986128789)
        ·
          refine ⟨467701745284974186849787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9977637232746115986128789 467701745284974186849787)
          ·
            refine ⟨701552617927461280274681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467701745284974186849787 701552617927461280274681)
            ·
              refine ⟨526164463445595960206011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701552617927461280274681 526164463445595960206011)
              ·
                refine ⟨789246695168393940309017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526164463445595960206011 789246695168393940309017)
                ·
                  refine ⟨591935021376295455231763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 789246695168393940309017 591935021376295455231763)
                  ·
                    refine ⟨887902532064443182847645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 591935021376295455231763 887902532064443182847645)
                    ·
                      refine ⟨332963449524166193567867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 887902532064443182847645 332963449524166193567867)
                      ·
                        rfl

theorem cell23_648444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_648444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648444 prefixEnd_648444 := by exact prefixLift 648444
  have htrace : WordTrace (prefixWord ++ tailWord_648444) baseStart_648444 baseEnd_648444 := by
    simpa [prefixWord, tailWord_648444, baseEnd_648444] using wordTrace_append hprefix tailTrace_648444
  have hstable : (prefixWord ++ tailWord_648444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648444).length < 2 ^ (prefixWord ++ tailWord_648444).sum := by decide
  have hdescent : baseEnd_648444 < baseStart_648444 := by decide
  rcases family_descends (prefixWord ++ tailWord_648444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648490 : List Nat := [3, 1, 4, 2, 1, 2, 1, 4, 5]
def baseStart_648490 : Nat := 118140960795 + 648490 * 2 ^ 59
def prefixEnd_648490 : Nat := 4983230072969 + 3 ^ 40 * 648490 * 2
def baseEnd_648490 : Nat := 36998563292697001510295

theorem tailTrace_648490 : CollatzResearch.WordTrace tailWord_648490 prefixEnd_648490 36998563292697001510295 := by
  unfold tailWord_648490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5913093355159739529897731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15768248947092638746393949 5913093355159739529897731)
  ·
    refine ⟨8869640032739609294846597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5913093355159739529897731 8869640032739609294846597)
    ·
      refine ⟨1663057506138676742783737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8869640032739609294846597 1663057506138676742783737)
      ·
        refine ⟨1247293129604007557087803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1663057506138676742783737 1247293129604007557087803)
        ·
          refine ⟨1870939694406011335631705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247293129604007557087803 1870939694406011335631705)
          ·
            refine ⟨1403204770804508501723779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1870939694406011335631705 1403204770804508501723779)
            ·
              refine ⟨2104807156206762752585669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403204770804508501723779 2104807156206762752585669)
              ·
                refine ⟨394651341788768016109813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2104807156206762752585669 394651341788768016109813)
                ·
                  refine ⟨36998563292697001510295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 394651341788768016109813 36998563292697001510295)
                  ·
                    rfl

theorem cell23_648490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_648490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648490 prefixEnd_648490 := by exact prefixLift 648490
  have htrace : WordTrace (prefixWord ++ tailWord_648490) baseStart_648490 baseEnd_648490 := by
    simpa [prefixWord, tailWord_648490, baseEnd_648490] using wordTrace_append hprefix tailTrace_648490
  have hstable : (prefixWord ++ tailWord_648490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648490).length < 2 ^ (prefixWord ++ tailWord_648490).sum := by decide
  have hdescent : baseEnd_648490 < baseStart_648490 := by decide
  rcases family_descends (prefixWord ++ tailWord_648490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648506 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_648506 : Nat := 118140960795 + 648506 * 2 ^ 59
def prefixEnd_648506 : Nat := 4983230072969 + 3 ^ 40 * 648506 * 2
def baseEnd_648506 : Nat := 332995285324744950992581

theorem tailTrace_648506 : CollatzResearch.WordTrace tailWord_648506 prefixEnd_648506 332995285324744950992581 := by
  unfold tailWord_648506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5913239247145248213043343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15768637992387328568115581 5913239247145248213043343)
  ·
    refine ⟨8869858870717872319565015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5913239247145248213043343 8869858870717872319565015)
    ·
      refine ⟨13304788306076808479347523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8869858870717872319565015 13304788306076808479347523)
      ·
        refine ⟨19957182459115212719021285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13304788306076808479347523 19957182459115212719021285)
        ·
          refine ⟨3741971711084102384816491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19957182459115212719021285 3741971711084102384816491)
          ·
            refine ⟨5612957566626153577224737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3741971711084102384816491 5612957566626153577224737)
            ·
              refine ⟨4209718174969615182918553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5612957566626153577224737 4209718174969615182918553)
              ·
                refine ⟨3157288631227211387188915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4209718174969615182918553 3157288631227211387188915)
                ·
                  refine ⟨4735932946840817080783373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157288631227211387188915 4735932946840817080783373)
                  ·
                    refine ⟨1775974855065306405293765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4735932946840817080783373 1775974855065306405293765)
                    ·
                      refine ⟨332995285324744950992581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1775974855065306405293765 332995285324744950992581)
                      ·
                        rfl

theorem cell23_648506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_648506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648506 prefixEnd_648506 := by exact prefixLift 648506
  have htrace : WordTrace (prefixWord ++ tailWord_648506) baseStart_648506 baseEnd_648506 := by
    simpa [prefixWord, tailWord_648506, baseEnd_648506] using wordTrace_append hprefix tailTrace_648506
  have hstable : (prefixWord ++ tailWord_648506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648506).length < 2 ^ (prefixWord ++ tailWord_648506).sum := by decide
  have hdescent : baseEnd_648506 < baseStart_648506 := by decide
  rcases family_descends (prefixWord ++ tailWord_648506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648576 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 3, 5]
def baseStart_648576 : Nat := 118140960795 + 648576 * 2 ^ 59
def prefixEnd_648576 : Nat := 4983230072969 + 3 ^ 40 * 648576 * 2
def baseEnd_648576 : Nat := 111010409656853225705753

theorem tailTrace_648576 : CollatzResearch.WordTrace tailWord_648576 prefixEnd_648576 111010409656853225705753 := by
  unfold tailWord_648576
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827755049163697403610791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15770340065551596538147721 11827755049163697403610791)
  ·
    refine ⟨17741632573745546105416187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11827755049163697403610791 17741632573745546105416187)
    ·
      refine ⟨26612448860618319158124281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17741632573745546105416187 26612448860618319158124281)
      ·
        refine ⟨19959336645463739368593211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26612448860618319158124281 19959336645463739368593211)
        ·
          refine ⟨29939004968195609052889817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19959336645463739368593211 29939004968195609052889817)
          ·
            refine ⟨22454253726146706789667363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29939004968195609052889817 22454253726146706789667363)
            ·
              refine ⟨33681380589220060184501045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22454253726146706789667363 33681380589220060184501045)
              ·
                refine ⟨3157629430239380642296973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33681380589220060184501045 3157629430239380642296973)
                ·
                  refine ⟨1184111036339767740861365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3157629430239380642296973 1184111036339767740861365)
                  ·
                    refine ⟨111010409656853225705753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1184111036339767740861365 111010409656853225705753)
                    ·
                      rfl

theorem cell23_648576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_648576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648576 prefixEnd_648576 := by exact prefixLift 648576
  have htrace : WordTrace (prefixWord ++ tailWord_648576) baseStart_648576 baseEnd_648576 := by
    simpa [prefixWord, tailWord_648576, baseEnd_648576] using wordTrace_append hprefix tailTrace_648576
  have hstable : (prefixWord ++ tailWord_648576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648576).length < 2 ^ (prefixWord ++ tailWord_648576).sum := by decide
  have hdescent : baseEnd_648576 < baseStart_648576 := by decide
  rcases family_descends (prefixWord ++ tailWord_648576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648607 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 3]
def baseStart_648607 : Nat := 118140960795 + 648607 * 2 ^ 59
def prefixEnd_648607 : Nat := 4983230072969 + 3 ^ 40 * 648607 * 2
def baseEnd_648607 : Nat := 333047146870849055829617

theorem tailTrace_648607 : CollatzResearch.WordTrace tailWord_648607 prefixEnd_648607 333047146870849055829617 := by
  unfold tailWord_648607
  simp only [CollatzResearch.WordTrace]
  refine ⟨23656640761215087101600075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15771093840810058067733383 23656640761215087101600075)
  ·
    refine ⟨35484961141822630652400113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23656640761215087101600075 35484961141822630652400113)
    ·
      refine ⟨26613720856366972989300085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35484961141822630652400113 26613720856366972989300085)
      ·
        refine ⟨2495036330284403717746883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26613720856366972989300085 2495036330284403717746883)
        ·
          refine ⟨3742554495426605576620325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495036330284403717746883 3742554495426605576620325)
          ·
            refine ⟨701728967892488545616311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3742554495426605576620325 701728967892488545616311)
            ·
              refine ⟨1052593451838732818424467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701728967892488545616311 1052593451838732818424467)
              ·
                refine ⟨1578890177758099227636701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052593451838732818424467 1578890177758099227636701)
                ·
                  refine ⟨592083816659287210363763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1578890177758099227636701 592083816659287210363763)
                  ·
                    refine ⟨888125724988930815545645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 592083816659287210363763 888125724988930815545645)
                    ·
                      refine ⟨333047146870849055829617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 888125724988930815545645 333047146870849055829617)
                      ·
                        rfl

theorem cell23_648607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_648607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648607 prefixEnd_648607 := by exact prefixLift 648607
  have htrace : WordTrace (prefixWord ++ tailWord_648607) baseStart_648607 baseEnd_648607 := by
    simpa [prefixWord, tailWord_648607, baseEnd_648607] using wordTrace_append hprefix tailTrace_648607
  have hstable : (prefixWord ++ tailWord_648607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648607).length < 2 ^ (prefixWord ++ tailWord_648607).sum := by decide
  have hdescent : baseEnd_648607 < baseStart_648607 := by decide
  rcases family_descends (prefixWord ++ tailWord_648607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648613 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 2, 6, 2]
def baseStart_648613 : Nat := 118140960795 + 648613 * 2 ^ 59
def prefixEnd_648613 : Nat := 4983230072969 + 3 ^ 40 * 648613 * 2
def baseEnd_648613 : Nat := 333050227754776032354589

theorem tailTrace_648613 : CollatzResearch.WordTrace tailWord_648613 prefixEnd_648613 333050227754776032354589 := by
  unfold tailWord_648613
  simp only [CollatzResearch.WordTrace]
  refine ⟨23656859599193350126318493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15771239732795566750878995 23656859599193350126318493)
  ·
    refine ⟨8871322349697506297369435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23656859599193350126318493 8871322349697506297369435)
    ·
      refine ⟨13306983524546259446054153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8871322349697506297369435 13306983524546259446054153)
      ·
        refine ⟨9980237643409694584540615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13306983524546259446054153 9980237643409694584540615)
        ·
          refine ⟨14970356465114541876810923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9980237643409694584540615 14970356465114541876810923)
          ·
            refine ⟨22455534697671812815216385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14970356465114541876810923 22455534697671812815216385)
            ·
              refine ⟨16841651023253859611412289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22455534697671812815216385 16841651023253859611412289)
              ·
                refine ⟨12631238267440394708559217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16841651023253859611412289 12631238267440394708559217)
                ·
                  refine ⟨9473428700580296031419413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12631238267440394708559217 9473428700580296031419413)
                  ·
                    refine ⟨444066970339701376472785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9473428700580296031419413 444066970339701376472785)
                    ·
                      refine ⟨333050227754776032354589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444066970339701376472785 333050227754776032354589)
                      ·
                        rfl

theorem cell23_648613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_648613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648613 prefixEnd_648613 := by exact prefixLift 648613
  have htrace : WordTrace (prefixWord ++ tailWord_648613) baseStart_648613 baseEnd_648613 := by
    simpa [prefixWord, tailWord_648613, baseEnd_648613] using wordTrace_append hprefix tailTrace_648613
  have hstable : (prefixWord ++ tailWord_648613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648613).length < 2 ^ (prefixWord ++ tailWord_648613).sum := by decide
  have hdescent : baseEnd_648613 < baseStart_648613 := by decide
  rcases family_descends (prefixWord ++ tailWord_648613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648650 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_648650 : Nat := 118140960795 + 648650 * 2 ^ 59
def prefixEnd_648650 : Nat := 4983230072969 + 3 ^ 40 * 648650 * 2
def baseEnd_648650 : Nat := 333069226538992387591919

theorem tailTrace_648650 : CollatzResearch.WordTrace tailWord_648650 prefixEnd_648650 333069226538992387591919 := by
  unfold tailWord_648650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5914552275014826361353851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15772139400039536963610269 5914552275014826361353851)
  ·
    refine ⟨8871828412522239542030777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5914552275014826361353851 8871828412522239542030777)
    ·
      refine ⟨6653871309391679656523083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8871828412522239542030777 6653871309391679656523083)
      ·
        refine ⟨9980806964087519484784625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6653871309391679656523083 9980806964087519484784625)
        ·
          refine ⟨7485605223065639613588469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9980806964087519484784625 7485605223065639613588469)
          ·
            refine ⟨701775489662403713773919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7485605223065639613588469 701775489662403713773919)
            ·
              refine ⟨1052663234493605570660879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701775489662403713773919 1052663234493605570660879)
              ·
                refine ⟨1578994851740408355991319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052663234493605570660879 1578994851740408355991319)
                ·
                  refine ⟨2368492277610612533986979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578994851740408355991319 2368492277610612533986979)
                  ·
                    refine ⟨3552738416415918800980469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2368492277610612533986979 3552738416415918800980469)
                    ·
                      refine ⟨333069226538992387591919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3552738416415918800980469 333069226538992387591919)
                      ·
                        rfl

theorem cell23_648650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_648650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648650 prefixEnd_648650 := by exact prefixLift 648650
  have htrace : WordTrace (prefixWord ++ tailWord_648650) baseStart_648650 baseEnd_648650 := by
    simpa [prefixWord, tailWord_648650, baseEnd_648650] using wordTrace_append hprefix tailTrace_648650
  have hstable : (prefixWord ++ tailWord_648650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648650).length < 2 ^ (prefixWord ++ tailWord_648650).sum := by decide
  have hdescent : baseEnd_648650 < baseStart_648650 := by decide
  rcases family_descends (prefixWord ++ tailWord_648650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648680 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_648680 : Nat := 118140960795 + 648680 * 2 ^ 59
def prefixEnd_648680 : Nat := 4983230072969 + 3 ^ 40 * 648680 * 2
def baseEnd_648680 : Nat := 333084630958627270216781

theorem tailTrace_648680 : CollatzResearch.WordTrace tailWord_648680 prefixEnd_648680 333084630958627270216781 := by
  unfold tailWord_648680
  simp only [CollatzResearch.WordTrace]
  refine ⟨11829651644975310284503747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15772868859967080379338329 11829651644975310284503747)
  ·
    refine ⟨17744477467462965426755621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11829651644975310284503747 17744477467462965426755621)
    ·
      refine ⟨3327089525149306017516679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17744477467462965426755621 3327089525149306017516679)
      ·
        refine ⟨4990634287723959026275019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3327089525149306017516679 4990634287723959026275019)
        ·
          refine ⟨7485951431585938539412529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4990634287723959026275019 7485951431585938539412529)
          ·
            refine ⟨5614463573689453904559397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7485951431585938539412529 5614463573689453904559397)
            ·
              refine ⟨1052711920066772607104887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5614463573689453904559397 1052711920066772607104887)
              ·
                refine ⟨1579067880100158910657331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052711920066772607104887 1579067880100158910657331)
                ·
                  refine ⟨2368601820150238365985997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579067880100158910657331 2368601820150238365985997)
                  ·
                    refine ⟨888225682556339387244749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368601820150238365985997 888225682556339387244749)
                    ·
                      refine ⟨333084630958627270216781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 888225682556339387244749 333084630958627270216781)
                      ·
                        rfl

theorem cell23_648680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_648680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648680 prefixEnd_648680 := by exact prefixLift 648680
  have htrace : WordTrace (prefixWord ++ tailWord_648680) baseStart_648680 baseEnd_648680 := by
    simpa [prefixWord, tailWord_648680, baseEnd_648680] using wordTrace_append hprefix tailTrace_648680
  have hstable : (prefixWord ++ tailWord_648680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648680).length < 2 ^ (prefixWord ++ tailWord_648680).sum := by decide
  have hdescent : baseEnd_648680 < baseStart_648680 := by decide
  rcases family_descends (prefixWord ++ tailWord_648680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648714 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_648714 : Nat := 118140960795 + 648714 * 2 ^ 59
def prefixEnd_648714 : Nat := 4983230072969 + 3 ^ 40 * 648714 * 2
def baseEnd_648714 : Nat := 333102089300880137191625

theorem tailTrace_648714 : CollatzResearch.WordTrace tailWord_648714 prefixEnd_648714 333102089300880137191625 := by
  unfold tailWord_648714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915135842956861093936299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15773695581218296250496797 5915135842956861093936299)
  ·
    refine ⟨8872703764435291640904449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5915135842956861093936299 8872703764435291640904449)
    ·
      refine ⟨6654527823326468730678337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8872703764435291640904449 6654527823326468730678337)
      ·
        refine ⟨4990895867494851548008753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6654527823326468730678337 4990895867494851548008753)
        ·
          refine ⟨3743171900621138661006565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4990895867494851548008753 3743171900621138661006565)
          ·
            refine ⟨701844731366463498938731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3743171900621138661006565 701844731366463498938731)
            ·
              refine ⟨1052767097049695248408097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701844731366463498938731 1052767097049695248408097)
              ·
                refine ⟨789575322787271436306073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052767097049695248408097 789575322787271436306073)
                ·
                  refine ⟨592181492090453577229555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 789575322787271436306073 592181492090453577229555)
                  ·
                    refine ⟨888272238135680365844333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 592181492090453577229555 888272238135680365844333)
                    ·
                      refine ⟨333102089300880137191625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 888272238135680365844333 333102089300880137191625)
                      ·
                        rfl

theorem cell23_648714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_648714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648714 prefixEnd_648714 := by exact prefixLift 648714
  have htrace : WordTrace (prefixWord ++ tailWord_648714) baseStart_648714 baseEnd_648714 := by
    simpa [prefixWord, tailWord_648714, baseEnd_648714] using wordTrace_append hprefix tailTrace_648714
  have hstable : (prefixWord ++ tailWord_648714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648714).length < 2 ^ (prefixWord ++ tailWord_648714).sum := by decide
  have hdescent : baseEnd_648714 < baseStart_648714 := by decide
  rcases family_descends (prefixWord ++ tailWord_648714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648737 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_648737 : Nat := 118140960795 + 648737 * 2 ^ 59
def prefixEnd_648737 : Nat := 4983230072969 + 3 ^ 40 * 648737 * 2
def baseEnd_648737 : Nat := 333113899355933547204019

theorem tailTrace_648737 : CollatzResearch.WordTrace tailWord_648737 prefixEnd_648737 333113899355933547204019 := by
  unfold tailWord_648737
  simp only [CollatzResearch.WordTrace]
  refine ⟨23661382250744119303832465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15774254833829412869221643 23661382250744119303832465)
  ·
    refine ⟨17746036688058089477874349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23661382250744119303832465 17746036688058089477874349)
    ·
      refine ⟨6654763758021783554202881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17746036688058089477874349 6654763758021783554202881)
      ·
        refine ⟨4991072818516337665652161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6654763758021783554202881 4991072818516337665652161)
        ·
          refine ⟨3743304613887253249239121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4991072818516337665652161 3743304613887253249239121)
          ·
            refine ⟨2807478460415439936929341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3743304613887253249239121 2807478460415439936929341)
            ·
              refine ⟨1052804422655789976348503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2807478460415439936929341 1052804422655789976348503)
              ·
                refine ⟨1579206633983684964522755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052804422655789976348503 1579206633983684964522755)
                ·
                  refine ⟨2368809950975527446784133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579206633983684964522755 2368809950975527446784133)
                  ·
                    refine ⟨444151865807911396272025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368809950975527446784133 444151865807911396272025)
                    ·
                      refine ⟨333113899355933547204019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444151865807911396272025 333113899355933547204019)
                      ·
                        rfl

theorem cell23_648737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_648737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648737 prefixEnd_648737 := by exact prefixLift 648737
  have htrace : WordTrace (prefixWord ++ tailWord_648737) baseStart_648737 baseEnd_648737 := by
    simpa [prefixWord, tailWord_648737, baseEnd_648737] using wordTrace_append hprefix tailTrace_648737
  have hstable : (prefixWord ++ tailWord_648737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648737).length < 2 ^ (prefixWord ++ tailWord_648737).sum := by decide
  have hdescent : baseEnd_648737 < baseStart_648737 := by decide
  rcases family_descends (prefixWord ++ tailWord_648737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648793 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_648793 : Nat := 118140960795 + 648793 * 2 ^ 59
def prefixEnd_648793 : Nat := 4983230072969 + 3 ^ 40 * 648793 * 2
def baseEnd_648793 : Nat := 333142654272585328103761

theorem tailTrace_648793 : CollatzResearch.WordTrace tailWord_648793 prefixEnd_648793 333142654272585328103761 := by
  unfold tailWord_648793
  simp only [CollatzResearch.WordTrace]
  refine ⟨23663424738541240867871033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15775616492360827245247355 23663424738541240867871033)
  ·
    refine ⟨17747568553905930650903275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23663424738541240867871033 17747568553905930650903275)
    ·
      refine ⟨26621352830858895976354913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17747568553905930650903275 26621352830858895976354913)
      ·
        refine ⟨19966014623144171982266185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26621352830858895976354913 19966014623144171982266185)
        ·
          refine ⟨14974510967358128986699639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19966014623144171982266185 14974510967358128986699639)
          ·
            refine ⟨22461766451037193480049459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14974510967358128986699639 22461766451037193480049459)
            ·
              refine ⟨33692649676555790220074189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22461766451037193480049459 33692649676555790220074189)
              ·
                refine ⟨12634743628708421332527821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33692649676555790220074189 12634743628708421332527821)
                ·
                  refine ⟨4738028860765657999697933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12634743628708421332527821 4738028860765657999697933)
                  ·
                    refine ⟨1776760822787121749886725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4738028860765657999697933 1776760822787121749886725)
                    ·
                      refine ⟨333142654272585328103761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1776760822787121749886725 333142654272585328103761)
                      ·
                        rfl

theorem cell23_648793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_648793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648793 prefixEnd_648793 := by exact prefixLift 648793
  have htrace : WordTrace (prefixWord ++ tailWord_648793) baseStart_648793 baseEnd_648793 := by
    simpa [prefixWord, tailWord_648793, baseEnd_648793] using wordTrace_append hprefix tailTrace_648793
  have hstable : (prefixWord ++ tailWord_648793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648793).length < 2 ^ (prefixWord ++ tailWord_648793).sum := by decide
  have hdescent : baseEnd_648793 < baseStart_648793 := by decide
  rcases family_descends (prefixWord ++ tailWord_648793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648823 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_648823 : Nat := 118140960795 + 648823 * 2 ^ 59
def prefixEnd_648823 : Nat := 4983230072969 + 3 ^ 40 * 648823 * 2
def baseEnd_648823 : Nat := 333158058692220210728623

theorem tailTrace_648823 : CollatzResearch.WordTrace tailWord_648823 prefixEnd_648823 333158058692220210728623 := by
  unfold tailWord_648823
  simp only [CollatzResearch.WordTrace]
  refine ⟨23664518928432555991463123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15776345952288370660975415 23664518928432555991463123)
  ·
    refine ⟨35496778392648833987194685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23664518928432555991463123 35496778392648833987194685)
    ·
      refine ⟨13311291897243312745198007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35496778392648833987194685 13311291897243312745198007)
      ·
        refine ⟨19966937845864969117797011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13311291897243312745198007 19966937845864969117797011)
        ·
          refine ⟨29950406768797453676695517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19966937845864969117797011 29950406768797453676695517)
          ·
            refine ⟨11231402538299045128760819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29950406768797453676695517 11231402538299045128760819)
            ·
              refine ⟨16847103807448567693141229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11231402538299045128760819 16847103807448567693141229)
              ·
                refine ⟨6317663927793212884927961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16847103807448567693141229 6317663927793212884927961)
                ·
                  refine ⟨4738247945844909663695971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6317663927793212884927961 4738247945844909663695971)
                  ·
                    refine ⟨7107371918767364495543957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4738247945844909663695971 7107371918767364495543957)
                    ·
                      refine ⟨333158058692220210728623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7107371918767364495543957 333158058692220210728623)
                      ·
                        rfl

theorem cell23_648823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_648823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648823 prefixEnd_648823 := by exact prefixLift 648823
  have htrace : WordTrace (prefixWord ++ tailWord_648823) baseStart_648823 baseEnd_648823 := by
    simpa [prefixWord, tailWord_648823, baseEnd_648823] using wordTrace_append hprefix tailTrace_648823
  have hstable : (prefixWord ++ tailWord_648823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648823).length < 2 ^ (prefixWord ++ tailWord_648823).sum := by decide
  have hdescent : baseEnd_648823 < baseStart_648823 := by decide
  rcases family_descends (prefixWord ++ tailWord_648823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648864 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3]
def baseStart_648864 : Nat := 118140960795 + 648864 * 2 ^ 59
def prefixEnd_648864 : Nat := 4983230072969 + 3 ^ 40 * 648864 * 2
def baseEnd_648864 : Nat := 333179111399054550315935

theorem tailTrace_648864 : CollatzResearch.WordTrace tailWord_648864 prefixEnd_648864 333179111399054550315935 := by
  unfold tailWord_648864
  simp only [CollatzResearch.WordTrace]
  refine ⟨11833007160642009996852823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15777342880856013329137097 11833007160642009996852823)
  ·
    refine ⟨17749510740963014995279235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11833007160642009996852823 17749510740963014995279235)
    ·
      refine ⟨26624266111444522492918853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17749510740963014995279235 26624266111444522492918853)
      ·
        refine ⟨4992049895895847967422285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26624266111444522492918853 4992049895895847967422285)
        ·
          refine ⟨1872018710960942987783357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4992049895895847967422285 1872018710960942987783357)
          ·
            refine ⟨702007016610353620418759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1872018710960942987783357 702007016610353620418759)
            ·
              refine ⟨1053010524915530430628139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702007016610353620418759 1053010524915530430628139)
              ·
                refine ⟨1579515787373295645942209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053010524915530430628139 1579515787373295645942209)
                ·
                  refine ⟨1184636840529971734456657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579515787373295645942209 1184636840529971734456657)
                  ·
                    refine ⟨888477630397478800842493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1184636840529971734456657 888477630397478800842493)
                    ·
                      refine ⟨333179111399054550315935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 888477630397478800842493 333179111399054550315935)
                      ·
                        rfl

theorem cell23_648864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_648864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648864 prefixEnd_648864 := by exact prefixLift 648864
  have htrace : WordTrace (prefixWord ++ tailWord_648864) baseStart_648864 baseEnd_648864 := by
    simpa [prefixWord, tailWord_648864, baseEnd_648864] using wordTrace_append hprefix tailTrace_648864
  have hstable : (prefixWord ++ tailWord_648864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648864).length < 2 ^ (prefixWord ++ tailWord_648864).sum := by decide
  have hdescent : baseEnd_648864 < baseStart_648864 := by decide
  rcases family_descends (prefixWord ++ tailWord_648864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648873 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_648873 : Nat := 118140960795 + 648873 * 2 ^ 59
def prefixEnd_648873 : Nat := 4983230072969 + 3 ^ 40 * 648873 * 2
def baseEnd_648873 : Nat := 333183732724945015103393

theorem tailTrace_648873 : CollatzResearch.WordTrace tailWord_648873 prefixEnd_648873 333183732724945015103393 := by
  unfold tailWord_648873
  simp only [CollatzResearch.WordTrace]
  refine ⟨23666342578251414530783273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15777561718834276353855515 23666342578251414530783273)
  ·
    refine ⟨17749756933688560898087455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23666342578251414530783273 17749756933688560898087455)
    ·
      refine ⟨26624635400532841347131183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17749756933688560898087455 26624635400532841347131183)
      ·
        refine ⟨39936953100799262020696775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26624635400532841347131183 39936953100799262020696775)
        ·
          refine ⟨59905429651198893031045163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39936953100799262020696775 59905429651198893031045163)
          ·
            refine ⟨89858144476798339546567745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59905429651198893031045163 89858144476798339546567745)
            ·
              refine ⟨67393608357598754659925809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89858144476798339546567745 67393608357598754659925809)
              ·
                refine ⟨50545206268199065994944357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67393608357598754659925809 50545206268199065994944357)
                ·
                  refine ⟨9477226175287324874052067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50545206268199065994944357 9477226175287324874052067)
                  ·
                    refine ⟨14215839262930987311078101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9477226175287324874052067 14215839262930987311078101)
                    ·
                      refine ⟨333183732724945015103393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14215839262930987311078101 333183732724945015103393)
                      ·
                        rfl

theorem cell23_648873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_648873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648873 prefixEnd_648873 := by exact prefixLift 648873
  have htrace : WordTrace (prefixWord ++ tailWord_648873) baseStart_648873 baseEnd_648873 := by
    simpa [prefixWord, tailWord_648873, baseEnd_648873] using wordTrace_append hprefix tailTrace_648873
  have hstable : (prefixWord ++ tailWord_648873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648873).length < 2 ^ (prefixWord ++ tailWord_648873).sum := by decide
  have hdescent : baseEnd_648873 < baseStart_648873 := by decide
  rcases family_descends (prefixWord ++ tailWord_648873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648894 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_648894 : Nat := 118140960795 + 648894 * 2 ^ 59
def prefixEnd_648894 : Nat := 4983230072969 + 3 ^ 40 * 648894 * 2
def baseEnd_648894 : Nat := 333194515818689432940797

theorem tailTrace_648894 : CollatzResearch.WordTrace tailWord_648894 prefixEnd_648894 333194515818689432940797 := by
  unfold tailWord_648894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958388563896916889662217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15778072340783556744865157 2958388563896916889662217)
  ·
    refine ⟨2218791422922687667246663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2958388563896916889662217 2218791422922687667246663)
    ·
      refine ⟨3328187134384031500869995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2218791422922687667246663 3328187134384031500869995)
      ·
        refine ⟨4992280701576047251304993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328187134384031500869995 4992280701576047251304993)
        ·
          refine ⟨3744210526182035438478745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4992280701576047251304993 3744210526182035438478745)
          ·
            refine ⟨2808157894636526578859059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3744210526182035438478745 2808157894636526578859059)
            ·
              refine ⟨4212236841954789868288589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808157894636526578859059 4212236841954789868288589)
              ·
                refine ⟨1579588815733046200608221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4212236841954789868288589 1579588815733046200608221)
                ·
                  refine ⟨592345805899892325228083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1579588815733046200608221 592345805899892325228083)
                  ·
                    refine ⟨888518708849838487842125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 592345805899892325228083 888518708849838487842125)
                    ·
                      refine ⟨333194515818689432940797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 888518708849838487842125 333194515818689432940797)
                      ·
                        rfl

theorem cell23_648894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_648894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648894 prefixEnd_648894 := by exact prefixLift 648894
  have htrace : WordTrace (prefixWord ++ tailWord_648894) baseStart_648894 baseEnd_648894 := by
    simpa [prefixWord, tailWord_648894, baseEnd_648894] using wordTrace_append hprefix tailTrace_648894
  have hstable : (prefixWord ++ tailWord_648894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648894).length < 2 ^ (prefixWord ++ tailWord_648894).sum := by decide
  have hdescent : baseEnd_648894 < baseStart_648894 := by decide
  rcases family_descends (prefixWord ++ tailWord_648894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648914 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_648914 : Nat := 118140960795 + 648914 * 2 ^ 59
def prefixEnd_648914 : Nat := 4983230072969 + 3 ^ 40 * 648914 * 2
def baseEnd_648914 : Nat := 111068261810593118230235

theorem tailTrace_648914 : CollatzResearch.WordTrace tailWord_648914 prefixEnd_648914 111068261810593118230235 := by
  unfold tailWord_648914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916959492775719633256449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15778558647401919022017197 5916959492775719633256449)
  ·
    refine ⟨4437719619581789724942337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5916959492775719633256449 4437719619581789724942337)
    ·
      refine ⟨3328289714686342293706753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4437719619581789724942337 3328289714686342293706753)
      ·
        refine ⟨2496217286014756720280065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3328289714686342293706753 2496217286014756720280065)
        ·
          refine ⟨1872162964511067540210049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496217286014756720280065 1872162964511067540210049)
          ·
            refine ⟨1404122223383300655157537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872162964511067540210049 1404122223383300655157537)
            ·
              refine ⟨1053091667537475491368153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404122223383300655157537 1053091667537475491368153)
              ·
                refine ⟨789818750653106618526115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053091667537475491368153 789818750653106618526115)
                ·
                  refine ⟨1184728125979659927789173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789818750653106618526115 1184728125979659927789173)
                  ·
                    refine ⟨111068261810593118230235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1184728125979659927789173 111068261810593118230235)
                    ·
                      rfl

theorem cell23_648914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_648914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648914 prefixEnd_648914 := by exact prefixLift 648914
  have htrace : WordTrace (prefixWord ++ tailWord_648914) baseStart_648914 baseEnd_648914 := by
    simpa [prefixWord, tailWord_648914, baseEnd_648914] using wordTrace_append hprefix tailTrace_648914
  have hstable : (prefixWord ++ tailWord_648914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648914).length < 2 ^ (prefixWord ++ tailWord_648914).sum := by decide
  have hdescent : baseEnd_648914 < baseStart_648914 := by decide
  rcases family_descends (prefixWord ++ tailWord_648914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648920 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_648920 : Nat := 118140960795 + 648920 * 2 ^ 59
def prefixEnd_648920 : Nat := 4983230072969 + 3 ^ 40 * 648920 * 2
def baseEnd_648920 : Nat := 333207866315706331215677

theorem tailTrace_648920 : CollatzResearch.WordTrace tailWord_648920 prefixEnd_648920 333207866315706331215677 := by
  unfold tailWord_648920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834028404540570778872107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15778704539387427705162809 11834028404540570778872107)
  ·
    refine ⟨17751042606810856168308161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11834028404540570778872107 17751042606810856168308161)
    ·
      refine ⟨13313281955108142126231121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17751042606810856168308161 13313281955108142126231121)
      ·
        refine ⟨9984961466331106594673341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13313281955108142126231121 9984961466331106594673341)
        ·
          refine ⟨3744360549874164973002503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9984961466331106594673341 3744360549874164973002503)
          ·
            refine ⟨5616540824811247459503755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744360549874164973002503 5616540824811247459503755)
            ·
              refine ⟨8424811237216871189255633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5616540824811247459503755 8424811237216871189255633)
              ·
                refine ⟨6318608427912653391941725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8424811237216871189255633 6318608427912653391941725)
                ·
                  refine ⟨2369478160467245021978147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6318608427912653391941725 2369478160467245021978147)
                  ·
                    refine ⟨3554217240700867532967221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2369478160467245021978147 3554217240700867532967221)
                    ·
                      refine ⟨333207866315706331215677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3554217240700867532967221 333207866315706331215677)
                      ·
                        rfl

theorem cell23_648920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_648920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648920 prefixEnd_648920 := by exact prefixLift 648920
  have htrace : WordTrace (prefixWord ++ tailWord_648920) baseStart_648920 baseEnd_648920 := by
    simpa [prefixWord, tailWord_648920, baseEnd_648920] using wordTrace_append hprefix tailTrace_648920
  have hstable : (prefixWord ++ tailWord_648920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648920).length < 2 ^ (prefixWord ++ tailWord_648920).sum := by decide
  have hdescent : baseEnd_648920 < baseStart_648920 := by decide
  rcases family_descends (prefixWord ++ tailWord_648920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648951 : List Nat := [1, 1, 3, 1, 1, 1, 4, 6, 1, 2, 2]
def baseStart_648951 : Nat := 118140960795 + 648951 * 2 ^ 59
def prefixEnd_648951 : Nat := 4983230072969 + 3 ^ 40 * 648951 * 2
def baseEnd_648951 : Nat := 333223784215995709928035

theorem tailTrace_648951 : CollatzResearch.WordTrace tailWord_648951 prefixEnd_648951 333223784215995709928035 := by
  unfold tailWord_648951
  simp only [CollatzResearch.WordTrace]
  refine ⟨23669187471968833852122707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15779458314645889234748471 23669187471968833852122707)
  ·
    refine ⟨35503781207953250778184061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23669187471968833852122707 35503781207953250778184061)
    ·
      refine ⟨13313917952982469041819023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35503781207953250778184061 13313917952982469041819023)
      ·
        refine ⟨19970876929473703562728535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13313917952982469041819023 19970876929473703562728535)
        ·
          refine ⟨29956315394210555344092803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19970876929473703562728535 29956315394210555344092803)
          ·
            refine ⟨44934473091315833016139205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29956315394210555344092803 44934473091315833016139205)
            ·
              refine ⟨8425213704621718690526101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44934473091315833016139205 8425213704621718690526101)
              ·
                refine ⟨394931892404143063618411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8425213704621718690526101 394931892404143063618411)
                ·
                  refine ⟨592397838606214595427617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394931892404143063618411 592397838606214595427617)
                  ·
                    refine ⟨444298378954660946570713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 592397838606214595427617 444298378954660946570713)
                    ·
                      refine ⟨333223784215995709928035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444298378954660946570713 333223784215995709928035)
                      ·
                        rfl

theorem cell23_648951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_648951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_648951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_648951 prefixEnd_648951 := by exact prefixLift 648951
  have htrace : WordTrace (prefixWord ++ tailWord_648951) baseStart_648951 baseEnd_648951 := by
    simpa [prefixWord, tailWord_648951, baseEnd_648951] using wordTrace_append hprefix tailTrace_648951
  have hstable : (prefixWord ++ tailWord_648951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648951).length < 2 ^ (prefixWord ++ tailWord_648951).sum := by decide
  have hdescent : baseEnd_648951 < baseStart_648951 := by decide
  rcases family_descends (prefixWord ++ tailWord_648951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649024 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 8, 2, 2]
def baseStart_649024 : Nat := 118140960795 + 649024 * 2 ^ 59
def prefixEnd_649024 : Nat := 4983230072969 + 3 ^ 40 * 649024 * 2
def baseEnd_649024 : Nat := 333261268303773924315199

theorem tailTrace_649024 : CollatzResearch.WordTrace tailWord_649024 prefixEnd_649024 333261268303773924315199 := by
  unfold tailWord_649024
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835925000352183659765063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15781233333802911546353417 11835925000352183659765063)
  ·
    refine ⟨17753887500528275489647595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11835925000352183659765063 17753887500528275489647595)
    ·
      refine ⟨26630831250792413234471393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17753887500528275489647595 26630831250792413234471393)
      ·
        refine ⟨19973123438094309925853545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26630831250792413234471393 19973123438094309925853545)
        ·
          refine ⟨14979842578570732444390159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19973123438094309925853545 14979842578570732444390159)
          ·
            refine ⟨22469763867856098666585239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14979842578570732444390159 22469763867856098666585239)
            ·
              refine ⟨33704645801784147999877859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22469763867856098666585239 33704645801784147999877859)
              ·
                refine ⟨50556968702676221999816789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33704645801784147999877859 50556968702676221999816789)
                ·
                  refine ⟨592464476984486976560353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 50556968702676221999816789 592464476984486976560353)
                  ·
                    refine ⟨444348357738365232420265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 592464476984486976560353 444348357738365232420265)
                    ·
                      refine ⟨333261268303773924315199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444348357738365232420265 333261268303773924315199)
                      ·
                        rfl

theorem cell23_649024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_649024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649024 prefixEnd_649024 := by exact prefixLift 649024
  have htrace : WordTrace (prefixWord ++ tailWord_649024) baseStart_649024 baseEnd_649024 := by
    simpa [prefixWord, tailWord_649024, baseEnd_649024] using wordTrace_append hprefix tailTrace_649024
  have hstable : (prefixWord ++ tailWord_649024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649024).length < 2 ^ (prefixWord ++ tailWord_649024).sum := by decide
  have hdescent : baseEnd_649024 < baseStart_649024 := by decide
  rcases family_descends (prefixWord ++ tailWord_649024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649040 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_649040 : Nat := 118140960795 + 649040 * 2 ^ 59
def prefixEnd_649040 : Nat := 4983230072969 + 3 ^ 40 * 649040 * 2
def baseEnd_649040 : Nat := 333269483994245861715125

theorem tailTrace_649040 : CollatzResearch.WordTrace tailWord_649040 prefixEnd_649040 333269483994245861715125 := by
  unfold tailWord_649040
  simp only [CollatzResearch.WordTrace]
  refine ⟨11836216784323201026056287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15781622379097601368075049 11836216784323201026056287)
  ·
    refine ⟨17754325176484801539084431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11836216784323201026056287 17754325176484801539084431)
    ·
      refine ⟨26631487764727202308626647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17754325176484801539084431 26631487764727202308626647)
      ·
        refine ⟨39947231647090803462939971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26631487764727202308626647 39947231647090803462939971)
        ·
          refine ⟨59920847470636205194409957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39947231647090803462939971 59920847470636205194409957)
          ·
            refine ⟨11235158900744288473951867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59920847470636205194409957 11235158900744288473951867)
            ·
              refine ⟨16852738351116432710927801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11235158900744288473951867 16852738351116432710927801)
              ·
                refine ⟨12639553763337324533195851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16852738351116432710927801 12639553763337324533195851)
                ·
                  refine ⟨18959330645005986799793777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12639553763337324533195851 18959330645005986799793777)
                  ·
                    refine ⟨14219497983754490099845333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18959330645005986799793777 14219497983754490099845333)
                    ·
                      refine ⟨333269483994245861715125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14219497983754490099845333 333269483994245861715125)
                      ·
                        rfl

theorem cell23_649040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_649040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649040 prefixEnd_649040 := by exact prefixLift 649040
  have htrace : WordTrace (prefixWord ++ tailWord_649040) baseStart_649040 baseEnd_649040 := by
    simpa [prefixWord, tailWord_649040, baseEnd_649040] using wordTrace_append hprefix tailTrace_649040
  have hstable : (prefixWord ++ tailWord_649040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649040).length < 2 ^ (prefixWord ++ tailWord_649040).sum := by decide
  have hdescent : baseEnd_649040 < baseStart_649040 := by decide
  rcases family_descends (prefixWord ++ tailWord_649040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649057 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_649057 : Nat := 118140960795 + 649057 * 2 ^ 59
def prefixEnd_649057 : Nat := 4983230072969 + 3 ^ 40 * 649057 * 2
def baseEnd_649057 : Nat := 333278213165372295202547

theorem tailTrace_649057 : CollatzResearch.WordTrace tailWord_649057 prefixEnd_649057 333278213165372295202547 := by
  unfold tailWord_649057
  simp only [CollatzResearch.WordTrace]
  refine ⟨23673053609584813955481425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15782035739723209303654283 23673053609584813955481425)
  ·
    refine ⟨17754790207188610466611069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23673053609584813955481425 17754790207188610466611069)
    ·
      refine ⟨6658046327695728924979151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17754790207188610466611069 6658046327695728924979151)
      ·
        refine ⟨9987069491543593387468727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6658046327695728924979151 9987069491543593387468727)
        ·
          refine ⟨14980604237315390081203091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9987069491543593387468727 14980604237315390081203091)
          ·
            refine ⟨22470906355973085121804637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14980604237315390081203091 22470906355973085121804637)
            ·
              refine ⟨8426589883489906920676739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22470906355973085121804637 8426589883489906920676739)
              ·
                refine ⟨12639884825234860381015109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8426589883489906920676739 12639884825234860381015109)
                ·
                  refine ⟨2369978404731536321440333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12639884825234860381015109 2369978404731536321440333)
                  ·
                    refine ⟨888741901774326120540125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369978404731536321440333 888741901774326120540125)
                    ·
                      refine ⟨333278213165372295202547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 888741901774326120540125 333278213165372295202547)
                      ·
                        rfl

theorem cell23_649057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_649057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649057 prefixEnd_649057 := by exact prefixLift 649057
  have htrace : WordTrace (prefixWord ++ tailWord_649057) baseStart_649057 baseEnd_649057 := by
    simpa [prefixWord, tailWord_649057, baseEnd_649057] using wordTrace_append hprefix tailTrace_649057
  have hstable : (prefixWord ++ tailWord_649057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649057).length < 2 ^ (prefixWord ++ tailWord_649057).sum := by decide
  have hdescent : baseEnd_649057 < baseStart_649057 := by decide
  rcases family_descends (prefixWord ++ tailWord_649057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649058 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_649058 : Nat := 118140960795 + 649058 * 2 ^ 59
def prefixEnd_649058 : Nat := 4983230072969 + 3 ^ 40 * 649058 * 2
def baseEnd_649058 : Nat := 333278726646026791290043

theorem tailTrace_649058 : CollatzResearch.WordTrace tailWord_649058 prefixEnd_649058 333278726646026791290043 := by
  unfold tailWord_649058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918272520645297781566957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15782060055054127417511885 5918272520645297781566957)
  ·
    refine ⟨2219352195241986668087609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5918272520645297781566957 2219352195241986668087609)
    ·
      refine ⟨1664514146431490001065707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2219352195241986668087609 1664514146431490001065707)
      ·
        refine ⟨2496771219647235001598561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664514146431490001065707 2496771219647235001598561)
        ·
          refine ⟨1872578414735426251198921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496771219647235001598561 1872578414735426251198921)
          ·
            refine ⟨1404433811051569688399191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872578414735426251198921 1404433811051569688399191)
            ·
              refine ⟨2106650716577354532598787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404433811051569688399191 2106650716577354532598787)
              ·
                refine ⟨3159976074866031798898181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106650716577354532598787 3159976074866031798898181)
                ·
                  refine ⟨592495514037380962293409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3159976074866031798898181 592495514037380962293409)
                  ·
                    refine ⟨444371635528035721720057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 592495514037380962293409 444371635528035721720057)
                    ·
                      refine ⟨333278726646026791290043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444371635528035721720057 333278726646026791290043)
                      ·
                        rfl

theorem cell23_649058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_649058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649058 prefixEnd_649058 := by exact prefixLift 649058
  have htrace : WordTrace (prefixWord ++ tailWord_649058) baseStart_649058 baseEnd_649058 := by
    simpa [prefixWord, tailWord_649058, baseEnd_649058] using wordTrace_append hprefix tailTrace_649058
  have hstable : (prefixWord ++ tailWord_649058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649058).length < 2 ^ (prefixWord ++ tailWord_649058).sum := by decide
  have hdescent : baseEnd_649058 < baseStart_649058 := by decide
  rcases family_descends (prefixWord ++ tailWord_649058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649064 : List Nat := [2, 1, 4, 2, 1, 1, 1, 6, 5]
def baseStart_649064 : Nat := 118140960795 + 649064 * 2 ^ 59
def prefixEnd_649064 : Nat := 4983230072969 + 3 ^ 40 * 649064 * 2
def baseEnd_649064 : Nat := 37031311947772640868335

theorem tailTrace_649064 : CollatzResearch.WordTrace tailWord_649064 prefixEnd_649064 37031311947772640868335 := by
  unfold tailWord_649064
  simp only [CollatzResearch.WordTrace]
  refine ⟨11836654460279727075493123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15782205947039636100657497 11836654460279727075493123)
  ·
    refine ⟨17754981690419590613239685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11836654460279727075493123 17754981690419590613239685)
    ·
      refine ⟨3329059066953673239982441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17754981690419590613239685 3329059066953673239982441)
      ·
        refine ⟨2496794300215254929986831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3329059066953673239982441 2496794300215254929986831)
        ·
          refine ⟨3745191450322882394980247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496794300215254929986831 3745191450322882394980247)
          ·
            refine ⟨5617787175484323592470371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3745191450322882394980247 5617787175484323592470371)
            ·
              refine ⟨8426680763226485388705557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617787175484323592470371 8426680763226485388705557)
              ·
                refine ⟨395000660776241502595573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8426680763226485388705557 395000660776241502595573)
                ·
                  refine ⟨37031311947772640868335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 395000660776241502595573 37031311947772640868335)
                  ·
                    rfl

theorem cell23_649064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 5].length) (baseStart_649064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649064 prefixEnd_649064 := by exact prefixLift 649064
  have htrace : WordTrace (prefixWord ++ tailWord_649064) baseStart_649064 baseEnd_649064 := by
    simpa [prefixWord, tailWord_649064, baseEnd_649064] using wordTrace_append hprefix tailTrace_649064
  have hstable : (prefixWord ++ tailWord_649064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649064).length < 2 ^ (prefixWord ++ tailWord_649064).sum := by decide
  have hdescent : baseEnd_649064 < baseStart_649064 := by decide
  rcases family_descends (prefixWord ++ tailWord_649064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649077 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_649077 : Nat := 118140960795 + 649077 * 2 ^ 59
def prefixEnd_649077 : Nat := 4983230072969 + 3 ^ 40 * 649077 * 2
def baseEnd_649077 : Nat := 111096160926154072317485

theorem tailTrace_649077 : CollatzResearch.WordTrace tailWord_649077 prefixEnd_649077 111096160926154072317485 := by
  unfold tailWord_649077
  simp only [CollatzResearch.WordTrace]
  refine ⟨23673783069512357371209485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15782522046341571580806323 23673783069512357371209485)
  ·
    refine ⟨8877668651067134014203557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23673783069512357371209485 8877668651067134014203557)
    ·
      refine ⟨1664562872075087627663167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8877668651067134014203557 1664562872075087627663167)
      ·
        refine ⟨2496844308112631441494751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664562872075087627663167 2496844308112631441494751)
        ·
          refine ⟨3745266462168947162242127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496844308112631441494751 3745266462168947162242127)
          ·
            refine ⟨5617899693253420743363191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3745266462168947162242127 5617899693253420743363191)
            ·
              refine ⟨8426849539880131115044787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617899693253420743363191 8426849539880131115044787)
              ·
                refine ⟨12640274309820196672567181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8426849539880131115044787 12640274309820196672567181)
                ·
                  refine ⟨4740102866182573752212693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12640274309820196672567181 4740102866182573752212693)
                  ·
                    refine ⟨111096160926154072317485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4740102866182573752212693 111096160926154072317485)
                    ·
                      rfl

theorem cell23_649077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_649077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649077 prefixEnd_649077 := by exact prefixLift 649077
  have htrace : WordTrace (prefixWord ++ tailWord_649077) baseStart_649077 baseEnd_649077 := by
    simpa [prefixWord, tailWord_649077, baseEnd_649077] using wordTrace_append hprefix tailTrace_649077
  have hstable : (prefixWord ++ tailWord_649077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649077).length < 2 ^ (prefixWord ++ tailWord_649077).sum := by decide
  have hdescent : baseEnd_649077 < baseStart_649077 := by decide
  rcases family_descends (prefixWord ++ tailWord_649077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649097 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_649097 : Nat := 118140960795 + 649097 * 2 ^ 59
def prefixEnd_649097 : Nat := 4983230072969 + 3 ^ 40 * 649097 * 2
def baseEnd_649097 : Nat := 333298752391552138702363

theorem tailTrace_649097 : CollatzResearch.WordTrace tailWord_649097 prefixEnd_649097 333298752391552138702363 := by
  unfold tailWord_649097
  simp only [CollatzResearch.WordTrace]
  refine ⟨23674512529439900786937545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15783008352959933857958363 23674512529439900786937545)
  ·
    refine ⟨17755884397079925590203159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23674512529439900786937545 17755884397079925590203159)
    ·
      refine ⟨26633826595619888385304739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17755884397079925590203159 26633826595619888385304739)
      ·
        refine ⟨39950739893429832577957109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26633826595619888385304739 39950739893429832577957109)
        ·
          refine ⟨3745381865009046804183479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39950739893429832577957109 3745381865009046804183479)
          ·
            refine ⟨5618072797513570206275219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3745381865009046804183479 5618072797513570206275219)
            ·
              refine ⟨8427109196270355309412829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5618072797513570206275219 8427109196270355309412829)
              ·
                refine ⟨3160165948601383241029811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8427109196270355309412829 3160165948601383241029811)
                ·
                  refine ⟨4740248922902074861544717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160165948601383241029811 4740248922902074861544717)
                  ·
                    refine ⟨1777593346088278073079269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4740248922902074861544717 1777593346088278073079269)
                    ·
                      refine ⟨333298752391552138702363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1777593346088278073079269 333298752391552138702363)
                      ·
                        rfl

theorem cell23_649097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_649097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649097 prefixEnd_649097 := by exact prefixLift 649097
  have htrace : WordTrace (prefixWord ++ tailWord_649097) baseStart_649097 baseEnd_649097 := by
    simpa [prefixWord, tailWord_649097, baseEnd_649097] using wordTrace_append hprefix tailTrace_649097
  have hstable : (prefixWord ++ tailWord_649097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649097).length < 2 ^ (prefixWord ++ tailWord_649097).sum := by decide
  have hdescent : baseEnd_649097 < baseStart_649097 := by decide
  rcases family_descends (prefixWord ++ tailWord_649097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649098 : List Nat := [3, 1, 2, 4, 2, 2, 1, 3, 5]
def baseStart_649098 : Nat := 118140960795 + 649098 * 2 ^ 59
def prefixEnd_649098 : Nat := 4983230072969 + 3 ^ 40 * 649098 * 2
def baseEnd_649098 : Nat := 37033251763578514976651

theorem tailTrace_649098 : CollatzResearch.WordTrace tailWord_649098 prefixEnd_649098 37033251763578514976651 := by
  unfold tailWord_649098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918637250609069489430987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15783032668290851971815965 5918637250609069489430987)
  ·
    refine ⟨8877955875913604234146481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5918637250609069489430987 8877955875913604234146481)
    ·
      refine ⟨6658466906935203175609861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8877955875913604234146481 6658466906935203175609861)
      ·
        refine ⟨1248462545050350595426849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6658466906935203175609861 1248462545050350595426849)
        ·
          refine ⟨936346908787762946570137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1248462545050350595426849 936346908787762946570137)
          ·
            refine ⟨702260181590822209927603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936346908787762946570137 702260181590822209927603)
            ·
              refine ⟨1053390272386233314891405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702260181590822209927603 1053390272386233314891405)
              ·
                refine ⟨395021352144837493084277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053390272386233314891405 395021352144837493084277)
                ·
                  refine ⟨37033251763578514976651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 395021352144837493084277 37033251763578514976651)
                  ·
                    rfl

theorem cell23_649098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_649098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649098 prefixEnd_649098 := by exact prefixLift 649098
  have htrace : WordTrace (prefixWord ++ tailWord_649098) baseStart_649098 baseEnd_649098 := by
    simpa [prefixWord, tailWord_649098, baseEnd_649098] using wordTrace_append hprefix tailTrace_649098
  have hstable : (prefixWord ++ tailWord_649098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649098).length < 2 ^ (prefixWord ++ tailWord_649098).sum := by decide
  have hdescent : baseEnd_649098 < baseStart_649098 := by decide
  rcases family_descends (prefixWord ++ tailWord_649098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649114 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_649114 : Nat := 118140960795 + 649114 * 2 ^ 59
def prefixEnd_649114 : Nat := 4983230072969 + 3 ^ 40 * 649114 * 2
def baseEnd_649114 : Nat := 333307481562678572189785

theorem tailTrace_649114 : CollatzResearch.WordTrace tailWord_649114 prefixEnd_649114 333307481562678572189785 := by
  unfold tailWord_649114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918783142594578172576599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15783421713585541793537597 5918783142594578172576599)
  ·
    refine ⟨8878174713891867258864899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5918783142594578172576599 8878174713891867258864899)
    ·
      refine ⟨13317262070837800888297349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8878174713891867258864899 13317262070837800888297349)
      ·
        refine ⟨2496986638282087666555753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13317262070837800888297349 2496986638282087666555753)
        ·
          refine ⟨1872739978711565749916815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496986638282087666555753 1872739978711565749916815)
          ·
            refine ⟨2809109968067348624875223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872739978711565749916815 2809109968067348624875223)
            ·
              refine ⟨4213664952101022937312835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809109968067348624875223 4213664952101022937312835)
              ·
                refine ⟨6320497428151534405969253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4213664952101022937312835 6320497428151534405969253)
                ·
                  refine ⟨1185093267778412701119235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6320497428151534405969253 1185093267778412701119235)
                  ·
                    refine ⟨1777639901667619051678853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185093267778412701119235 1777639901667619051678853)
                    ·
                      refine ⟨333307481562678572189785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1777639901667619051678853 333307481562678572189785)
                      ·
                        rfl

theorem cell23_649114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_649114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649114 prefixEnd_649114 := by exact prefixLift 649114
  have htrace : WordTrace (prefixWord ++ tailWord_649114) baseStart_649114 baseEnd_649114 := by
    simpa [prefixWord, tailWord_649114, baseEnd_649114] using wordTrace_append hprefix tailTrace_649114
  have hstable : (prefixWord ++ tailWord_649114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649114).length < 2 ^ (prefixWord ++ tailWord_649114).sum := by decide
  have hdescent : baseEnd_649114 < baseStart_649114 := by decide
  rcases family_descends (prefixWord ++ tailWord_649114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649147 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 3]
def baseStart_649147 : Nat := 118140960795 + 649147 * 2 ^ 59
def prefixEnd_649147 : Nat := 4983230072969 + 3 ^ 40 * 649147 * 2
def baseEnd_649147 : Nat := 333324426424276943077133

theorem tailTrace_649147 : CollatzResearch.WordTrace tailWord_649147 prefixEnd_649147 333324426424276943077133 := by
  unfold tailWord_649147
  simp only [CollatzResearch.WordTrace]
  refine ⟨23676336179258759326257695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15784224119505839550838463 23676336179258759326257695)
  ·
    refine ⟨35514504268888138989386543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23676336179258759326257695 35514504268888138989386543)
    ·
      refine ⟨53271756403332208484079815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35514504268888138989386543 53271756403332208484079815)
      ·
        refine ⟨79907634604998312726119723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53271756403332208484079815 79907634604998312726119723)
        ·
          refine ⟨119861451907497469089179585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79907634604998312726119723 119861451907497469089179585)
          ·
            refine ⟨89896088930623101816884689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119861451907497469089179585 89896088930623101816884689)
            ·
              refine ⟨67422066697967326362663517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89896088930623101816884689 67422066697967326362663517)
              ·
                refine ⟨25283275011737747385998819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67422066697967326362663517 25283275011737747385998819)
                ·
                  refine ⟨37924912517606621078998229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25283275011737747385998819 37924912517606621078998229)
                  ·
                    refine ⟨888865137131405181539021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37924912517606621078998229 888865137131405181539021)
                    ·
                      refine ⟨333324426424276943077133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 888865137131405181539021 333324426424276943077133)
                      ·
                        rfl

theorem cell23_649147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 3].length) (baseStart_649147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649147 prefixEnd_649147 := by exact prefixLift 649147
  have htrace : WordTrace (prefixWord ++ tailWord_649147) baseStart_649147 baseEnd_649147 := by
    simpa [prefixWord, tailWord_649147, baseEnd_649147] using wordTrace_append hprefix tailTrace_649147
  have hstable : (prefixWord ++ tailWord_649147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649147).length < 2 ^ (prefixWord ++ tailWord_649147).sum := by decide
  have hdescent : baseEnd_649147 < baseStart_649147 := by decide
  rcases family_descends (prefixWord ++ tailWord_649147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649148 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_649148 : Nat := 118140960795 + 649148 * 2 ^ 59
def prefixEnd_649148 : Nat := 4983230072969 + 3 ^ 40 * 649148 * 2
def baseEnd_649148 : Nat := 333324939904931439164629

theorem tailTrace_649148 : CollatzResearch.WordTrace tailWord_649148 prefixEnd_649148 333324939904931439164629 := by
  unfold tailWord_649148
  simp only [CollatzResearch.WordTrace]
  refine ⟨11838186326127568248522049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15784248434836757664696065 11838186326127568248522049)
  ·
    refine ⟨8878639744595676186391537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11838186326127568248522049 8878639744595676186391537)
    ·
      refine ⟨6658979808446757139793653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8878639744595676186391537 6658979808446757139793653)
      ·
        refine ⟨624279357041883481855655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6658979808446757139793653 624279357041883481855655)
        ·
          refine ⟨936419035562825222783483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624279357041883481855655 936419035562825222783483)
          ·
            refine ⟨1404628553344237834175225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936419035562825222783483 1404628553344237834175225)
            ·
              refine ⟨1053471415008178375631419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404628553344237834175225 1053471415008178375631419)
              ·
                refine ⟨1580207122512267563447129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053471415008178375631419 1580207122512267563447129)
                ·
                  refine ⟨1185155341884200672585347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1580207122512267563447129 1185155341884200672585347)
                  ·
                    refine ⟨1777733012826301008878021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185155341884200672585347 1777733012826301008878021)
                    ·
                      refine ⟨333324939904931439164629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1777733012826301008878021 333324939904931439164629)
                      ·
                        rfl

theorem cell23_649148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_649148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649148 prefixEnd_649148 := by exact prefixLift 649148
  have htrace : WordTrace (prefixWord ++ tailWord_649148) baseStart_649148 baseEnd_649148 := by
    simpa [prefixWord, tailWord_649148, baseEnd_649148] using wordTrace_append hprefix tailTrace_649148
  have hstable : (prefixWord ++ tailWord_649148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649148).length < 2 ^ (prefixWord ++ tailWord_649148).sum := by decide
  have hdescent : baseEnd_649148 < baseStart_649148 := by decide
  rcases family_descends (prefixWord ++ tailWord_649148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649198 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_649198 : Nat := 118140960795 + 649198 * 2 ^ 59
def prefixEnd_649198 : Nat := 4983230072969 + 3 ^ 40 * 649198 * 2
def baseEnd_649198 : Nat := 333350613937656243539399

theorem tailTrace_649198 : CollatzResearch.WordTrace tailWord_649198 prefixEnd_649198 333350613937656243539399 := by
  unfold tailWord_649198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959774537759249379545531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15785464201382663357576165 2959774537759249379545531)
  ·
    refine ⟨4439661806638874069318297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2959774537759249379545531 4439661806638874069318297)
    ·
      refine ⟨3329746354979155551988723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4439661806638874069318297 3329746354979155551988723)
      ·
        refine ⟨4994619532468733327983085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3329746354979155551988723 4994619532468733327983085)
        ·
          refine ⟨1872982324675774997993657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4994619532468733327983085 1872982324675774997993657)
          ·
            refine ⟨1404736743506831248495243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872982324675774997993657 1404736743506831248495243)
            ·
              refine ⟨2107105115260246872742865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404736743506831248495243 2107105115260246872742865)
              ·
                refine ⟨1580328836445185154557149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2107105115260246872742865 1580328836445185154557149)
                ·
                  refine ⟨592623313666944432958931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1580328836445185154557149 592623313666944432958931)
                  ·
                    refine ⟨888934970500416649438397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 592623313666944432958931 888934970500416649438397)
                    ·
                      refine ⟨333350613937656243539399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 888934970500416649438397 333350613937656243539399)
                      ·
                        rfl

theorem cell23_649198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_649198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649198 prefixEnd_649198 := by exact prefixLift 649198
  have htrace : WordTrace (prefixWord ++ tailWord_649198) baseStart_649198 baseEnd_649198 := by
    simpa [prefixWord, tailWord_649198, baseEnd_649198] using wordTrace_append hprefix tailTrace_649198
  have hstable : (prefixWord ++ tailWord_649198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649198).length < 2 ^ (prefixWord ++ tailWord_649198).sum := by decide
  have hdescent : baseEnd_649198 < baseStart_649198 := by decide
  rcases family_descends (prefixWord ++ tailWord_649198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649221 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_649221 : Nat := 118140960795 + 649221 * 2 ^ 59
def prefixEnd_649221 : Nat := 4983230072969 + 3 ^ 40 * 649221 * 2
def baseEnd_649221 : Nat := 333362423992709653551793

theorem tailTrace_649221 : CollatzResearch.WordTrace tailWord_649221 prefixEnd_649221 333362423992709653551793 := by
  unfold tailWord_649221
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679035180990669964451517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15786023453993779976301011 23679035180990669964451517)
  ·
    refine ⟨8879638192871501236669319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23679035180990669964451517 8879638192871501236669319)
    ·
      refine ⟨13319457289307251855003979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8879638192871501236669319 13319457289307251855003979)
      ·
        refine ⟨19979185933960877782505969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13319457289307251855003979 19979185933960877782505969)
        ·
          refine ⟨14984389450470658336879477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19979185933960877782505969 14984389450470658336879477)
          ·
            refine ⟨1404786510981624219082451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14984389450470658336879477 1404786510981624219082451)
            ·
              refine ⟨2107179766472436328623677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404786510981624219082451 2107179766472436328623677)
              ·
                refine ⟨790192412427163623233879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2107179766472436328623677 790192412427163623233879)
                ·
                  refine ⟨1185288618640745434850819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790192412427163623233879 1185288618640745434850819)
                  ·
                    refine ⟨1777932927961118152276229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185288618640745434850819 1777932927961118152276229)
                    ·
                      refine ⟨333362423992709653551793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1777932927961118152276229 333362423992709653551793)
                      ·
                        rfl

theorem cell23_649221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_649221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649221 prefixEnd_649221 := by exact prefixLift 649221
  have htrace : WordTrace (prefixWord ++ tailWord_649221) baseStart_649221 baseEnd_649221 := by
    simpa [prefixWord, tailWord_649221, baseEnd_649221] using wordTrace_append hprefix tailTrace_649221
  have hstable : (prefixWord ++ tailWord_649221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649221).length < 2 ^ (prefixWord ++ tailWord_649221).sum := by decide
  have hdescent : baseEnd_649221 < baseStart_649221 := by decide
  rcases family_descends (prefixWord ++ tailWord_649221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649224 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_649224 : Nat := 118140960795 + 649224 * 2 ^ 59
def prefixEnd_649224 : Nat := 4983230072969 + 3 ^ 40 * 649224 * 2
def baseEnd_649224 : Nat := 333363964434673141814279

theorem tailTrace_649224 : CollatzResearch.WordTrace tailWord_649224 prefixEnd_649224 333363964434673141814279 := by
  unfold tailWord_649224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11839572299989900738405363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15786096399986534317873817 11839572299989900738405363)
  ·
    refine ⟨17759358449984851107608045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11839572299989900738405363 17759358449984851107608045)
    ·
      refine ⟨6659759418744319165353017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17759358449984851107608045 6659759418744319165353017)
      ·
        refine ⟨4994819564058239374014763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6659759418744319165353017 4994819564058239374014763)
        ·
          refine ⟨7492229346087359061022145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4994819564058239374014763 7492229346087359061022145)
          ·
            refine ⟨5619172009565519295766609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7492229346087359061022145 5619172009565519295766609)
            ·
              refine ⟨4214379007174139471824957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5619172009565519295766609 4214379007174139471824957)
              ·
                refine ⟨1580392127690302301934359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4214379007174139471824957 1580392127690302301934359)
                ·
                  refine ⟨2370588191535453452901539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580392127690302301934359 2370588191535453452901539)
                  ·
                    refine ⟨3555882287303180179352309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2370588191535453452901539 3555882287303180179352309)
                    ·
                      refine ⟨333363964434673141814279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3555882287303180179352309 333363964434673141814279)
                      ·
                        rfl

theorem cell23_649224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_649224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649224 prefixEnd_649224 := by exact prefixLift 649224
  have htrace : WordTrace (prefixWord ++ tailWord_649224) baseStart_649224 baseEnd_649224 := by
    simpa [prefixWord, tailWord_649224, baseEnd_649224] using wordTrace_append hprefix tailTrace_649224
  have hstable : (prefixWord ++ tailWord_649224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649224).length < 2 ^ (prefixWord ++ tailWord_649224).sum := by decide
  have hdescent : baseEnd_649224 < baseStart_649224 := by decide
  rcases family_descends (prefixWord ++ tailWord_649224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649227 : List Nat := [1, 1, 1, 1, 6, 1, 12]
def baseStart_649227 : Nat := 118140960795 + 649227 * 2 ^ 59
def prefixEnd_649227 : Nat := 4983230072969 + 3 ^ 40 * 649227 * 2
def baseEnd_649227 : Nat := 4115623516995513951565

theorem tailTrace_649227 : CollatzResearch.WordTrace tailWord_649227 prefixEnd_649227 4115623516995513951565 := by
  unfold tailWord_649227
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679254018968932989169935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15786169345979288659446623 23679254018968932989169935)
  ·
    refine ⟨35518881028453399483754903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23679254018968932989169935 35518881028453399483754903)
    ·
      refine ⟨53278321542680099225632355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35518881028453399483754903 53278321542680099225632355)
      ·
        refine ⟨79917482314020148838448533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53278321542680099225632355 79917482314020148838448533)
        ·
          refine ⟨3746131983469694476802275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79917482314020148838448533 3746131983469694476802275)
          ·
            refine ⟨5619197975204541715203413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746131983469694476802275 5619197975204541715203413)
            ·
              refine ⟨4115623516995513951565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 5619197975204541715203413 4115623516995513951565)
              ·
                rfl

theorem cell23_649227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 12].length) (baseStart_649227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649227 prefixEnd_649227 := by exact prefixLift 649227
  have htrace : WordTrace (prefixWord ++ tailWord_649227) baseStart_649227 baseEnd_649227 := by
    simpa [prefixWord, tailWord_649227, baseEnd_649227] using wordTrace_append hprefix tailTrace_649227
  have hstable : (prefixWord ++ tailWord_649227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649227).length < 2 ^ (prefixWord ++ tailWord_649227).sum := by decide
  have hdescent : baseEnd_649227 < baseStart_649227 := by decide
  rcases family_descends (prefixWord ++ tailWord_649227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649255 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_649255 : Nat := 118140960795 + 649255 * 2 ^ 59
def prefixEnd_649255 : Nat := 4983230072969 + 3 ^ 40 * 649255 * 2
def baseEnd_649255 : Nat := 333379882334962520526637

theorem tailTrace_649255 : CollatzResearch.WordTrace tailWord_649255 prefixEnd_649255 333379882334962520526637 := by
  unfold tailWord_649255
  simp only [CollatzResearch.WordTrace]
  refine ⟨23680275262867493771189219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15786850175244995847459479 23680275262867493771189219)
  ·
    refine ⟨35520412894301240656783829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23680275262867493771189219 35520412894301240656783829)
    ·
      refine ⟨832509677210185327893371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 35520412894301240656783829 832509677210185327893371)
      ·
        refine ⟨1248764515815277991840057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832509677210185327893371 1248764515815277991840057)
        ·
          refine ⟨936573386861458493880043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1248764515815277991840057 936573386861458493880043)
          ·
            refine ⟨1404860080292187740820065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936573386861458493880043 1404860080292187740820065)
            ·
              refine ⟨1053645060219140805615049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404860080292187740820065 1053645060219140805615049)
              ·
                refine ⟨790233795164355604211287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053645060219140805615049 790233795164355604211287)
                ·
                  refine ⟨1185350692746533406316931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790233795164355604211287 1185350692746533406316931)
                  ·
                    refine ⟨1778026039119800109475397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185350692746533406316931 1778026039119800109475397)
                    ·
                      refine ⟨333379882334962520526637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1778026039119800109475397 333379882334962520526637)
                      ·
                        rfl

theorem cell23_649255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_649255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649255 prefixEnd_649255 := by exact prefixLift 649255
  have htrace : WordTrace (prefixWord ++ tailWord_649255) baseStart_649255 baseEnd_649255 := by
    simpa [prefixWord, tailWord_649255, baseEnd_649255] using wordTrace_append hprefix tailTrace_649255
  have hstable : (prefixWord ++ tailWord_649255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649255).length < 2 ^ (prefixWord ++ tailWord_649255).sum := by decide
  have hdescent : baseEnd_649255 < baseStart_649255 := by decide
  rcases family_descends (prefixWord ++ tailWord_649255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649257 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 9]
def baseStart_649257 : Nat := 118140960795 + 649257 * 2 ^ 59
def prefixEnd_649257 : Nat := 4983230072969 + 3 ^ 40 * 649257 * 2
def baseEnd_649257 : Nat := 111126969765423837567209

theorem tailTrace_649257 : CollatzResearch.WordTrace tailWord_649257 prefixEnd_649257 111126969765423837567209 := by
  unfold tailWord_649257
  simp only [CollatzResearch.WordTrace]
  refine ⟨23680348208860248112762025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15786898805906832075174683 23680348208860248112762025)
  ·
    refine ⟨17760261156645186084571519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23680348208860248112762025 17760261156645186084571519)
    ·
      refine ⟨26640391734967779126857279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17760261156645186084571519 26640391734967779126857279)
      ·
        refine ⟨39960587602451668690285919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26640391734967779126857279 39960587602451668690285919)
        ·
          refine ⟨59940881403677503035428879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39960587602451668690285919 59940881403677503035428879)
          ·
            refine ⟨89911322105516254553143319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59940881403677503035428879 89911322105516254553143319)
            ·
              refine ⟨134866983158274381829714979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89911322105516254553143319 134866983158274381829714979)
              ·
                refine ⟨202300474737411572744572469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134866983158274381829714979 202300474737411572744572469)
                ·
                  refine ⟨18965669506632334944803669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202300474737411572744572469 18965669506632334944803669)
                  ·
                    refine ⟨111126969765423837567209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 18965669506632334944803669 111126969765423837567209)
                    ·
                      rfl

theorem cell23_649257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_649257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649257 prefixEnd_649257 := by exact prefixLift 649257
  have htrace : WordTrace (prefixWord ++ tailWord_649257) baseStart_649257 baseEnd_649257 := by
    simpa [prefixWord, tailWord_649257, baseEnd_649257] using wordTrace_append hprefix tailTrace_649257
  have hstable : (prefixWord ++ tailWord_649257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649257).length < 2 ^ (prefixWord ++ tailWord_649257).sum := by decide
  have hdescent : baseEnd_649257 < baseStart_649257 := by decide
  rcases family_descends (prefixWord ++ tailWord_649257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649258 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_649258 : Nat := 118140960795 + 649258 * 2 ^ 59
def prefixEnd_649258 : Nat := 4983230072969 + 3 ^ 40 * 649258 * 2
def baseEnd_649258 : Nat := 333381422776926008789123

theorem tailTrace_649258 : CollatzResearch.WordTrace tailWord_649258 prefixEnd_649258 333381422776926008789123 := by
  unfold tailWord_649258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5920096170464156320887107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15786923121237750189032285 5920096170464156320887107)
  ·
    refine ⟨8880144255696234481330661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5920096170464156320887107 8880144255696234481330661)
    ·
      refine ⟨1665027047943043965249499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8880144255696234481330661 1665027047943043965249499)
      ·
        refine ⟨2497540571914565947874249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665027047943043965249499 2497540571914565947874249)
        ·
          refine ⟨1873155428935924460905687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2497540571914565947874249 1873155428935924460905687)
          ·
            refine ⟨2809733143403886691358531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873155428935924460905687 2809733143403886691358531)
            ·
              refine ⟨4214599715105830037037797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809733143403886691358531 4214599715105830037037797)
              ·
                refine ⟨790237446582343131944587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4214599715105830037037797 790237446582343131944587)
                ·
                  refine ⟨1185356169873514697916881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790237446582343131944587 1185356169873514697916881)
                  ·
                    refine ⟨889017127405136023437661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185356169873514697916881 889017127405136023437661)
                    ·
                      refine ⟨333381422776926008789123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 889017127405136023437661 333381422776926008789123)
                      ·
                        rfl

theorem cell23_649258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_649258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649258 prefixEnd_649258 := by exact prefixLift 649258
  have htrace : WordTrace (prefixWord ++ tailWord_649258) baseStart_649258 baseEnd_649258 := by
    simpa [prefixWord, tailWord_649258, baseEnd_649258] using wordTrace_append hprefix tailTrace_649258
  have hstable : (prefixWord ++ tailWord_649258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649258).length < 2 ^ (prefixWord ++ tailWord_649258).sum := by decide
  have hdescent : baseEnd_649258 < baseStart_649258 := by decide
  rcases family_descends (prefixWord ++ tailWord_649258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649271 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_649271 : Nat := 118140960795 + 649271 * 2 ^ 59
def prefixEnd_649271 : Nat := 4983230072969 + 3 ^ 40 * 649271 * 2
def baseEnd_649271 : Nat := 333388098025434457926563

theorem tailTrace_649271 : CollatzResearch.WordTrace tailWord_649271 prefixEnd_649271 333388098025434457926563 := by
  unfold tailWord_649271
  simp only [CollatzResearch.WordTrace]
  refine ⟨23680858830809528503771667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15787239220539685669181111 23680858830809528503771667)
  ·
    refine ⟨35521288246214292755657501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23680858830809528503771667 35521288246214292755657501)
    ·
      refine ⟨13320483092330359783371563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35521288246214292755657501 13320483092330359783371563)
      ·
        refine ⟨19980724638495539675057345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13320483092330359783371563 19980724638495539675057345)
        ·
          refine ⟨14985543478871654756293009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19980724638495539675057345 14985543478871654756293009)
          ·
            refine ⟨11239157609153741067219757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14985543478871654756293009 11239157609153741067219757)
            ·
              refine ⟨4214684103432652900207409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11239157609153741067219757 4214684103432652900207409)
              ·
                refine ⟨3161013077574489675155557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4214684103432652900207409 3161013077574489675155557)
                ·
                  refine ⟨592689952045216814091667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3161013077574489675155557 592689952045216814091667)
                  ·
                    refine ⟨889034928067825221137501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 592689952045216814091667 889034928067825221137501)
                    ·
                      refine ⟨333388098025434457926563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 889034928067825221137501 333388098025434457926563)
                      ·
                        rfl

theorem cell23_649271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_649271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649271 prefixEnd_649271 := by exact prefixLift 649271
  have htrace : WordTrace (prefixWord ++ tailWord_649271) baseStart_649271 baseEnd_649271 := by
    simpa [prefixWord, tailWord_649271, baseEnd_649271] using wordTrace_append hprefix tailTrace_649271
  have hstable : (prefixWord ++ tailWord_649271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649271).length < 2 ^ (prefixWord ++ tailWord_649271).sum := by decide
  have hdescent : baseEnd_649271 < baseStart_649271 := by decide
  rcases family_descends (prefixWord ++ tailWord_649271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649278 : List Nat := [4, 2, 1, 3, 3, 1, 9]
def baseStart_649278 : Nat := 118140960795 + 649278 * 2 ^ 59
def prefixEnd_649278 : Nat := 4983230072969 + 3 ^ 40 * 649278 * 2
def baseEnd_649278 : Nat := 4115946819629826302951

theorem tailTrace_649278 : CollatzResearch.WordTrace tailWord_649278 prefixEnd_649278 4115946819629826302951 := by
  unfold tailWord_649278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960139267723021087409561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15787409427856112466184325 2960139267723021087409561)
  ·
    refine ⟨2220104450792265815557171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2960139267723021087409561 2220104450792265815557171)
    ·
      refine ⟨3330156676188398723335757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220104450792265815557171 3330156676188398723335757)
      ·
        refine ⟨1248808753570649521250909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3330156676188398723335757 1248808753570649521250909)
        ·
          refine ⟨468303282588993570469091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1248808753570649521250909 468303282588993570469091)
          ·
            refine ⟨702454923883490355703637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468303282588993570469091 702454923883490355703637)
            ·
              refine ⟨4115946819629826302951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 702454923883490355703637 4115946819629826302951)
              ·
                rfl

theorem cell23_649278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 9].length) (baseStart_649278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649278 prefixEnd_649278 := by exact prefixLift 649278
  have htrace : WordTrace (prefixWord ++ tailWord_649278) baseStart_649278 baseEnd_649278 := by
    simpa [prefixWord, tailWord_649278, baseEnd_649278] using wordTrace_append hprefix tailTrace_649278
  have hstable : (prefixWord ++ tailWord_649278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649278).length < 2 ^ (prefixWord ++ tailWord_649278).sum := by decide
  have hdescent : baseEnd_649278 < baseStart_649278 := by decide
  rcases family_descends (prefixWord ++ tailWord_649278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649328 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 1, 4, 2]
def baseStart_649328 : Nat := 118140960795 + 649328 * 2 ^ 59
def prefixEnd_649328 : Nat := 4983230072969 + 3 ^ 40 * 649328 * 2
def baseEnd_649328 : Nat := 333417366422740734913801

theorem tailTrace_649328 : CollatzResearch.WordTrace tailWord_649328 prefixEnd_649328 333417366422740734913801 := by
  unfold tailWord_649328
  simp only [CollatzResearch.WordTrace]
  refine ⟨11841468895801513619298319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15788625194402018159064425 11841468895801513619298319)
  ·
    refine ⟨17762203343702270428947479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11841468895801513619298319 17762203343702270428947479)
    ·
      refine ⟨26643305015553405643421219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17762203343702270428947479 26643305015553405643421219)
      ·
        refine ⟨39964957523330108465131829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26643305015553405643421219 39964957523330108465131829)
        ·
          refine ⟨3746714767812197668606109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39964957523330108465131829 3746714767812197668606109)
          ·
            refine ⟨1405018037929574125727291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3746714767812197668606109 1405018037929574125727291)
            ·
              refine ⟨2107527056894361188590937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405018037929574125727291 2107527056894361188590937)
              ·
                refine ⟨1580645292670770891443203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2107527056894361188590937 1580645292670770891443203)
                ·
                  refine ⟨2370967939006156337164805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580645292670770891443203 2370967939006156337164805)
                  ·
                    refine ⟨444556488563654313218401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2370967939006156337164805 444556488563654313218401)
                    ·
                      refine ⟨333417366422740734913801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444556488563654313218401 333417366422740734913801)
                      ·
                        rfl

theorem cell23_649328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 4, 2].length) (baseStart_649328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649328 prefixEnd_649328 := by exact prefixLift 649328
  have htrace : WordTrace (prefixWord ++ tailWord_649328) baseStart_649328 baseEnd_649328 := by
    simpa [prefixWord, tailWord_649328, baseEnd_649328] using wordTrace_append hprefix tailTrace_649328
  have hstable : (prefixWord ++ tailWord_649328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649328).length < 2 ^ (prefixWord ++ tailWord_649328).sum := by decide
  have hdescent : baseEnd_649328 < baseStart_649328 := by decide
  rcases family_descends (prefixWord ++ tailWord_649328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649358 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_649358 : Nat := 118140960795 + 649358 * 2 ^ 59
def prefixEnd_649358 : Nat := 4983230072969 + 3 ^ 40 * 649358 * 2
def baseEnd_649358 : Nat := 333432770842375617538663

theorem tailTrace_649358 : CollatzResearch.WordTrace tailWord_649358 prefixEnd_649358 333432770842375617538663 := by
  unfold tailWord_649358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960503997686792795273591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15789354654329561574792485 2960503997686792795273591)
  ·
    refine ⟨4440755996530189192910387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2960503997686792795273591 4440755996530189192910387)
    ·
      refine ⟨6661133994795283789365581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4440755996530189192910387 6661133994795283789365581)
      ·
        refine ⟨2497925248048231421012093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6661133994795283789365581 2497925248048231421012093)
        ·
          refine ⟨936721968018086782879535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2497925248048231421012093 936721968018086782879535)
          ·
            refine ⟨1405082952027130174319303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936721968018086782879535 1405082952027130174319303)
            ·
              refine ⟨2107624428040695261478955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405082952027130174319303 2107624428040695261478955)
              ·
                refine ⟨3161436642061042892218433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107624428040695261478955 3161436642061042892218433)
                ·
                  refine ⟨2371077481545782169163825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161436642061042892218433 2371077481545782169163825)
                  ·
                    refine ⟨1778308111159336626872869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2371077481545782169163825 1778308111159336626872869)
                    ·
                      refine ⟨333432770842375617538663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1778308111159336626872869 333432770842375617538663)
                      ·
                        rfl

theorem cell23_649358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_649358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649358 prefixEnd_649358 := by exact prefixLift 649358
  have htrace : WordTrace (prefixWord ++ tailWord_649358) baseStart_649358 baseEnd_649358 := by
    simpa [prefixWord, tailWord_649358, baseEnd_649358] using wordTrace_append hprefix tailTrace_649358
  have hstable : (prefixWord ++ tailWord_649358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649358).length < 2 ^ (prefixWord ++ tailWord_649358).sum := by decide
  have hdescent : baseEnd_649358 < baseStart_649358 := by decide
  rcases family_descends (prefixWord ++ tailWord_649358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649371 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 2, 5, 2]
def baseStart_649371 : Nat := 118140960795 + 649371 * 2 ^ 59
def prefixEnd_649371 : Nat := 4983230072969 + 3 ^ 40 * 649371 * 2
def baseEnd_649371 : Nat := 333439446090884066676103

theorem tailTrace_649371 : CollatzResearch.WordTrace tailWord_649371 prefixEnd_649371 333439446090884066676103 := by
  unfold tailWord_649371
  simp only [CollatzResearch.WordTrace]
  refine ⟨23684506130447245582411967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15789670753631497054941311 23684506130447245582411967)
  ·
    refine ⟨35526759195670868373617951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23684506130447245582411967 35526759195670868373617951)
    ·
      refine ⟨53290138793506302560426927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35526759195670868373617951 53290138793506302560426927)
      ·
        refine ⟨79935208190259453840640391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53290138793506302560426927 79935208190259453840640391)
        ·
          refine ⟨119902812285389180760960587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79935208190259453840640391 119902812285389180760960587)
          ·
            refine ⟨179854218428083771141440881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119902812285389180760960587 179854218428083771141440881)
            ·
              refine ⟨134890663821062828356080661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179854218428083771141440881 134890663821062828356080661)
              ·
                refine ⟨6322999866612320079191281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134890663821062828356080661 6322999866612320079191281)
                ·
                  refine ⟨4742249899959240059393461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6322999866612320079191281 4742249899959240059393461)
                  ·
                    refine ⟨444585928121178755568137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4742249899959240059393461 444585928121178755568137)
                    ·
                      refine ⟨333439446090884066676103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444585928121178755568137 333439446090884066676103)
                      ·
                        rfl

theorem cell23_649371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5, 2].length) (baseStart_649371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649371 prefixEnd_649371 := by exact prefixLift 649371
  have htrace : WordTrace (prefixWord ++ tailWord_649371) baseStart_649371 baseEnd_649371 := by
    simpa [prefixWord, tailWord_649371, baseEnd_649371] using wordTrace_append hprefix tailTrace_649371
  have hstable : (prefixWord ++ tailWord_649371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649371).length < 2 ^ (prefixWord ++ tailWord_649371).sum := by decide
  have hdescent : baseEnd_649371 < baseStart_649371 := by decide
  rcases family_descends (prefixWord ++ tailWord_649371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649396 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_649396 : Nat := 118140960795 + 649396 * 2 ^ 59
def prefixEnd_649396 : Nat := 4983230072969 + 3 ^ 40 * 649396 * 2
def baseEnd_649396 : Nat := 333452283107246468863489

theorem tailTrace_649396 : CollatzResearch.WordTrace tailWord_649396 prefixEnd_649396 333452283107246468863489 := by
  unfold tailWord_649396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842708977678337426036021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15790278636904449901381361 11842708977678337426036021)
  ·
    refine ⟨1110253966657344133690877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11842708977678337426036021 1110253966657344133690877)
    ·
      refine ⟨416345237496504050134079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1110253966657344133690877 416345237496504050134079)
      ·
        refine ⟨624517856244756075201119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416345237496504050134079 624517856244756075201119)
        ·
          refine ⟨936776784367134112801679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624517856244756075201119 936776784367134112801679)
          ·
            refine ⟨1405165176550701169202519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936776784367134112801679 1405165176550701169202519)
            ·
              refine ⟨2107747764826051753803779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405165176550701169202519 2107747764826051753803779)
              ·
                refine ⟨3161621647239077630705669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107747764826051753803779 3161621647239077630705669)
                ·
                  refine ⟨592804058857327055757313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3161621647239077630705669 592804058857327055757313)
                  ·
                    refine ⟨444603044142995291817985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 592804058857327055757313 444603044142995291817985)
                    ·
                      refine ⟨333452283107246468863489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444603044142995291817985 333452283107246468863489)
                      ·
                        rfl

theorem cell23_649396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_649396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649396 prefixEnd_649396 := by exact prefixLift 649396
  have htrace : WordTrace (prefixWord ++ tailWord_649396) baseStart_649396 baseEnd_649396 := by
    simpa [prefixWord, tailWord_649396, baseEnd_649396] using wordTrace_append hprefix tailTrace_649396
  have hstable : (prefixWord ++ tailWord_649396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649396).length < 2 ^ (prefixWord ++ tailWord_649396).sum := by decide
  have hdescent : baseEnd_649396 < baseStart_649396 := by decide
  rcases family_descends (prefixWord ++ tailWord_649396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649401 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_649401 : Nat := 118140960795 + 649401 * 2 ^ 59
def prefixEnd_649401 : Nat := 4983230072969 + 3 ^ 40 * 649401 * 2
def baseEnd_649401 : Nat := 333454850510518949300965

theorem tailTrace_649401 : CollatzResearch.WordTrace tailWord_649401 prefixEnd_649401 333454850510518949300965 := by
  unfold tailWord_649401
  simp only [CollatzResearch.WordTrace]
  refine ⟨23685600320338560706004057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15790400213559040470669371 23685600320338560706004057)
  ·
    refine ⟨17764200240253920529503043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23685600320338560706004057 17764200240253920529503043)
    ·
      refine ⟨26646300360380880794254565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17764200240253920529503043 26646300360380880794254565)
      ·
        refine ⟨4996181317571415148922731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26646300360380880794254565 4996181317571415148922731)
        ·
          refine ⟨7494271976357122723384097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4996181317571415148922731 7494271976357122723384097)
          ·
            refine ⟨5620703982267842042538073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7494271976357122723384097 5620703982267842042538073)
            ·
              refine ⟨4215527986700881531903555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5620703982267842042538073 4215527986700881531903555)
              ·
                refine ⟨6323291980051322297855333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4215527986700881531903555 6323291980051322297855333)
                ·
                  refine ⟨1185617246259622930847875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6323291980051322297855333 1185617246259622930847875)
                  ·
                    refine ⟨1778425869389434396271813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185617246259622930847875 1778425869389434396271813)
                    ·
                      refine ⟨333454850510518949300965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1778425869389434396271813 333454850510518949300965)
                      ·
                        rfl

theorem cell23_649401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_649401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649401 prefixEnd_649401 := by exact prefixLift 649401
  have htrace : WordTrace (prefixWord ++ tailWord_649401) baseStart_649401 baseEnd_649401 := by
    simpa [prefixWord, tailWord_649401, baseEnd_649401] using wordTrace_append hprefix tailTrace_649401
  have hstable : (prefixWord ++ tailWord_649401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649401).length < 2 ^ (prefixWord ++ tailWord_649401).sum := by decide
  have hdescent : baseEnd_649401 < baseStart_649401 := by decide
  rcases family_descends (prefixWord ++ tailWord_649401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649418 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_649418 : Nat := 118140960795 + 649418 * 2 ^ 59
def prefixEnd_649418 : Nat := 4983230072969 + 3 ^ 40 * 649418 * 2
def baseEnd_649418 : Nat := 333463579681645382788387

theorem tailTrace_649418 : CollatzResearch.WordTrace tailWord_649418 prefixEnd_649418 333463579681645382788387 := by
  unfold tailWord_649418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921555090319243152343227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15790813574184648406248605 5921555090319243152343227)
  ·
    refine ⟨8882332635478864728514841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5921555090319243152343227 8882332635478864728514841)
    ·
      refine ⟨6661749476609148546386131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8882332635478864728514841 6661749476609148546386131)
      ·
        refine ⟨9992624214913722819579197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6661749476609148546386131 9992624214913722819579197)
        ·
          refine ⟨3747234080592646057342199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9992624214913722819579197 3747234080592646057342199)
          ·
            refine ⟨5620851120888969086013299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747234080592646057342199 5620851120888969086013299)
            ·
              refine ⟨8431276681333453629019949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620851120888969086013299 8431276681333453629019949)
              ·
                refine ⟨3161728755500045110882481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8431276681333453629019949 3161728755500045110882481)
                ·
                  refine ⟨2371296566625033833161861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161728755500045110882481 2371296566625033833161861)
                  ·
                    refine ⟨444618106242193843717849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371296566625033833161861 444618106242193843717849)
                    ·
                      refine ⟨333463579681645382788387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444618106242193843717849 333463579681645382788387)
                      ·
                        rfl

theorem cell23_649418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_649418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649418 prefixEnd_649418 := by exact prefixLift 649418
  have htrace : WordTrace (prefixWord ++ tailWord_649418) baseStart_649418 baseEnd_649418 := by
    simpa [prefixWord, tailWord_649418, baseEnd_649418] using wordTrace_append hprefix tailTrace_649418
  have hstable : (prefixWord ++ tailWord_649418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649418).length < 2 ^ (prefixWord ++ tailWord_649418).sum := by decide
  have hdescent : baseEnd_649418 < baseStart_649418 := by decide
  rcases family_descends (prefixWord ++ tailWord_649418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649471 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 3, 5]
def baseStart_649471 : Nat := 118140960795 + 649471 * 2 ^ 59
def prefixEnd_649471 : Nat := 4983230072969 + 3 ^ 40 * 649471 * 2
def baseEnd_649471 : Nat := 111163598052111225141881

theorem tailTrace_649471 : CollatzResearch.WordTrace tailWord_649471 prefixEnd_649471 111163598052111225141881 := by
  unfold tailWord_649471
  simp only [CollatzResearch.WordTrace]
  refine ⟨23688153430084962661052267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15792102286723308440701511 23688153430084962661052267)
  ·
    refine ⟨35532230145127443991578401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23688153430084962661052267 35532230145127443991578401)
    ·
      refine ⟨26649172608845582993683801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35532230145127443991578401 26649172608845582993683801)
      ·
        refine ⟨19986879456634187245262851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26649172608845582993683801 19986879456634187245262851)
        ·
          refine ⟨29980319184951280867894277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19986879456634187245262851 29980319184951280867894277)
          ·
            refine ⟨5621309847178365162730177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29980319184951280867894277 5621309847178365162730177)
            ·
              refine ⟨4215982385383773872047633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5621309847178365162730177 4215982385383773872047633)
              ·
                refine ⟨3161986789037830404035725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215982385383773872047633 3161986789037830404035725)
                ·
                  refine ⟨1185745045889186401513397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3161986789037830404035725 1185745045889186401513397)
                  ·
                    refine ⟨111163598052111225141881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1185745045889186401513397 111163598052111225141881)
                    ·
                      rfl

theorem cell23_649471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_649471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649471 prefixEnd_649471 := by exact prefixLift 649471
  have htrace : WordTrace (prefixWord ++ tailWord_649471) baseStart_649471 baseEnd_649471 := by
    simpa [prefixWord, tailWord_649471, baseEnd_649471] using wordTrace_append hprefix tailTrace_649471
  have hstable : (prefixWord ++ tailWord_649471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649471).length < 2 ^ (prefixWord ++ tailWord_649471).sum := by decide
  have hdescent : baseEnd_649471 < baseStart_649471 := by decide
  rcases family_descends (prefixWord ++ tailWord_649471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649495 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 2, 3, 2]
def baseStart_649495 : Nat := 118140960795 + 649495 * 2 ^ 59
def prefixEnd_649495 : Nat := 4983230072969 + 3 ^ 40 * 649495 * 2
def baseEnd_649495 : Nat := 333503117692041581525533

theorem tailTrace_649495 : CollatzResearch.WordTrace tailWord_649495 prefixEnd_649495 333503117692041581525533 := by
  unfold tailWord_649495
  simp only [CollatzResearch.WordTrace]
  refine ⟨23689028781998014759925939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15792685854665343173283959 23689028781998014759925939)
  ·
    refine ⟨35533543172997022139888909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23689028781998014759925939 35533543172997022139888909)
    ·
      refine ⟨13325078689873883302458341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35533543172997022139888909 13325078689873883302458341)
      ·
        refine ⟨2498452254351353119210939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13325078689873883302458341 2498452254351353119210939)
        ·
          refine ⟨3747678381527029678816409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498452254351353119210939 3747678381527029678816409)
          ·
            refine ⟨2810758786145272259112307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3747678381527029678816409 2810758786145272259112307)
            ·
              refine ⟨4216138179217908388668461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810758786145272259112307 4216138179217908388668461)
              ·
                refine ⟨1581051817206715645750673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4216138179217908388668461 1581051817206715645750673)
                ·
                  refine ⟨1185788862905036734313005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1581051817206715645750673 1185788862905036734313005)
                  ·
                    refine ⟨444670823589388775367377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1185788862905036734313005 444670823589388775367377)
                    ·
                      refine ⟨333503117692041581525533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444670823589388775367377 333503117692041581525533)
                      ·
                        rfl

theorem cell23_649495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_649495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649495 prefixEnd_649495 := by exact prefixLift 649495
  have htrace : WordTrace (prefixWord ++ tailWord_649495) baseStart_649495 baseEnd_649495 := by
    simpa [prefixWord, tailWord_649495, baseEnd_649495] using wordTrace_append hprefix tailTrace_649495
  have hstable : (prefixWord ++ tailWord_649495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649495).length < 2 ^ (prefixWord ++ tailWord_649495).sum := by decide
  have hdescent : baseEnd_649495 < baseStart_649495 := by decide
  rcases family_descends (prefixWord ++ tailWord_649495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649528 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_649528 : Nat := 118140960795 + 649528 * 2 ^ 59
def prefixEnd_649528 : Nat := 4983230072969 + 3 ^ 40 * 649528 * 2
def baseEnd_649528 : Nat := 333520062553639952412881

theorem tailTrace_649528 : CollatzResearch.WordTrace tailWord_649528 prefixEnd_649528 333520062553639952412881 := by
  unfold tailWord_649528
  simp only [CollatzResearch.WordTrace]
  refine ⟨11845116195439230697938619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15793488260585640930584825 11845116195439230697938619)
  ·
    refine ⟨17767674293158846046907929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11845116195439230697938619 17767674293158846046907929)
    ·
      refine ⟨13325755719869134535180947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17767674293158846046907929 13325755719869134535180947)
      ·
        refine ⟨19988633579803701802771421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325755719869134535180947 19988633579803701802771421)
        ·
          refine ⟨7495737592426388176039283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19988633579803701802771421 7495737592426388176039283)
          ·
            refine ⟨11243606388639582264058925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7495737592426388176039283 11243606388639582264058925)
            ·
              refine ⟨4216352395739843349022097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11243606388639582264058925 4216352395739843349022097)
              ·
                refine ⟨3162264296804882511766573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216352395739843349022097 3162264296804882511766573)
                ·
                  refine ⟨1185849111301830941912465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3162264296804882511766573 1185849111301830941912465)
                  ·
                    refine ⟨889386833476373206434349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185849111301830941912465 889386833476373206434349)
                    ·
                      refine ⟨333520062553639952412881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 889386833476373206434349 333520062553639952412881)
                      ·
                        rfl

theorem cell23_649528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_649528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649528 prefixEnd_649528 := by exact prefixLift 649528
  have htrace : WordTrace (prefixWord ++ tailWord_649528) baseStart_649528 baseEnd_649528 := by
    simpa [prefixWord, tailWord_649528, baseEnd_649528] using wordTrace_append hprefix tailTrace_649528
  have hstable : (prefixWord ++ tailWord_649528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649528).length < 2 ^ (prefixWord ++ tailWord_649528).sum := by decide
  have hdescent : baseEnd_649528 < baseStart_649528 := by decide
  rcases family_descends (prefixWord ++ tailWord_649528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649548 : List Nat := [2, 2, 1, 3, 2, 1, 5, 7]
def baseStart_649548 : Nat := 118140960795 + 649548 * 2 ^ 59
def prefixEnd_649548 : Nat := 4983230072969 + 3 ^ 40 * 649548 * 2
def baseEnd_649548 : Nat := 12352975265434439783807

theorem tailTrace_649548 : CollatzResearch.WordTrace tailWord_649548 prefixEnd_649548 12352975265434439783807 := by
  unfold tailWord_649548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11845480925403002405802649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15793974567204003207736865 11845480925403002405802649)
  ·
    refine ⟨8884110694052251804351987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11845480925403002405802649 8884110694052251804351987)
    ·
      refine ⟨13326166041078377706527981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8884110694052251804351987 13326166041078377706527981)
      ·
        refine ⟨4997312265404391639947993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13326166041078377706527981 4997312265404391639947993)
        ·
          refine ⟨3747984199053293729960995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4997312265404391639947993 3747984199053293729960995)
          ·
            refine ⟨5621976298579940594941493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747984199053293729960995 5621976298579940594941493)
            ·
              refine ⟨527060277991869430775765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5621976298579940594941493 527060277991869430775765)
              ·
                refine ⟨12352975265434439783807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 527060277991869430775765 12352975265434439783807)
                ·
                  rfl

theorem cell23_649548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 7].length) (baseStart_649548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649548 prefixEnd_649548 := by exact prefixLift 649548
  have htrace : WordTrace (prefixWord ++ tailWord_649548) baseStart_649548 baseEnd_649548 := by
    simpa [prefixWord, tailWord_649548, baseEnd_649548] using wordTrace_append hprefix tailTrace_649548
  have hstable : (prefixWord ++ tailWord_649548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649548).length < 2 ^ (prefixWord ++ tailWord_649548).sum := by decide
  have hdescent : baseEnd_649548 < baseStart_649548 := by decide
  rcases family_descends (prefixWord ++ tailWord_649548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649559 : List Nat := [1, 1, 3, 2, 3, 1, 4, 3, 1, 2, 2]
def baseStart_649559 : Nat := 118140960795 + 649559 * 2 ^ 59
def prefixEnd_649559 : Nat := 4983230072969 + 3 ^ 40 * 649559 * 2
def baseEnd_649559 : Nat := 333535980453929331125239

theorem tailTrace_649559 : CollatzResearch.WordTrace tailWord_649559 prefixEnd_649559 333535980453929331125239 := by
  unfold tailWord_649559
  simp only [CollatzResearch.WordTrace]
  refine ⟨23691363053766153690255731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15794242035844102460170487 23691363053766153690255731)
  ·
    refine ⟨35537044580649230535383597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23691363053766153690255731 35537044580649230535383597)
    ·
      refine ⟨13326391717743461450768849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35537044580649230535383597 13326391717743461450768849)
      ·
        refine ⟨9994793788307596088076637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13326391717743461450768849 9994793788307596088076637)
        ·
          refine ⟨3748047670615348533028739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9994793788307596088076637 3748047670615348533028739)
          ·
            refine ⟨5622071505923022799543109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748047670615348533028739 5622071505923022799543109)
            ·
              refine ⟨1054138407360566774914333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5622071505923022799543109 1054138407360566774914333)
              ·
                refine ⟨395301902760212540592875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054138407360566774914333 395301902760212540592875)
                ·
                  refine ⟨592952854140318810889313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395301902760212540592875 592952854140318810889313)
                  ·
                    refine ⟨444714640605239108166985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 592952854140318810889313 444714640605239108166985)
                    ·
                      refine ⟨333535980453929331125239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444714640605239108166985 333535980453929331125239)
                      ·
                        rfl

theorem cell23_649559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_649559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649559 prefixEnd_649559 := by exact prefixLift 649559
  have htrace : WordTrace (prefixWord ++ tailWord_649559) baseStart_649559 baseEnd_649559 := by
    simpa [prefixWord, tailWord_649559, baseEnd_649559] using wordTrace_append hprefix tailTrace_649559
  have hstable : (prefixWord ++ tailWord_649559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649559).length < 2 ^ (prefixWord ++ tailWord_649559).sum := by decide
  have hdescent : baseEnd_649559 < baseStart_649559 := by decide
  rcases family_descends (prefixWord ++ tailWord_649559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649591 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 1, 8]
def baseStart_649591 : Nat := 118140960795 + 649591 * 2 ^ 59
def prefixEnd_649591 : Nat := 4983230072969 + 3 ^ 40 * 649591 * 2
def baseEnd_649591 : Nat := 111184137278291068641697

theorem tailTrace_649591 : CollatzResearch.WordTrace tailWord_649591 prefixEnd_649591 111184137278291068641697 := by
  unfold tailWord_649591
  simp only [CollatzResearch.WordTrace]
  refine ⟨23692530189650223155420627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15795020126433482103613751 23692530189650223155420627)
  ·
    refine ⟨35538795284475334733130941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23692530189650223155420627 35538795284475334733130941)
    ·
      refine ⟨13327048231678250524924103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35538795284475334733130941 13327048231678250524924103)
      ·
        refine ⟨19990572347517375787386155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13327048231678250524924103 19990572347517375787386155)
        ·
          refine ⟨29985858521276063681079233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19990572347517375787386155 29985858521276063681079233)
          ·
            refine ⟨22489393890957047760809425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29985858521276063681079233 22489393890957047760809425)
            ·
              refine ⟨16867045418217785820607069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22489393890957047760809425 16867045418217785820607069)
              ·
                refine ⟨6325142031831669682727651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16867045418217785820607069 6325142031831669682727651)
                ·
                  refine ⟨9487713047747504524091477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325142031831669682727651 9487713047747504524091477)
                  ·
                    refine ⟨111184137278291068641697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9487713047747504524091477 111184137278291068641697)
                    ·
                      rfl

theorem cell23_649591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_649591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649591 prefixEnd_649591 := by exact prefixLift 649591
  have htrace : WordTrace (prefixWord ++ tailWord_649591) baseStart_649591 baseEnd_649591 := by
    simpa [prefixWord, tailWord_649591, baseEnd_649591] using wordTrace_append hprefix tailTrace_649591
  have hstable : (prefixWord ++ tailWord_649591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649591).length < 2 ^ (prefixWord ++ tailWord_649591).sum := by decide
  have hdescent : baseEnd_649591 < baseStart_649591 := by decide
  rcases family_descends (prefixWord ++ tailWord_649591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649610 : List Nat := [3, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_649610 : Nat := 118140960795 + 649610 * 2 ^ 59
def prefixEnd_649610 : Nat := 4983230072969 + 3 ^ 40 * 649610 * 2
def baseEnd_649610 : Nat := 333562167967308631587505

theorem tailTrace_649610 : CollatzResearch.WordTrace tailWord_649610 prefixEnd_649610 333562167967308631587505 := by
  unfold tailWord_649610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923305794145347350090571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15795482117720926266908189 5923305794145347350090571)
  ·
    refine ⟨8884958691218021025135857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923305794145347350090571 8884958691218021025135857)
    ·
      refine ⟨6663719018413515768851893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8884958691218021025135857 6663719018413515768851893)
      ·
        refine ⟨624723657976267103329865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6663719018413515768851893 624723657976267103329865)
        ·
          refine ⟨468542743482200327497399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624723657976267103329865 468542743482200327497399)
          ·
            refine ⟨702814115223300491246099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468542743482200327497399 702814115223300491246099)
            ·
              refine ⟨1054221172834950736869149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702814115223300491246099 1054221172834950736869149)
              ·
                refine ⟨395332939813106526325931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054221172834950736869149 395332939813106526325931)
                ·
                  refine ⟨592999409719659789488897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395332939813106526325931 592999409719659789488897)
                  ·
                    refine ⟨444749557289744842116673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 592999409719659789488897 444749557289744842116673)
                    ·
                      refine ⟨333562167967308631587505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444749557289744842116673 333562167967308631587505)
                      ·
                        rfl

theorem cell23_649610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_649610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649610 prefixEnd_649610 := by exact prefixLift 649610
  have htrace : WordTrace (prefixWord ++ tailWord_649610) baseStart_649610 baseEnd_649610 := by
    simpa [prefixWord, tailWord_649610, baseEnd_649610] using wordTrace_append hprefix tailTrace_649610
  have hstable : (prefixWord ++ tailWord_649610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649610).length < 2 ^ (prefixWord ++ tailWord_649610).sum := by decide
  have hdescent : baseEnd_649610 < baseStart_649610 := by decide
  rcases family_descends (prefixWord ++ tailWord_649610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649632 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 4, 2, 2]
def baseStart_649632 : Nat := 118140960795 + 649632 * 2 ^ 59
def prefixEnd_649632 : Nat := 4983230072969 + 3 ^ 40 * 649632 * 2
def baseEnd_649632 : Nat := 333573464541707545512403

theorem tailTrace_649632 : CollatzResearch.WordTrace tailWord_649632 prefixEnd_649632 333573464541707545512403 := by
  unfold tailWord_649632
  simp only [CollatzResearch.WordTrace]
  refine ⟨11847012791250843578831575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15796017055001124771775433 11847012791250843578831575)
  ·
    refine ⟨17770519186876265368247363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11847012791250843578831575 17770519186876265368247363)
    ·
      refine ⟨26655778780314398052371045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17770519186876265368247363 26655778780314398052371045)
      ·
        refine ⟨4997958521308949634819571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26655778780314398052371045 4997958521308949634819571)
        ·
          refine ⟨7496937781963424452229357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997958521308949634819571 7496937781963424452229357)
          ·
            refine ⟨2811351668236284169586009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7496937781963424452229357 2811351668236284169586009)
            ·
              refine ⟨2108513751177213127189507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811351668236284169586009 2108513751177213127189507)
              ·
                refine ⟨3162770626765819690784261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108513751177213127189507 3162770626765819690784261)
                ·
                  refine ⟨593019492518591192022049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3162770626765819690784261 593019492518591192022049)
                  ·
                    refine ⟨444764619388943394016537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 593019492518591192022049 444764619388943394016537)
                    ·
                      refine ⟨333573464541707545512403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444764619388943394016537 333573464541707545512403)
                      ·
                        rfl

theorem cell23_649632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_649632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649632 prefixEnd_649632 := by exact prefixLift 649632
  have htrace : WordTrace (prefixWord ++ tailWord_649632) baseStart_649632 baseEnd_649632 := by
    simpa [prefixWord, tailWord_649632, baseEnd_649632] using wordTrace_append hprefix tailTrace_649632
  have hstable : (prefixWord ++ tailWord_649632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649632).length < 2 ^ (prefixWord ++ tailWord_649632).sum := by decide
  have hdescent : baseEnd_649632 < baseStart_649632 := by decide
  rcases family_descends (prefixWord ++ tailWord_649632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649648 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3]
def baseStart_649648 : Nat := 118140960795 + 649648 * 2 ^ 59
def prefixEnd_649648 : Nat := 4983230072969 + 3 ^ 40 * 649648 * 2
def baseEnd_649648 : Nat := 333581680232179482912329

theorem tailTrace_649648 : CollatzResearch.WordTrace tailWord_649648 prefixEnd_649648 333581680232179482912329 := by
  unfold tailWord_649648
  simp only [CollatzResearch.WordTrace]
  refine ⟨11847304575221860945122799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15796406100295814593497065 11847304575221860945122799)
  ·
    refine ⟨17770956862832791417684199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11847304575221860945122799 17770956862832791417684199)
    ·
      refine ⟨26656435294249187126526299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17770956862832791417684199 26656435294249187126526299)
      ·
        refine ⟨39984652941373780689789449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26656435294249187126526299 39984652941373780689789449)
        ·
          refine ⟨29988489706030335517342087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39984652941373780689789449 29988489706030335517342087)
          ·
            refine ⟨44982734559045503276013131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29988489706030335517342087 44982734559045503276013131)
            ·
              refine ⟨67474101838568254914019697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44982734559045503276013131 67474101838568254914019697)
              ·
                refine ⟨50605576378926191185514773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67474101838568254914019697 50605576378926191185514773)
                ·
                  refine ⟨2372136392762165211821005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50605576378926191185514773 2372136392762165211821005)
                  ·
                    refine ⟨889551147285811954432877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372136392762165211821005 889551147285811954432877)
                    ·
                      refine ⟨333581680232179482912329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 889551147285811954432877 333581680232179482912329)
                      ·
                        rfl

theorem cell23_649648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_649648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649648 prefixEnd_649648 := by exact prefixLift 649648
  have htrace : WordTrace (prefixWord ++ tailWord_649648) baseStart_649648 baseEnd_649648 := by
    simpa [prefixWord, tailWord_649648, baseEnd_649648] using wordTrace_append hprefix tailTrace_649648
  have hstable : (prefixWord ++ tailWord_649648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649648).length < 2 ^ (prefixWord ++ tailWord_649648).sum := by decide
  have hdescent : baseEnd_649648 < baseStart_649648 := by decide
  rcases family_descends (prefixWord ++ tailWord_649648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649649 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 2, 2, 2]
def baseStart_649649 : Nat := 118140960795 + 649649 * 2 ^ 59
def prefixEnd_649649 : Nat := 4983230072969 + 3 ^ 40 * 649649 * 2
def baseEnd_649649 : Nat := 333582193712833978999825

theorem tailTrace_649649 : CollatzResearch.WordTrace tailWord_649649 prefixEnd_649649 333582193712833978999825 := by
  unfold tailWord_649649
  simp only [CollatzResearch.WordTrace]
  refine ⟨23694645623440099061032001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15796430415626732707354667 23694645623440099061032001)
  ·
    refine ⟨17770984217580074295774001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23694645623440099061032001 17770984217580074295774001)
    ·
      refine ⟨13328238163185055721830501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17770984217580074295774001 13328238163185055721830501)
      ·
        refine ⟨2499044655597197947843219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13328238163185055721830501 2499044655597197947843219)
        ·
          refine ⟨3748566983395796921764829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499044655597197947843219 3748566983395796921764829)
          ·
            refine ⟨1405712618773423845661811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3748566983395796921764829 1405712618773423845661811)
            ·
              refine ⟨2108568928160135768492717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405712618773423845661811 2108568928160135768492717)
              ·
                refine ⟨790713348060050913184769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108568928160135768492717 790713348060050913184769)
                ·
                  refine ⟨593035011045038184888577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 790713348060050913184769 593035011045038184888577)
                  ·
                    refine ⟨444776258283778638666433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 593035011045038184888577 444776258283778638666433)
                    ·
                      refine ⟨333582193712833978999825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444776258283778638666433 333582193712833978999825)
                      ·
                        rfl

theorem cell23_649649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_649649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649649 prefixEnd_649649 := by exact prefixLift 649649
  have htrace : WordTrace (prefixWord ++ tailWord_649649) baseStart_649649 baseEnd_649649 := by
    simpa [prefixWord, tailWord_649649, baseEnd_649649] using wordTrace_append hprefix tailTrace_649649
  have hstable : (prefixWord ++ tailWord_649649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649649).length < 2 ^ (prefixWord ++ tailWord_649649).sum := by decide
  have hdescent : baseEnd_649649 < baseStart_649649 := by decide
  rcases family_descends (prefixWord ++ tailWord_649649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649685 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_649685 : Nat := 118140960795 + 649685 * 2 ^ 59
def prefixEnd_649685 : Nat := 4983230072969 + 3 ^ 40 * 649685 * 2
def baseEnd_649685 : Nat := 111200226338798612716553

theorem tailTrace_649685 : CollatzResearch.WordTrace tailWord_649685 prefixEnd_649685 111200226338798612716553 := by
  unfold tailWord_649685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23695958651309677209342509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15797305767539784806228339 23695958651309677209342509)
  ·
    refine ⟨8885984494241128953503441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23695958651309677209342509 8885984494241128953503441)
    ·
      refine ⟨6664488370680846715127581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8885984494241128953503441 6664488370680846715127581)
      ·
        refine ⟨2499183139005317518172843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6664488370680846715127581 2499183139005317518172843)
        ·
          refine ⟨3748774708507976277259265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499183139005317518172843 3748774708507976277259265)
          ·
            refine ⟨2811581031380982207944449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3748774708507976277259265 2811581031380982207944449)
            ·
              refine ⟨2108685773535736655958337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811581031380982207944449 2108685773535736655958337)
              ·
                refine ⟨1581514330151802491968753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108685773535736655958337 1581514330151802491968753)
                ·
                  refine ⟨1186135747613851868976565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1581514330151802491968753 1186135747613851868976565)
                  ·
                    refine ⟨111200226338798612716553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1186135747613851868976565 111200226338798612716553)
                    ·
                      rfl

theorem cell23_649685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_649685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649685 prefixEnd_649685 := by exact prefixLift 649685
  have htrace : WordTrace (prefixWord ++ tailWord_649685) baseStart_649685 baseEnd_649685 := by
    simpa [prefixWord, tailWord_649685, baseEnd_649685] using wordTrace_append hprefix tailTrace_649685
  have hstable : (prefixWord ++ tailWord_649685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649685).length < 2 ^ (prefixWord ++ tailWord_649685).sum := by decide
  have hdescent : baseEnd_649685 < baseStart_649685 := by decide
  rcases family_descends (prefixWord ++ tailWord_649685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649688 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_649688 : Nat := 118140960795 + 649688 * 2 ^ 59
def prefixEnd_649688 : Nat := 4983230072969 + 3 ^ 40 * 649688 * 2
def baseEnd_649688 : Nat := 333602219458359326412145

theorem tailTrace_649688 : CollatzResearch.WordTrace tailWord_649688 prefixEnd_649688 333602219458359326412145 := by
  unfold tailWord_649688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11848034035149404360850859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15797378713532539147801145 11848034035149404360850859)
  ·
    refine ⟨17772051052724106541276289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11848034035149404360850859 17772051052724106541276289)
    ·
      refine ⟨13329038289543079905957217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17772051052724106541276289 13329038289543079905957217)
      ·
        refine ⟨9996778717157309929467913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13329038289543079905957217 9996778717157309929467913)
        ·
          refine ⟨7497584037867982447100935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996778717157309929467913 7497584037867982447100935)
          ·
            refine ⟨11246376056801973670651403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497584037867982447100935 11246376056801973670651403)
            ·
              refine ⟨16869564085202960505977105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11246376056801973670651403 16869564085202960505977105)
              ·
                refine ⟨12652173063902220379482829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16869564085202960505977105 12652173063902220379482829)
                ·
                  refine ⟨4744564898963332642306061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12652173063902220379482829 4744564898963332642306061)
                  ·
                    refine ⟨1779211837111249740864773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4744564898963332642306061 1779211837111249740864773)
                    ·
                      refine ⟨333602219458359326412145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1779211837111249740864773 333602219458359326412145)
                      ·
                        rfl

theorem cell23_649688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_649688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649688 prefixEnd_649688 := by exact prefixLift 649688
  have htrace : WordTrace (prefixWord ++ tailWord_649688) baseStart_649688 baseEnd_649688 := by
    simpa [prefixWord, tailWord_649688, baseEnd_649688] using wordTrace_append hprefix tailTrace_649688
  have hstable : (prefixWord ++ tailWord_649688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649688).length < 2 ^ (prefixWord ++ tailWord_649688).sum := by decide
  have hdescent : baseEnd_649688 < baseStart_649688 := by decide
  rcases family_descends (prefixWord ++ tailWord_649688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649715 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 3, 4]
def baseStart_649715 : Nat := 118140960795 + 649715 * 2 ^ 59
def prefixEnd_649715 : Nat := 4983230072969 + 3 ^ 40 * 649715 * 2
def baseEnd_649715 : Nat := 111205361145343573591507

theorem tailTrace_649715 : CollatzResearch.WordTrace tailWord_649715 prefixEnd_649715 111205361145343573591507 := by
  unfold tailWord_649715
  simp only [CollatzResearch.WordTrace]
  refine ⟨23697052841200992332934599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15798035227467328221956399 23697052841200992332934599)
  ·
    refine ⟨35545579261801488499401899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23697052841200992332934599 35545579261801488499401899)
    ·
      refine ⟨53318368892702232749102849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35545579261801488499401899 53318368892702232749102849)
      ·
        refine ⟨39988776669526674561827137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53318368892702232749102849 39988776669526674561827137)
        ·
          refine ⟨29991582502145005921370353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39988776669526674561827137 29991582502145005921370353)
          ·
            refine ⟨22493686876608754441027765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29991582502145005921370353 22493686876608754441027765)
            ·
              refine ⟨2108783144682070728846353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22493686876608754441027765 2108783144682070728846353)
              ·
                refine ⟨1581587358511553046634765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108783144682070728846353 1581587358511553046634765)
                ·
                  refine ⟨593095259441832392488037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1581587358511553046634765 593095259441832392488037)
                  ·
                    refine ⟨111205361145343573591507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 593095259441832392488037 111205361145343573591507)
                    ·
                      rfl

theorem cell23_649715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 4].length) (baseStart_649715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649715 prefixEnd_649715 := by exact prefixLift 649715
  have htrace : WordTrace (prefixWord ++ tailWord_649715) baseStart_649715 baseEnd_649715 := by
    simpa [prefixWord, tailWord_649715, baseEnd_649715] using wordTrace_append hprefix tailTrace_649715
  have hstable : (prefixWord ++ tailWord_649715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649715).length < 2 ^ (prefixWord ++ tailWord_649715).sum := by decide
  have hdescent : baseEnd_649715 < baseStart_649715 := by decide
  rcases family_descends (prefixWord ++ tailWord_649715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649725 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_649725 : Nat := 118140960795 + 649725 * 2 ^ 59
def prefixEnd_649725 : Nat := 4983230072969 + 3 ^ 40 * 649725 * 2
def baseEnd_649725 : Nat := 333621218242575681649475

theorem tailTrace_649725 : CollatzResearch.WordTrace tailWord_649725 prefixEnd_649725 333621218242575681649475 := by
  unfold tailWord_649725
  simp only [CollatzResearch.WordTrace]
  refine ⟨23697417571164764040798629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15798278380776509360532419 23697417571164764040798629)
  ·
    refine ⟨4443265794593393257649743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23697417571164764040798629 4443265794593393257649743)
    ·
      refine ⟨6664898691890089886474615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4443265794593393257649743 6664898691890089886474615)
      ·
        refine ⟨9997348037835134829711923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6664898691890089886474615 9997348037835134829711923)
        ·
          refine ⟨14996022056752702244567885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9997348037835134829711923 14996022056752702244567885)
          ·
            refine ⟨5623508271282263341712957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14996022056752702244567885 5623508271282263341712957)
            ·
              refine ⟨2108815601730848753142359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5623508271282263341712957 2108815601730848753142359)
              ·
                refine ⟨3163223402596273129713539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108815601730848753142359 3163223402596273129713539)
                ·
                  refine ⟨4744835103894409694570309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163223402596273129713539 4744835103894409694570309)
                  ·
                    refine ⟨889656581980201817731933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4744835103894409694570309 889656581980201817731933)
                    ·
                      refine ⟨333621218242575681649475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 889656581980201817731933 333621218242575681649475)
                      ·
                        rfl

theorem cell23_649725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_649725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649725 prefixEnd_649725 := by exact prefixLift 649725
  have htrace : WordTrace (prefixWord ++ tailWord_649725) baseStart_649725 baseEnd_649725 := by
    simpa [prefixWord, tailWord_649725, baseEnd_649725] using wordTrace_append hprefix tailTrace_649725
  have hstable : (prefixWord ++ tailWord_649725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649725).length < 2 ^ (prefixWord ++ tailWord_649725).sum := by decide
  have hdescent : baseEnd_649725 < baseStart_649725 := by decide
  rcases family_descends (prefixWord ++ tailWord_649725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649799 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_649799 : Nat := 118140960795 + 649799 * 2 ^ 59
def prefixEnd_649799 : Nat := 4983230072969 + 3 ^ 40 * 649799 * 2
def baseEnd_649799 : Nat := 333659215811008392124135

theorem tailTrace_649799 : CollatzResearch.WordTrace tailWord_649799 prefixEnd_649799 333659215811008392124135 := by
  unfold tailWord_649799
  simp only [CollatzResearch.WordTrace]
  refine ⟨23700116572896674678992451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15800077715264449785994967 23700116572896674678992451)
  ·
    refine ⟨35550174859345012018488677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23700116572896674678992451 35550174859345012018488677)
    ·
      refine ⟨6665657786127189753466627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35550174859345012018488677 6665657786127189753466627)
      ·
        refine ⟨9998486679190784630199941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665657786127189753466627 9998486679190784630199941)
        ·
          refine ⟨1874716252348272118162489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9998486679190784630199941 1874716252348272118162489)
          ·
            refine ⟨1406037189261204088621867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874716252348272118162489 1406037189261204088621867)
            ·
              refine ⟨2109055783891806132932801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406037189261204088621867 2109055783891806132932801)
              ·
                refine ⟨1581791837918854599699601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109055783891806132932801 1581791837918854599699601)
                ·
                  refine ⟨1186343878439140949774701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1581791837918854599699601 1186343878439140949774701)
                  ·
                    refine ⟨444878954414677856165513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186343878439140949774701 444878954414677856165513)
                    ·
                      refine ⟨333659215811008392124135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 444878954414677856165513 333659215811008392124135)
                      ·
                        rfl

theorem cell23_649799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_649799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649799 prefixEnd_649799 := by exact prefixLift 649799
  have htrace : WordTrace (prefixWord ++ tailWord_649799) baseStart_649799 baseEnd_649799 := by
    simpa [prefixWord, tailWord_649799, baseEnd_649799] using wordTrace_append hprefix tailTrace_649799
  have hstable : (prefixWord ++ tailWord_649799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649799).length < 2 ^ (prefixWord ++ tailWord_649799).sum := by decide
  have hdescent : baseEnd_649799 < baseStart_649799 := by decide
  rcases family_descends (prefixWord ++ tailWord_649799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649815 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_649815 : Nat := 118140960795 + 649815 * 2 ^ 59
def prefixEnd_649815 : Nat := 4983230072969 + 3 ^ 40 * 649815 * 2
def baseEnd_649815 : Nat := 333667431501480329524061

theorem tailTrace_649815 : CollatzResearch.WordTrace tailWord_649815 prefixEnd_649815 333667431501480329524061 := by
  unfold tailWord_649815
  simp only [CollatzResearch.WordTrace]
  refine ⟨23700700140838709411574899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15800466760559139607716599 23700700140838709411574899)
  ·
    refine ⟨35551050211258064117362349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23700700140838709411574899 35551050211258064117362349)
    ·
      refine ⟨13331643829221774044010881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35551050211258064117362349 13331643829221774044010881)
      ·
        refine ⟨9998732871916330533008161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13331643829221774044010881 9998732871916330533008161)
        ·
          refine ⟨7499049653937247899756121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9998732871916330533008161 7499049653937247899756121)
          ·
            refine ⟨5624287240452935924817091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7499049653937247899756121 5624287240452935924817091)
            ·
              refine ⟨8436430860679403887225637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624287240452935924817091 8436430860679403887225637)
              ·
                refine ⟨1581830786377388228854807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8436430860679403887225637 1581830786377388228854807)
                ·
                  refine ⟨2372746179566082343282211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581830786377388228854807 2372746179566082343282211)
                  ·
                    refine ⟨3559119269349123514923317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2372746179566082343282211 3559119269349123514923317)
                    ·
                      refine ⟨333667431501480329524061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3559119269349123514923317 333667431501480329524061)
                      ·
                        rfl

theorem cell23_649815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_649815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649815 prefixEnd_649815 := by exact prefixLift 649815
  have htrace : WordTrace (prefixWord ++ tailWord_649815) baseStart_649815 baseEnd_649815 := by
    simpa [prefixWord, tailWord_649815, baseEnd_649815] using wordTrace_append hprefix tailTrace_649815
  have hstable : (prefixWord ++ tailWord_649815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649815).length < 2 ^ (prefixWord ++ tailWord_649815).sum := by decide
  have hdescent : baseEnd_649815 < baseStart_649815 := by decide
  rcases family_descends (prefixWord ++ tailWord_649815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649825 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_649825 : Nat := 118140960795 + 649825 * 2 ^ 59
def prefixEnd_649825 : Nat := 4983230072969 + 3 ^ 40 * 649825 * 2
def baseEnd_649825 : Nat := 333672566308025290399015

theorem tailTrace_649825 : CollatzResearch.WordTrace tailWord_649825 prefixEnd_649825 333672566308025290399015 := by
  unfold tailWord_649825
  simp only [CollatzResearch.WordTrace]
  refine ⟨23701064870802481119438929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15800709913868320746292619 23701064870802481119438929)
  ·
    refine ⟨17775798653101860839579197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23701064870802481119438929 17775798653101860839579197)
    ·
      refine ⟨6665924494913197814842199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17775798653101860839579197 6665924494913197814842199)
      ·
        refine ⟨9998886742369796722263299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665924494913197814842199 9998886742369796722263299)
        ·
          refine ⟨14998330113554695083394949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9998886742369796722263299 14998330113554695083394949)
          ·
            refine ⟨2812186896291505328136553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14998330113554695083394949 2812186896291505328136553)
            ·
              refine ⟨2109140172218628996102415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812186896291505328136553 2109140172218628996102415)
              ·
                refine ⟨3163710258327943494153623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109140172218628996102415 3163710258327943494153623)
                ·
                  refine ⟨4745565387491915241230435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163710258327943494153623 4745565387491915241230435)
                  ·
                    refine ⟨7118348081237872861845653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4745565387491915241230435 7118348081237872861845653)
                    ·
                      refine ⟨333672566308025290399015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7118348081237872861845653 333672566308025290399015)
                      ·
                        rfl

theorem cell23_649825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_649825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649825 prefixEnd_649825 := by exact prefixLift 649825
  have htrace : WordTrace (prefixWord ++ tailWord_649825) baseStart_649825 baseEnd_649825 := by
    simpa [prefixWord, tailWord_649825, baseEnd_649825] using wordTrace_append hprefix tailTrace_649825
  have hstable : (prefixWord ++ tailWord_649825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649825).length < 2 ^ (prefixWord ++ tailWord_649825).sum := by decide
  have hdescent : baseEnd_649825 < baseStart_649825 := by decide
  rcases family_descends (prefixWord ++ tailWord_649825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649879 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_649879 : Nat := 118140960795 + 649879 * 2 ^ 59
def prefixEnd_649879 : Nat := 4983230072969 + 3 ^ 40 * 649879 * 2
def baseEnd_649879 : Nat := 333700294263368079123767

theorem tailTrace_649879 : CollatzResearch.WordTrace tailWord_649879 prefixEnd_649879 333700294263368079123767 := by
  unfold tailWord_649879
  simp only [CollatzResearch.WordTrace]
  refine ⟨23703034412606848341904691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15802022941737898894603127 23703034412606848341904691)
  ·
    refine ⟨35554551618910272512857037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23703034412606848341904691 35554551618910272512857037)
    ·
      refine ⟨13332956857091352192321389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35554551618910272512857037 13332956857091352192321389)
      ·
        refine ⟨4999858821409257072120521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13332956857091352192321389 4999858821409257072120521)
        ·
          refine ⟨3749894116056942804090391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4999858821409257072120521 3749894116056942804090391)
          ·
            refine ⟨5624841174085414206135587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749894116056942804090391 5624841174085414206135587)
            ·
              refine ⟨8437261761128121309203381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624841174085414206135587 8437261761128121309203381)
              ·
                refine ⟨790993290105761372737817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8437261761128121309203381 790993290105761372737817)
                ·
                  refine ⟨593244967579321029553363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 790993290105761372737817 593244967579321029553363)
                  ·
                    refine ⟨889867451368981544330045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 593244967579321029553363 889867451368981544330045)
                    ·
                      refine ⟨333700294263368079123767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 889867451368981544330045 333700294263368079123767)
                      ·
                        rfl

theorem cell23_649879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_649879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_649879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_649879 prefixEnd_649879 := by exact prefixLift 649879
  have htrace : WordTrace (prefixWord ++ tailWord_649879) baseStart_649879 baseEnd_649879 := by
    simpa [prefixWord, tailWord_649879, baseEnd_649879] using wordTrace_append hprefix tailTrace_649879
  have hstable : (prefixWord ++ tailWord_649879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649879).length < 2 ^ (prefixWord ++ tailWord_649879).sum := by decide
  have hdescent : baseEnd_649879 < baseStart_649879 := by decide
  rcases family_descends (prefixWord ++ tailWord_649879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650079 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 1, 5]
def baseStart_650079 : Nat := 118140960795 + 650079 * 2 ^ 59
def prefixEnd_650079 : Nat := 4983230072969 + 3 ^ 40 * 650079 * 2
def baseEnd_650079 : Nat := 111267663464755765540949

theorem tailTrace_650079 : CollatzResearch.WordTrace tailWord_650079 prefixEnd_650079 111267663464755765540949 := by
  unfold tailWord_650079
  simp only [CollatzResearch.WordTrace]
  refine ⟨23710329011882282499185291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15806886007921521666123527 23710329011882282499185291)
  ·
    refine ⟨35565493517823423748777937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23710329011882282499185291 35565493517823423748777937)
    ·
      refine ⟨26674120138367567811583453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35565493517823423748777937 26674120138367567811583453)
      ·
        refine ⟨10002795051887837929343795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26674120138367567811583453 10002795051887837929343795)
        ·
          refine ⟨15004192577831756894015693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10002795051887837929343795 15004192577831756894015693)
          ·
            refine ⟨5626572216686908835255885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15004192577831756894015693 5626572216686908835255885)
            ·
              refine ⟨2109964581257590813220957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5626572216686908835255885 2109964581257590813220957)
              ·
                refine ⟨791236717971596554957859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2109964581257590813220957 791236717971596554957859)
                ·
                  refine ⟨1186855076957394832436789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791236717971596554957859 1186855076957394832436789)
                  ·
                    refine ⟨111267663464755765540949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1186855076957394832436789 111267663464755765540949)
                    ·
                      rfl

theorem cell23_650079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_650079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650079 prefixEnd_650079 := by exact prefixLift 650079
  have htrace : WordTrace (prefixWord ++ tailWord_650079) baseStart_650079 baseEnd_650079 := by
    simpa [prefixWord, tailWord_650079, baseEnd_650079] using wordTrace_append hprefix tailTrace_650079
  have hstable : (prefixWord ++ tailWord_650079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650079).length < 2 ^ (prefixWord ++ tailWord_650079).sum := by decide
  have hdescent : baseEnd_650079 < baseStart_650079 := by decide
  rcases family_descends (prefixWord ++ tailWord_650079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650109 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_650109 : Nat := 118140960795 + 650109 * 2 ^ 59
def prefixEnd_650109 : Nat := 4983230072969 + 3 ^ 40 * 650109 * 2
def baseEnd_650109 : Nat := 111272798271300726415903

theorem tailTrace_650109 : CollatzResearch.WordTrace tailWord_650109 prefixEnd_650109 111272798271300726415903 := by
  unfold tailWord_650109
  simp only [CollatzResearch.WordTrace]
  refine ⟨23711423201773597622777381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15807615467849065081851587 23711423201773597622777381)
  ·
    refine ⟨4445891850332549554270759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23711423201773597622777381 4445891850332549554270759)
    ·
      refine ⟨6668837775498824331406139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4445891850332549554270759 6668837775498824331406139)
      ·
        refine ⟨10003256663248236497109209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6668837775498824331406139 10003256663248236497109209)
        ·
          refine ⟨7502442497436177372831907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10003256663248236497109209 7502442497436177372831907)
          ·
            refine ⟨11253663746154266059247861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7502442497436177372831907 11253663746154266059247861)
            ·
              refine ⟨1055030976201962443054487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11253663746154266059247861 1055030976201962443054487)
              ·
                refine ⟨1582546464302943664581731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055030976201962443054487 1582546464302943664581731)
                ·
                  refine ⟨2373819696454415496872597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582546464302943664581731 2373819696454415496872597)
                  ·
                    refine ⟨111272798271300726415903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2373819696454415496872597 111272798271300726415903)
                    ·
                      rfl

theorem cell23_650109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_650109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650109 prefixEnd_650109 := by exact prefixLift 650109
  have htrace : WordTrace (prefixWord ++ tailWord_650109) baseStart_650109 baseEnd_650109 := by
    simpa [prefixWord, tailWord_650109, baseEnd_650109] using wordTrace_append hprefix tailTrace_650109
  have hstable : (prefixWord ++ tailWord_650109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650109).length < 2 ^ (prefixWord ++ tailWord_650109).sum := by decide
  have hdescent : baseEnd_650109 < baseStart_650109 := by decide
  rcases family_descends (prefixWord ++ tailWord_650109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650210 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_650210 : Nat := 118140960795 + 650210 * 2 ^ 59
def prefixEnd_650210 : Nat := 4983230072969 + 3 ^ 40 * 650210 * 2
def baseEnd_650210 : Nat := 333870256360006284084745

theorem tailTrace_650210 : CollatzResearch.WordTrace tailWord_650210 prefixEnd_650210 333870256360006284084745 := by
  unfold tailWord_650210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5928776743601922968051021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15810071316271794581469389 5928776743601922968051021)
  ·
    refine ⟨2223291278850721113019133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5928776743601922968051021 2223291278850721113019133)
    ·
      refine ⟨833734229569020417382175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2223291278850721113019133 833734229569020417382175)
      ·
        refine ⟨1250601344353530626073263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833734229569020417382175 1250601344353530626073263)
        ·
          refine ⟨1875902016530295939109895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250601344353530626073263 1875902016530295939109895)
          ·
            refine ⟨2813853024795443908664843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875902016530295939109895 2813853024795443908664843)
            ·
              refine ⟨4220779537193165862997265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813853024795443908664843 4220779537193165862997265)
              ·
                refine ⟨3165584652894874397247949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220779537193165862997265 3165584652894874397247949)
                ·
                  refine ⟨1187094244835577898967981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3165584652894874397247949 1187094244835577898967981)
                  ·
                    refine ⟨445160341813341712112993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187094244835577898967981 445160341813341712112993)
                    ·
                      refine ⟨333870256360006284084745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445160341813341712112993 333870256360006284084745)
                      ·
                        rfl

theorem cell23_650210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_650210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650210 prefixEnd_650210 := by exact prefixLift 650210
  have htrace : WordTrace (prefixWord ++ tailWord_650210) baseStart_650210 baseEnd_650210 := by
    simpa [prefixWord, tailWord_650210, baseEnd_650210] using wordTrace_append hprefix tailTrace_650210
  have hstable : (prefixWord ++ tailWord_650210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650210).length < 2 ^ (prefixWord ++ tailWord_650210).sum := by decide
  have hdescent : baseEnd_650210 < baseStart_650210 := by decide
  rcases family_descends (prefixWord ++ tailWord_650210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650223 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 1, 4, 2]
def baseStart_650223 : Nat := 118140960795 + 650223 * 2 ^ 59
def prefixEnd_650223 : Nat := 4983230072969 + 3 ^ 40 * 650223 * 2
def baseEnd_650223 : Nat := 333876931608514733222185

theorem tailTrace_650223 : CollatzResearch.WordTrace tailWord_650223 prefixEnd_650223 333876931608514733222185 := by
  unfold tailWord_650223
  simp only [CollatzResearch.WordTrace]
  refine ⟨23715581123360595092427323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15810387415573730061618215 23715581123360595092427323)
  ·
    refine ⟨35573371685040892638640985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23715581123360595092427323 35573371685040892638640985)
    ·
      refine ⟨26680028763780669478980739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35573371685040892638640985 26680028763780669478980739)
      ·
        refine ⟨40020043145671004218471109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26680028763780669478980739 40020043145671004218471109)
        ·
          refine ⟨7503758089813313290963333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40020043145671004218471109 7503758089813313290963333)
          ·
            refine ⟨1406954641839996242055625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7503758089813313290963333 1406954641839996242055625)
            ·
              refine ⟨1055215981379997181541719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1406954641839996242055625 1055215981379997181541719)
              ·
                refine ⟨1582823972069995772312579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055215981379997181541719 1582823972069995772312579)
                ·
                  refine ⟨2374235958104993658468869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582823972069995772312579 2374235958104993658468869)
                  ·
                    refine ⟨445169242144686310962913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2374235958104993658468869 445169242144686310962913)
                    ·
                      refine ⟨333876931608514733222185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445169242144686310962913 333876931608514733222185)
                      ·
                        rfl

theorem cell23_650223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4, 2].length) (baseStart_650223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650223 prefixEnd_650223 := by exact prefixLift 650223
  have htrace : WordTrace (prefixWord ++ tailWord_650223) baseStart_650223 baseEnd_650223 := by
    simpa [prefixWord, tailWord_650223, baseEnd_650223] using wordTrace_append hprefix tailTrace_650223
  have hstable : (prefixWord ++ tailWord_650223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650223).length < 2 ^ (prefixWord ++ tailWord_650223).sum := by decide
  have hdescent : baseEnd_650223 < baseStart_650223 := by decide
  rcases family_descends (prefixWord ++ tailWord_650223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650259 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 4, 5]
def baseStart_650259 : Nat := 118140960795 + 650259 * 2 ^ 59
def prefixEnd_650259 : Nat := 4983230072969 + 3 ^ 40 * 650259 * 2
def baseEnd_650259 : Nat := 111298472304025530790673

theorem tailTrace_650259 : CollatzResearch.WordTrace tailWord_650259 prefixEnd_650259 111298472304025530790673 := by
  unfold tailWord_650259
  simp only [CollatzResearch.WordTrace]
  refine ⟨23716894151230173240737831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15811262767486782160491887 23716894151230173240737831)
  ·
    refine ⟨35575341226845259861106747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23716894151230173240737831 35575341226845259861106747)
    ·
      refine ⟨53363011840267889791660121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35575341226845259861106747 53363011840267889791660121)
      ·
        refine ⟨40022258880200917343745091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53363011840267889791660121 40022258880200917343745091)
        ·
          refine ⟨60033388320301376015617637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40022258880200917343745091 60033388320301376015617637)
          ·
            refine ⟨11256260310056508002928307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60033388320301376015617637 11256260310056508002928307)
            ·
              refine ⟨16884390465084762004392461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11256260310056508002928307 16884390465084762004392461)
              ·
                refine ⟨6331646424406785751647173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16884390465084762004392461 6331646424406785751647173)
                ·
                  refine ⟨1187183704576272328433845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6331646424406785751647173 1187183704576272328433845)
                  ·
                    refine ⟨111298472304025530790673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1187183704576272328433845 111298472304025530790673)
                    ·
                      rfl

theorem cell23_650259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 5].length) (baseStart_650259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650259 prefixEnd_650259 := by exact prefixLift 650259
  have htrace : WordTrace (prefixWord ++ tailWord_650259) baseStart_650259 baseEnd_650259 := by
    simpa [prefixWord, tailWord_650259, baseEnd_650259] using wordTrace_append hprefix tailTrace_650259
  have hstable : (prefixWord ++ tailWord_650259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650259).length < 2 ^ (prefixWord ++ tailWord_650259).sum := by decide
  have hdescent : baseEnd_650259 < baseStart_650259 := by decide
  rcases family_descends (prefixWord ++ tailWord_650259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650263 : List Nat := [1, 1, 3, 5, 1, 1, 2, 4, 5]
def baseStart_650263 : Nat := 118140960795 + 650263 * 2 ^ 59
def prefixEnd_650263 : Nat := 4983230072969 + 3 ^ 40 * 650263 * 2
def baseEnd_650263 : Nat := 37099718981632730746889

theorem tailTrace_650263 : CollatzResearch.WordTrace tailWord_650263 prefixEnd_650263 37099718981632730746889 := by
  unfold tailWord_650263
  simp only [CollatzResearch.WordTrace]
  refine ⟨23717040043215681923883443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15811360028810454615922295 23717040043215681923883443)
  ·
    refine ⟨35575560064823522885825165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23717040043215681923883443 35575560064823522885825165)
    ·
      refine ⟨13340835024308821082184437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35575560064823522885825165 13340835024308821082184437)
      ·
        refine ⟨1250703283528951976454791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13340835024308821082184437 1250703283528951976454791)
        ·
          refine ⟨1876054925293427964682187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250703283528951976454791 1876054925293427964682187)
          ·
            refine ⟨2814082387940141947023281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876054925293427964682187 2814082387940141947023281)
            ·
              refine ⟨2110561790955106460267461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814082387940141947023281 2110561790955106460267461)
              ·
                refine ⟨395730335804082461300149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2110561790955106460267461 395730335804082461300149)
                ·
                  refine ⟨37099718981632730746889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 395730335804082461300149 37099718981632730746889)
                  ·
                    rfl

theorem cell23_650263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 5].length) (baseStart_650263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650263 prefixEnd_650263 := by exact prefixLift 650263
  have htrace : WordTrace (prefixWord ++ tailWord_650263) baseStart_650263 baseEnd_650263 := by
    simpa [prefixWord, tailWord_650263, baseEnd_650263] using wordTrace_append hprefix tailTrace_650263
  have hstable : (prefixWord ++ tailWord_650263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650263).length < 2 ^ (prefixWord ++ tailWord_650263).sum := by decide
  have hdescent : baseEnd_650263 < baseStart_650263 := by decide
  rcases family_descends (prefixWord ++ tailWord_650263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650276 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_650276 : Nat := 118140960795 + 650276 * 2 ^ 59
def prefixEnd_650276 : Nat := 4983230072969 + 3 ^ 40 * 650276 * 2
def baseEnd_650276 : Nat := 111301382027734341953147

theorem tailTrace_650276 : CollatzResearch.WordTrace tailWord_650276 prefixEnd_650276 111301382027734341953147 := by
  unfold tailWord_650276
  simp only [CollatzResearch.WordTrace]
  refine ⟨11858757096084292572053341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15811676128112390096071121 11858757096084292572053341)
  ·
    refine ⟨4447033911031609714520003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11858757096084292572053341 4447033911031609714520003)
    ·
      refine ⟨6670550866547414571780005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4447033911031609714520003 6670550866547414571780005)
      ·
        refine ⟨1250728287477640232208751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6670550866547414571780005 1250728287477640232208751)
        ·
          refine ⟨1876092431216460348313127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250728287477640232208751 1876092431216460348313127)
          ·
            refine ⟨2814138646824690522469691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876092431216460348313127 2814138646824690522469691)
            ·
              refine ⟨4221207970237035783704537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814138646824690522469691 4221207970237035783704537)
              ·
                refine ⟨3165905977677776837778403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4221207970237035783704537 3165905977677776837778403)
                ·
                  refine ⟨4748858966516665256667605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165905977677776837778403 4748858966516665256667605)
                  ·
                    refine ⟨111301382027734341953147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4748858966516665256667605 111301382027734341953147)
                    ·
                      rfl

theorem cell23_650276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_650276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650276 prefixEnd_650276 := by exact prefixLift 650276
  have htrace : WordTrace (prefixWord ++ tailWord_650276) baseStart_650276 baseEnd_650276 := by
    simpa [prefixWord, tailWord_650276, baseEnd_650276] using wordTrace_append hprefix tailTrace_650276
  have hstable : (prefixWord ++ tailWord_650276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650276).length < 2 ^ (prefixWord ++ tailWord_650276).sum := by decide
  have hdescent : baseEnd_650276 < baseStart_650276 := by decide
  rcases family_descends (prefixWord ++ tailWord_650276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650289 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 2, 8]
def baseStart_650289 : Nat := 118140960795 + 650289 * 2 ^ 59
def prefixEnd_650289 : Nat := 4983230072969 + 3 ^ 40 * 650289 * 2
def baseEnd_650289 : Nat := 111303607110570491665627

theorem tailTrace_650289 : CollatzResearch.WordTrace tailWord_650289 prefixEnd_650289 111303607110570491665627 := by
  unfold tailWord_650289
  simp only [CollatzResearch.WordTrace]
  refine ⟨23717988341121488364329921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15811992227414325576219947 23717988341121488364329921)
  ·
    refine ⟨17788491255841116273247441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23717988341121488364329921 17788491255841116273247441)
    ·
      refine ⟨13341368441880837204935581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17788491255841116273247441 13341368441880837204935581)
      ·
        refine ⟨5003013165705313951850843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13341368441880837204935581 5003013165705313951850843)
        ·
          refine ⟨7504519748557970927776265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5003013165705313951850843 7504519748557970927776265)
          ·
            refine ⟨5628389811418478195832199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7504519748557970927776265 5628389811418478195832199)
            ·
              refine ⟨8442584717127717293748299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5628389811418478195832199 8442584717127717293748299)
              ·
                refine ⟨12663877075691575940622449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8442584717127717293748299 12663877075691575940622449)
                ·
                  refine ⟨9497907806768681955466837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12663877075691575940622449 9497907806768681955466837)
                  ·
                    refine ⟨111303607110570491665627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9497907806768681955466837 111303607110570491665627)
                    ·
                      rfl

theorem cell23_650289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_650289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650289 prefixEnd_650289 := by exact prefixLift 650289
  have htrace : WordTrace (prefixWord ++ tailWord_650289) baseStart_650289 baseEnd_650289 := by
    simpa [prefixWord, tailWord_650289, baseEnd_650289] using wordTrace_append hprefix tailTrace_650289
  have hstable : (prefixWord ++ tailWord_650289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650289).length < 2 ^ (prefixWord ++ tailWord_650289).sum := by decide
  have hdescent : baseEnd_650289 < baseStart_650289 := by decide
  rcases family_descends (prefixWord ++ tailWord_650289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650296 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_650296 : Nat := 118140960795 + 650296 * 2 ^ 59
def prefixEnd_650296 : Nat := 4983230072969 + 3 ^ 40 * 650296 * 2
def baseEnd_650296 : Nat := 333914415696292947609349

theorem tailTrace_650296 : CollatzResearch.WordTrace tailWord_650296 prefixEnd_650296 333914415696292947609349 := by
  unfold tailWord_650296
  simp only [CollatzResearch.WordTrace]
  refine ⟨11859121826048064279917371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15812162434730752373223161 11859121826048064279917371)
  ·
    refine ⟨17788682739072096419876057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11859121826048064279917371 17788682739072096419876057)
    ·
      refine ⟨13341512054304072314907043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17788682739072096419876057 13341512054304072314907043)
      ·
        refine ⟨20012268081456108472360565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13341512054304072314907043 20012268081456108472360565)
        ·
          refine ⟨1876150132636510169283803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20012268081456108472360565 1876150132636510169283803)
          ·
            refine ⟨2814225198954765253925705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876150132636510169283803 2814225198954765253925705)
            ·
              refine ⟨2110668899216073940444279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814225198954765253925705 2110668899216073940444279)
              ·
                refine ⟨3166003348824110910666419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110668899216073940444279 3166003348824110910666419)
                ·
                  refine ⟨4749005023236166365999629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166003348824110910666419 4749005023236166365999629)
                  ·
                    refine ⟨1780876883713562387249861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4749005023236166365999629 1780876883713562387249861)
                    ·
                      refine ⟨333914415696292947609349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1780876883713562387249861 333914415696292947609349)
                      ·
                        rfl

theorem cell23_650296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_650296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650296 prefixEnd_650296 := by exact prefixLift 650296
  have htrace : WordTrace (prefixWord ++ tailWord_650296) baseStart_650296 baseEnd_650296 := by
    simpa [prefixWord, tailWord_650296, baseEnd_650296] using wordTrace_append hprefix tailTrace_650296
  have hstable : (prefixWord ++ tailWord_650296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650296).length < 2 ^ (prefixWord ++ tailWord_650296).sum := by decide
  have hdescent : baseEnd_650296 < baseStart_650296 := by decide
  rcases family_descends (prefixWord ++ tailWord_650296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650309 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_650309 : Nat := 118140960795 + 650309 * 2 ^ 59
def prefixEnd_650309 : Nat := 4983230072969 + 3 ^ 40 * 650309 * 2
def baseEnd_650309 : Nat := 333921090944801396746789

theorem tailTrace_650309 : CollatzResearch.WordTrace tailWord_650309 prefixEnd_650309 333921090944801396746789 := by
  unfold tailWord_650309
  simp only [CollatzResearch.WordTrace]
  refine ⟨23718717801049031780057981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15812478534032687853371987 23718717801049031780057981)
  ·
    refine ⟨8894519175393386917521743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23718717801049031780057981 8894519175393386917521743)
    ·
      refine ⟨13341778763090080376282615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8894519175393386917521743 13341778763090080376282615)
      ·
        refine ⟨20012668144635120564423923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13341778763090080376282615 20012668144635120564423923)
        ·
          refine ⟨30019002216952680846635885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20012668144635120564423923 30019002216952680846635885)
          ·
            refine ⟨11257125831357255317488457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30019002216952680846635885 11257125831357255317488457)
            ·
              refine ⟨8442844373517941488116343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11257125831357255317488457 8442844373517941488116343)
              ·
                refine ⟨12664266560276912232174515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8442844373517941488116343 12664266560276912232174515)
                ·
                  refine ⟨18996399840415368348261773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12664266560276912232174515 18996399840415368348261773)
                  ·
                    refine ⟨7123649940155763130598165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18996399840415368348261773 7123649940155763130598165)
                    ·
                      refine ⟨333921090944801396746789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7123649940155763130598165 333921090944801396746789)
                      ·
                        rfl

theorem cell23_650309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_650309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650309 prefixEnd_650309 := by exact prefixLift 650309
  have htrace : WordTrace (prefixWord ++ tailWord_650309) baseStart_650309 baseEnd_650309 := by
    simpa [prefixWord, tailWord_650309, baseEnd_650309] using wordTrace_append hprefix tailTrace_650309
  have hstable : (prefixWord ++ tailWord_650309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650309).length < 2 ^ (prefixWord ++ tailWord_650309).sum := by decide
  have hdescent : baseEnd_650309 < baseStart_650309 := by decide
  rcases family_descends (prefixWord ++ tailWord_650309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650310 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_650310 : Nat := 118140960795 + 650310 * 2 ^ 59
def prefixEnd_650310 : Nat := 4983230072969 + 3 ^ 40 * 650310 * 2
def baseEnd_650310 : Nat := 111307201475151964278095

theorem tailTrace_650310 : CollatzResearch.WordTrace tailWord_650310 prefixEnd_650310 111307201475151964278095 := by
  unfold tailWord_650310
  simp only [CollatzResearch.WordTrace]
  refine ⟨741211071063919029713887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15812502849363605967229589 741211071063919029713887)
  ·
    refine ⟨1111816606595878544570831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741211071063919029713887 1111816606595878544570831)
    ·
      refine ⟨1667724909893817816856247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111816606595878544570831 1667724909893817816856247)
      ·
        refine ⟨2501587364840726725284371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667724909893817816856247 2501587364840726725284371)
        ·
          refine ⟨3752381047261090087926557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501587364840726725284371 3752381047261090087926557)
          ·
            refine ⟨1407142892722908782972459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3752381047261090087926557 1407142892722908782972459)
            ·
              refine ⟨2110714339084363174458689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407142892722908782972459 2110714339084363174458689)
              ·
                refine ⟨1583035754313272380844017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110714339084363174458689 1583035754313272380844017)
                ·
                  refine ⟨1187276815734954285633013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1583035754313272380844017 1187276815734954285633013)
                  ·
                    refine ⟨111307201475151964278095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1187276815734954285633013 111307201475151964278095)
                    ·
                      rfl

theorem cell23_650310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_650310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650310 prefixEnd_650310 := by exact prefixLift 650310
  have htrace : WordTrace (prefixWord ++ tailWord_650310) baseStart_650310 baseEnd_650310 := by
    simpa [prefixWord, tailWord_650310, baseEnd_650310] using wordTrace_append hprefix tailTrace_650310
  have hstable : (prefixWord ++ tailWord_650310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650310).length < 2 ^ (prefixWord ++ tailWord_650310).sum := by decide
  have hdescent : baseEnd_650310 < baseStart_650310 := by decide
  rcases family_descends (prefixWord ++ tailWord_650310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650336 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 6]
def baseStart_650336 : Nat := 118140960795 + 650336 * 2 ^ 59
def prefixEnd_650336 : Nat := 4983230072969 + 3 ^ 40 * 650336 * 2
def baseEnd_650336 : Nat := 37103883880274754567685

theorem tailTrace_650336 : CollatzResearch.WordTrace tailWord_650336 prefixEnd_650336 37103883880274754567685 := by
  unfold tailWord_650336
  simp only [CollatzResearch.WordTrace]
  refine ⟨11859851285975607695645431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15813135047967476927527241 11859851285975607695645431)
  ·
    refine ⟨17789776928963411543468147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11859851285975607695645431 17789776928963411543468147)
    ·
      refine ⟨26684665393445117315202221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17789776928963411543468147 26684665393445117315202221)
      ·
        refine ⟨10006749522541918993200833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26684665393445117315202221 10006749522541918993200833)
        ·
          refine ⟨7505062141906439244900625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10006749522541918993200833 7505062141906439244900625)
          ·
            refine ⟨5628796606429829433675469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7505062141906439244900625 5628796606429829433675469)
            ·
              refine ⟨2110798727411186037628301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5628796606429829433675469 2110798727411186037628301)
              ·
                refine ⟨791549522779194764110613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2110798727411186037628301 791549522779194764110613)
                ·
                  refine ⟨37103883880274754567685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 791549522779194764110613 37103883880274754567685)
                  ·
                    rfl

theorem cell23_650336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 6].length) (baseStart_650336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650336 prefixEnd_650336 := by exact prefixLift 650336
  have htrace : WordTrace (prefixWord ++ tailWord_650336) baseStart_650336 baseEnd_650336 := by
    simpa [prefixWord, tailWord_650336, baseEnd_650336] using wordTrace_append hprefix tailTrace_650336
  have hstable : (prefixWord ++ tailWord_650336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650336).length < 2 ^ (prefixWord ++ tailWord_650336).sum := by decide
  have hdescent : baseEnd_650336 < baseStart_650336 := by decide
  rcases family_descends (prefixWord ++ tailWord_650336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650350 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_650350 : Nat := 118140960795 + 650350 * 2 ^ 59
def prefixEnd_650350 : Nat := 4983230072969 + 3 ^ 40 * 650350 * 2
def baseEnd_650350 : Nat := 333942143651635736334101

theorem tailTrace_650350 : CollatzResearch.WordTrace tailWord_650350 prefixEnd_650350 333942143651635736334101 := by
  unfold tailWord_650350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965026649237561972787563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15813475462600330521533669 2965026649237561972787563)
  ·
    refine ⟨4447539973856342959181345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2965026649237561972787563 4447539973856342959181345)
    ·
      refine ⟨3335654980392257219386009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4447539973856342959181345 3335654980392257219386009)
      ·
        refine ⟨2501741235294192914539507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3335654980392257219386009 2501741235294192914539507)
        ·
          refine ⟨3752611852941289371809261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501741235294192914539507 3752611852941289371809261)
          ·
            refine ⟨1407229444852983514428473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3752611852941289371809261 1407229444852983514428473)
            ·
              refine ⟨1055422083639737635821355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407229444852983514428473 1055422083639737635821355)
              ·
                refine ⟨1583133125459606453732033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055422083639737635821355 1583133125459606453732033)
                ·
                  refine ⟨1187349844094704840299025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1583133125459606453732033 1187349844094704840299025)
                  ·
                    refine ⟨890512383071028630224269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1187349844094704840299025 890512383071028630224269)
                    ·
                      refine ⟨333942143651635736334101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 890512383071028630224269 333942143651635736334101)
                      ·
                        rfl

theorem cell23_650350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_650350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650350 prefixEnd_650350 := by exact prefixLift 650350
  have htrace : WordTrace (prefixWord ++ tailWord_650350) baseStart_650350 baseEnd_650350 := by
    simpa [prefixWord, tailWord_650350, baseEnd_650350] using wordTrace_append hprefix tailTrace_650350
  have hstable : (prefixWord ++ tailWord_650350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650350).length < 2 ^ (prefixWord ++ tailWord_650350).sum := by decide
  have hdescent : baseEnd_650350 < baseStart_650350 := by decide
  rcases family_descends (prefixWord ++ tailWord_650350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650407 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_650407 : Nat := 118140960795 + 650407 * 2 ^ 59
def prefixEnd_650407 : Nat := 4983230072969 + 3 ^ 40 * 650407 * 2
def baseEnd_650407 : Nat := 333971412048942013321339

theorem tailTrace_650407 : CollatzResearch.WordTrace tailWord_650407 prefixEnd_650407 333971412048942013321339 := by
  unfold tailWord_650407
  simp only [CollatzResearch.WordTrace]
  refine ⟨23722292154693994517125475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15814861436462663011416983 23722292154693994517125475)
  ·
    refine ⟨35583438232040991775688213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23722292154693994517125475 35583438232040991775688213)
    ·
      refine ⟨1667973667126921489485385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35583438232040991775688213 1667973667126921489485385)
      ·
        refine ⟨1250980250345191117114039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1667973667126921489485385 1250980250345191117114039)
        ·
          refine ⟨1876470375517786675671059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250980250345191117114039 1876470375517786675671059)
          ·
            refine ⟨2814705563276680013506589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876470375517786675671059 2814705563276680013506589)
            ·
              refine ⟨1055514586228755005064971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2814705563276680013506589 1055514586228755005064971)
              ·
                refine ⟨1583271879343132507597457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055514586228755005064971 1583271879343132507597457)
                ·
                  refine ⟨1187453909507349380698093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1583271879343132507597457 1187453909507349380698093)
                  ·
                    refine ⟨445295216065256017761785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187453909507349380698093 445295216065256017761785)
                    ·
                      refine ⟨333971412048942013321339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445295216065256017761785 333971412048942013321339)
                      ·
                        rfl

theorem cell23_650407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_650407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650407 prefixEnd_650407 := by exact prefixLift 650407
  have htrace : WordTrace (prefixWord ++ tailWord_650407) baseStart_650407 baseEnd_650407 := by
    simpa [prefixWord, tailWord_650407, baseEnd_650407] using wordTrace_append hprefix tailTrace_650407
  have hstable : (prefixWord ++ tailWord_650407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650407).length < 2 ^ (prefixWord ++ tailWord_650407).sum := by decide
  have hdescent : baseEnd_650407 < baseStart_650407 := by decide
  rcases family_descends (prefixWord ++ tailWord_650407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650417 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 1, 5]
def baseStart_650417 : Nat := 118140960795 + 650417 * 2 ^ 59
def prefixEnd_650417 : Nat := 4983230072969 + 3 ^ 40 * 650417 * 2
def baseEnd_650417 : Nat := 111325515618495658065431

theorem tailTrace_650417 : CollatzResearch.WordTrace tailWord_650417 prefixEnd_650417 111325515618495658065431 := by
  unfold tailWord_650417
  simp only [CollatzResearch.WordTrace]
  refine ⟨23722656884657766224989505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15815104589771844149993003 23722656884657766224989505)
  ·
    refine ⟨17791992663493324668742129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23722656884657766224989505 17791992663493324668742129)
    ·
      refine ⟨13343994497619993501556597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17791992663493324668742129 13343994497619993501556597)
      ·
        refine ⟨1250999484151874390770931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13343994497619993501556597 1250999484151874390770931)
        ·
          refine ⟨1876499226227811586156397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250999484151874390770931 1876499226227811586156397)
          ·
            refine ⟨703687209835429344808649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1876499226227811586156397 703687209835429344808649)
            ·
              refine ⟨527765407376572008606487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703687209835429344808649 527765407376572008606487)
              ·
                refine ⟨791648111064858012909731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527765407376572008606487 791648111064858012909731)
                ·
                  refine ⟨1187472166597287019364597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791648111064858012909731 1187472166597287019364597)
                  ·
                    refine ⟨111325515618495658065431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1187472166597287019364597 111325515618495658065431)
                    ·
                      rfl

theorem cell23_650417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_650417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650417 prefixEnd_650417 := by exact prefixLift 650417
  have htrace : WordTrace (prefixWord ++ tailWord_650417) baseStart_650417 baseEnd_650417 := by
    simpa [prefixWord, tailWord_650417, baseEnd_650417] using wordTrace_append hprefix tailTrace_650417
  have hstable : (prefixWord ++ tailWord_650417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650417).length < 2 ^ (prefixWord ++ tailWord_650417).sum := by decide
  have hdescent : baseEnd_650417 < baseStart_650417 := by decide
  rcases family_descends (prefixWord ++ tailWord_650417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650430 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_650430 : Nat := 118140960795 + 650430 * 2 ^ 59
def prefixEnd_650430 : Nat := 4983230072969 + 3 ^ 40 * 650430 * 2
def baseEnd_650430 : Nat := 111327740701331807777911

theorem tailTrace_650430 : CollatzResearch.WordTrace tailWord_650430 prefixEnd_650430 111327740701331807777911 := by
  unfold tailWord_650430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965391379201333680651593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15815420689073779630141829 2965391379201333680651593)
  ·
    refine ⟨2224043534401000260488695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2965391379201333680651593 2224043534401000260488695)
    ·
      refine ⟨3336065301601500390733043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224043534401000260488695 3336065301601500390733043)
      ·
        refine ⟨5004097952402250586099565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336065301601500390733043 5004097952402250586099565)
        ·
          refine ⟨1876536732150843969787337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5004097952402250586099565 1876536732150843969787337)
          ·
            refine ⟨1407402549113132977340503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876536732150843969787337 1407402549113132977340503)
            ·
              refine ⟨2111103823669699466010755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407402549113132977340503 2111103823669699466010755)
              ·
                refine ⟨3166655735504549199016133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111103823669699466010755 3166655735504549199016133)
                ·
                  refine ⟨593747950407102974815525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3166655735504549199016133 593747950407102974815525)
                  ·
                    refine ⟨111327740701331807777911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 593747950407102974815525 111327740701331807777911)
                    ·
                      rfl

theorem cell23_650430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_650430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650430 prefixEnd_650430 := by exact prefixLift 650430
  have htrace : WordTrace (prefixWord ++ tailWord_650430) baseStart_650430 baseEnd_650430 := by
    simpa [prefixWord, tailWord_650430, baseEnd_650430] using wordTrace_append hprefix tailTrace_650430
  have hstable : (prefixWord ++ tailWord_650430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650430).length < 2 ^ (prefixWord ++ tailWord_650430).sum := by decide
  have hdescent : baseEnd_650430 < baseStart_650430 := by decide
  rcases family_descends (prefixWord ++ tailWord_650430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650454 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_650454 : Nat := 118140960795 + 650454 * 2 ^ 59
def prefixEnd_650454 : Nat := 4983230072969 + 3 ^ 40 * 650454 * 2
def baseEnd_650454 : Nat := 333995545639703329433623

theorem tailTrace_650454 : CollatzResearch.WordTrace tailWord_650454 prefixEnd_650454 333995545639703329433623 := by
  unfold tailWord_650454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482750399095232596505401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15816004257015814362724277 1482750399095232596505401)
  ·
    refine ⟨1112062799321424447379051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1482750399095232596505401 1112062799321424447379051)
    ·
      refine ⟨1668094198982136671068577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112062799321424447379051 1668094198982136671068577)
      ·
        refine ⟨1251070649236602503301433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1668094198982136671068577 1251070649236602503301433)
        ·
          refine ⟨938302986927451877476075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251070649236602503301433 938302986927451877476075)
          ·
            refine ⟨1407454480391177816214113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938302986927451877476075 1407454480391177816214113)
            ·
              refine ⟨1055590860293383362160585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407454480391177816214113 1055590860293383362160585)
              ·
                refine ⟨791693145220037521620439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055590860293383362160585 791693145220037521620439)
                ·
                  refine ⟨1187539717830056282430659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791693145220037521620439 1187539717830056282430659)
                  ·
                    refine ⟨1781309576745084423645989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1187539717830056282430659 1781309576745084423645989)
                    ·
                      refine ⟨333995545639703329433623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1781309576745084423645989 333995545639703329433623)
                      ·
                        rfl

theorem cell23_650454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_650454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650454 prefixEnd_650454 := by exact prefixLift 650454
  have htrace : WordTrace (prefixWord ++ tailWord_650454) baseStart_650454 baseEnd_650454 := by
    simpa [prefixWord, tailWord_650454, baseEnd_650454] using wordTrace_append hprefix tailTrace_650454
  have hstable : (prefixWord ++ tailWord_650454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650454).length < 2 ^ (prefixWord ++ tailWord_650454).sum := by decide
  have hdescent : baseEnd_650454 < baseStart_650454 := by decide
  rcases family_descends (prefixWord ++ tailWord_650454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650496 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_650496 : Nat := 118140960795 + 650496 * 2 ^ 59
def prefixEnd_650496 : Nat := 4983230072969 + 3 ^ 40 * 650496 * 2
def baseEnd_650496 : Nat := 334017111827192165108429

theorem tailTrace_650496 : CollatzResearch.WordTrace tailWord_650496 prefixEnd_650496 334017111827192165108429 := by
  unfold tailWord_650496
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862769125685781358557671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15817025500914375144743561 11862769125685781358557671)
  ·
    refine ⟨17794153688528672037836507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11862769125685781358557671 17794153688528672037836507)
    ·
      refine ⟨26691230532793008056754761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17794153688528672037836507 26691230532793008056754761)
      ·
        refine ⟨20018422899594756042566071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26691230532793008056754761 20018422899594756042566071)
        ·
          refine ⟨30027634349392134063849107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20018422899594756042566071 30027634349392134063849107)
          ·
            refine ⟨45041451524088201095773661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30027634349392134063849107 45041451524088201095773661)
            ·
              refine ⟨16890544321533075410915123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45041451524088201095773661 16890544321533075410915123)
              ·
                refine ⟨25335816482299613116372685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16890544321533075410915123 25335816482299613116372685)
                ·
                  refine ⟨9500931180862354918639757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25335816482299613116372685 9500931180862354918639757)
                  ·
                    refine ⟨3562849192823383094489909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9500931180862354918639757 3562849192823383094489909)
                    ·
                      refine ⟨334017111827192165108429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3562849192823383094489909 334017111827192165108429)
                      ·
                        rfl

theorem cell23_650496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_650496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650496 prefixEnd_650496 := by exact prefixLift 650496
  have htrace : WordTrace (prefixWord ++ tailWord_650496) baseStart_650496 baseEnd_650496 := by
    simpa [prefixWord, tailWord_650496, baseEnd_650496] using wordTrace_append hprefix tailTrace_650496
  have hstable : (prefixWord ++ tailWord_650496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650496).length < 2 ^ (prefixWord ++ tailWord_650496).sum := by decide
  have hdescent : baseEnd_650496 < baseStart_650496 := by decide
  rcases family_descends (prefixWord ++ tailWord_650496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650527 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 1, 4, 2]
def baseStart_650527 : Nat := 118140960795 + 650527 * 2 ^ 59
def prefixEnd_650527 : Nat := 4983230072969 + 3 ^ 40 * 650527 * 2
def baseEnd_650527 : Nat := 334033029727481543820787

theorem tailTrace_650527 : CollatzResearch.WordTrace tailWord_650527 prefixEnd_650527 334033029727481543820787 := by
  unfold tailWord_650527
  simp only [CollatzResearch.WordTrace]
  refine ⟨23726668914259255011493835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15817779276172836674329223 23726668914259255011493835)
  ·
    refine ⟨35590003371388882517240753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23726668914259255011493835 35590003371388882517240753)
    ·
      refine ⟨26692502528541661887930565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35590003371388882517240753 26692502528541661887930565)
      ·
        refine ⟨5004844224101561603986981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26692502528541661887930565 5004844224101561603986981)
        ·
          refine ⟨938408292019042800747559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5004844224101561603986981 938408292019042800747559)
          ·
            refine ⟨1407612438028564201121339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938408292019042800747559 1407612438028564201121339)
            ·
              refine ⟨2111418657042846301682009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407612438028564201121339 2111418657042846301682009)
              ·
                refine ⟨1583563992782134726261507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111418657042846301682009 1583563992782134726261507)
                ·
                  refine ⟨2375345989173202089392261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583563992782134726261507 2375345989173202089392261)
                  ·
                    refine ⟨445377372969975391761049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2375345989173202089392261 445377372969975391761049)
                    ·
                      refine ⟨334033029727481543820787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445377372969975391761049 334033029727481543820787)
                      ·
                        rfl

theorem cell23_650527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_650527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650527 prefixEnd_650527 := by exact prefixLift 650527
  have htrace : WordTrace (prefixWord ++ tailWord_650527) baseStart_650527 baseEnd_650527 := by
    simpa [prefixWord, tailWord_650527, baseEnd_650527] using wordTrace_append hprefix tailTrace_650527
  have hstable : (prefixWord ++ tailWord_650527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650527).length < 2 ^ (prefixWord ++ tailWord_650527).sum := by decide
  have hdescent : baseEnd_650527 < baseStart_650527 := by decide
  rcases family_descends (prefixWord ++ tailWord_650527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650543 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 3]
def baseStart_650543 : Nat := 118140960795 + 650543 * 2 ^ 59
def prefixEnd_650543 : Nat := 4983230072969 + 3 ^ 40 * 650543 * 2
def baseEnd_650543 : Nat := 334041245417953481220713

theorem tailTrace_650543 : CollatzResearch.WordTrace tailWord_650543 prefixEnd_650543 334041245417953481220713 := by
  unfold tailWord_650543
  simp only [CollatzResearch.WordTrace]
  refine ⟨23727252482201289744076283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15818168321467526496050855 23727252482201289744076283)
  ·
    refine ⟨35590878723301934616114425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23727252482201289744076283 35590878723301934616114425)
    ·
      refine ⟨26693159042476450962085819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35590878723301934616114425 26693159042476450962085819)
      ·
        refine ⟨40039738563714676443128729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26693159042476450962085819 40039738563714676443128729)
        ·
          refine ⟨30029803922786007332346547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40039738563714676443128729 30029803922786007332346547)
          ·
            refine ⟨45044705884179010998519821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30029803922786007332346547 45044705884179010998519821)
            ·
              refine ⟨16891764706567129124444933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45044705884179010998519821 16891764706567129124444933)
              ·
                refine ⟨3167205882481336710833425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16891764706567129124444933 3167205882481336710833425)
                ·
                  refine ⟨2375404411861002533125069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3167205882481336710833425 2375404411861002533125069)
                  ·
                    refine ⟨890776654447875949921901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375404411861002533125069 890776654447875949921901)
                    ·
                      refine ⟨334041245417953481220713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 890776654447875949921901 334041245417953481220713)
                      ·
                        rfl

theorem cell23_650543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_650543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650543 prefixEnd_650543 := by exact prefixLift 650543
  have htrace : WordTrace (prefixWord ++ tailWord_650543) baseStart_650543 baseEnd_650543 := by
    simpa [prefixWord, tailWord_650543, baseEnd_650543] using wordTrace_append hprefix tailTrace_650543
  have hstable : (prefixWord ++ tailWord_650543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650543).length < 2 ^ (prefixWord ++ tailWord_650543).sum := by decide
  have hdescent : baseEnd_650543 < baseStart_650543 := by decide
  rcases family_descends (prefixWord ++ tailWord_650543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650557 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_650557 : Nat := 118140960795 + 650557 * 2 ^ 59
def prefixEnd_650557 : Nat := 4983230072969 + 3 ^ 40 * 650557 * 2
def baseEnd_650557 : Nat := 334048434147116426445649

theorem tailTrace_650557 : CollatzResearch.WordTrace tailWord_650557 prefixEnd_650557 334048434147116426445649 := by
  unfold tailWord_650557
  simp only [CollatzResearch.WordTrace]
  refine ⟨23727763104150570135085925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15818508736100380090057283 23727763104150570135085925)
  ·
    refine ⟨4448955582028231900328611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23727763104150570135085925 4448955582028231900328611)
    ·
      refine ⟨6673433373042347850492917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448955582028231900328611 6673433373042347850492917)
      ·
        refine ⟨625634378722720110983711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6673433373042347850492917 625634378722720110983711)
        ·
          refine ⟨938451568084080166475567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625634378722720110983711 938451568084080166475567)
          ·
            refine ⟨1407677352126120249713351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938451568084080166475567 1407677352126120249713351)
            ·
              refine ⟨2111516028189180374570027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407677352126120249713351 2111516028189180374570027)
              ·
                refine ⟨3167274042283770561855041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111516028189180374570027 3167274042283770561855041)
                ·
                  refine ⟨2375455531712827921391281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3167274042283770561855041 2375455531712827921391281)
                  ·
                    refine ⟨1781591648784620941043461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2375455531712827921391281 1781591648784620941043461)
                    ·
                      refine ⟨334048434147116426445649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1781591648784620941043461 334048434147116426445649)
                      ·
                        rfl

theorem cell23_650557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_650557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650557 prefixEnd_650557 := by exact prefixLift 650557
  have htrace : WordTrace (prefixWord ++ tailWord_650557) baseStart_650557 baseEnd_650557 := by
    simpa [prefixWord, tailWord_650557, baseEnd_650557] using wordTrace_append hprefix tailTrace_650557
  have hstable : (prefixWord ++ tailWord_650557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650557).length < 2 ^ (prefixWord ++ tailWord_650557).sum := by decide
  have hdescent : baseEnd_650557 < baseStart_650557 := by decide
  rcases family_descends (prefixWord ++ tailWord_650557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650582 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_650582 : Nat := 118140960795 + 650582 * 2 ^ 59
def prefixEnd_650582 : Nat := 4983230072969 + 3 ^ 40 * 650582 * 2
def baseEnd_650582 : Nat := 334061271163478828633035

theorem tailTrace_650582 : CollatzResearch.WordTrace tailWord_650582 prefixEnd_650582 334061271163478828633035 := by
  unfold tailWord_650582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483042183066249962796625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15819116619373332936497333 1483042183066249962796625)
  ·
    refine ⟨1112281637299687472097469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1483042183066249962796625 1112281637299687472097469)
    ·
      refine ⟨417105613987382802036551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1112281637299687472097469 417105613987382802036551)
      ·
        refine ⟨625658420981074203054827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417105613987382802036551 625658420981074203054827)
        ·
          refine ⟨938487631471611304582241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625658420981074203054827 938487631471611304582241)
          ·
            refine ⟨703865723603708478436681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 938487631471611304582241 703865723603708478436681)
            ·
              refine ⟨527899292702781358827511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703865723603708478436681 527899292702781358827511)
              ·
                refine ⟨791848939054172038241267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527899292702781358827511 791848939054172038241267)
                ·
                  refine ⟨1187773408581258057361901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791848939054172038241267 1187773408581258057361901)
                  ·
                    refine ⟨445415028217971771510713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187773408581258057361901 445415028217971771510713)
                    ·
                      refine ⟨334061271163478828633035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445415028217971771510713 334061271163478828633035)
                      ·
                        rfl

theorem cell23_650582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_650582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650582 prefixEnd_650582 := by exact prefixLift 650582
  have htrace : WordTrace (prefixWord ++ tailWord_650582) baseStart_650582 baseEnd_650582 := by
    simpa [prefixWord, tailWord_650582, baseEnd_650582] using wordTrace_append hprefix tailTrace_650582
  have hstable : (prefixWord ++ tailWord_650582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650582).length < 2 ^ (prefixWord ++ tailWord_650582).sum := by decide
  have hdescent : baseEnd_650582 < baseStart_650582 := by decide
  rcases family_descends (prefixWord ++ tailWord_650582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650603 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 3]
def baseStart_650603 : Nat := 118140960795 + 650603 * 2 ^ 59
def prefixEnd_650603 : Nat := 4983230072969 + 3 ^ 40 * 650603 * 2
def baseEnd_650603 : Nat := 334072054257223246470437

theorem tailTrace_650603 : CollatzResearch.WordTrace tailWord_650603 prefixEnd_650603 334072054257223246470437 := by
  unfold tailWord_650603
  simp only [CollatzResearch.WordTrace]
  refine ⟨23729440861983919991260463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15819627241322613327506975 23729440861983919991260463)
  ·
    refine ⟨35594161292975879986890695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23729440861983919991260463 35594161292975879986890695)
    ·
      refine ⟨53391241939463819980336043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35594161292975879986890695 53391241939463819980336043)
      ·
        refine ⟨80086862909195729970504065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53391241939463819980336043 80086862909195729970504065)
        ·
          refine ⟨60065147181896797477878049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80086862909195729970504065 60065147181896797477878049)
          ·
            refine ⟨45048860386422598108408537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60065147181896797477878049 45048860386422598108408537)
            ·
              refine ⟨33786645289816948581306403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45048860386422598108408537 33786645289816948581306403)
              ·
                refine ⟨50679967934725422871959605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33786645289816948581306403 50679967934725422871959605)
                ·
                  refine ⟨4751246993880508394246213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50679967934725422871959605 4751246993880508394246213)
                  ·
                    refine ⟨890858811352595323921165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751246993880508394246213 890858811352595323921165)
                    ·
                      refine ⟨334072054257223246470437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 890858811352595323921165 334072054257223246470437)
                      ·
                        rfl

theorem cell23_650603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 3].length) (baseStart_650603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650603 prefixEnd_650603 := by exact prefixLift 650603
  have htrace : WordTrace (prefixWord ++ tailWord_650603) baseStart_650603 baseEnd_650603 := by
    simpa [prefixWord, tailWord_650603, baseEnd_650603] using wordTrace_append hprefix tailTrace_650603
  have hstable : (prefixWord ++ tailWord_650603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650603).length < 2 ^ (prefixWord ++ tailWord_650603).sum := by decide
  have hdescent : baseEnd_650603 < baseStart_650603 := by decide
  rcases family_descends (prefixWord ++ tailWord_650603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650693 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_650693 : Nat := 118140960795 + 650693 * 2 ^ 59
def prefixEnd_650693 : Nat := 4983230072969 + 3 ^ 40 * 650693 * 2
def baseEnd_650693 : Nat := 334118267516127894345023

theorem tailTrace_650693 : CollatzResearch.WordTrace tailWord_650693 prefixEnd_650693 334118267516127894345023 := by
  unfold tailWord_650693
  simp only [CollatzResearch.WordTrace]
  refine ⟨23732723431657865362036733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15821815621105243574691155 23732723431657865362036733)
  ·
    refine ⟨8899771286871699510763775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23732723431657865362036733 8899771286871699510763775)
    ·
      refine ⟨13349656930307549266145663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8899771286871699510763775 13349656930307549266145663)
      ·
        refine ⟨20024485395461323899218495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13349656930307549266145663 20024485395461323899218495)
        ·
          refine ⟨30036728093191985848827743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20024485395461323899218495 30036728093191985848827743)
          ·
            refine ⟨45055092139787978773241615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30036728093191985848827743 45055092139787978773241615)
            ·
              refine ⟨67582638209681968159862423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45055092139787978773241615 67582638209681968159862423)
              ·
                refine ⟨101373957314522952239793635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67582638209681968159862423 101373957314522952239793635)
                ·
                  refine ⟨152060935971784428359690453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101373957314522952239793635 152060935971784428359690453)
                  ·
                    refine ⟨3563928186838697539680245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 152060935971784428359690453 3563928186838697539680245)
                    ·
                      refine ⟨334118267516127894345023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3563928186838697539680245 334118267516127894345023)
                      ·
                        rfl

theorem cell23_650693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_650693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650693 prefixEnd_650693 := by exact prefixLift 650693
  have htrace : WordTrace (prefixWord ++ tailWord_650693) baseStart_650693 baseEnd_650693 := by
    simpa [prefixWord, tailWord_650693, baseEnd_650693] using wordTrace_append hprefix tailTrace_650693
  have hstable : (prefixWord ++ tailWord_650693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650693).length < 2 ^ (prefixWord ++ tailWord_650693).sum := by decide
  have hdescent : baseEnd_650693 < baseStart_650693 := by decide
  rcases family_descends (prefixWord ++ tailWord_650693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650700 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_650700 : Nat := 118140960795 + 650700 * 2 ^ 59
def prefixEnd_650700 : Nat := 4983230072969 + 3 ^ 40 * 650700 * 2
def baseEnd_650700 : Nat := 111373953960236455652497

theorem tailTrace_650700 : CollatzResearch.WordTrace tailWord_650700 prefixEnd_650700 111373953960236455652497 := by
  unfold tailWord_650700
  simp only [CollatzResearch.WordTrace]
  refine ⟨11866489371316252778770777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15821985828421670371694369 11866489371316252778770777)
  ·
    refine ⟨8899867028487189584078083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11866489371316252778770777 8899867028487189584078083)
    ·
      refine ⟨13349800542730784376117125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8899867028487189584078083 13349800542730784376117125)
      ·
        refine ⟨2503087601762022070521961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13349800542730784376117125 2503087601762022070521961)
        ·
          refine ⟨1877315701321516552891471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2503087601762022070521961 1877315701321516552891471)
          ·
            refine ⟨2815973551982274829337207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877315701321516552891471 2815973551982274829337207)
            ·
              refine ⟨4223960327973412244005811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815973551982274829337207 4223960327973412244005811)
              ·
                refine ⟨6335940491960118366008717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223960327973412244005811 6335940491960118366008717)
                ·
                  refine ⟨2375977684485044387253269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6335940491960118366008717 2375977684485044387253269)
                  ·
                    refine ⟨111373953960236455652497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2375977684485044387253269 111373953960236455652497)
                    ·
                      rfl

theorem cell23_650700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_650700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650700 prefixEnd_650700 := by exact prefixLift 650700
  have htrace : WordTrace (prefixWord ++ tailWord_650700) baseStart_650700 baseEnd_650700 := by
    simpa [prefixWord, tailWord_650700, baseEnd_650700] using wordTrace_append hprefix tailTrace_650700
  have hstable : (prefixWord ++ tailWord_650700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650700).length < 2 ^ (prefixWord ++ tailWord_650700).sum := by decide
  have hdescent : baseEnd_650700 < baseStart_650700 := by decide
  rcases family_descends (prefixWord ++ tailWord_650700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650713 : List Nat := [1, 2, 1, 2, 4, 13]
def baseStart_650713 : Nat := 118140960795 + 650713 * 2 ^ 59
def prefixEnd_650713 : Nat := 4983230072969 + 3 ^ 40 * 650713 * 2
def baseEnd_650713 : Nat := 1375014556087316115617

theorem tailTrace_650713 : CollatzResearch.WordTrace tailWord_650713 prefixEnd_650713 1375014556087316115617 := by
  unfold tailWord_650713
  simp only [CollatzResearch.WordTrace]
  refine ⟨23733452891585408777764793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15822301927723605851843195 23733452891585408777764793)
  ·
    refine ⟨17800089668689056583323595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23733452891585408777764793 17800089668689056583323595)
    ·
      refine ⟨26700134503033584874985393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17800089668689056583323595 26700134503033584874985393)
      ·
        refine ⟨20025100877275188656239045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26700134503033584874985393 20025100877275188656239045)
        ·
          refine ⟨3754706414489097873044821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20025100877275188656239045 3754706414489097873044821)
          ·
            refine ⟨1375014556087316115617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 3754706414489097873044821 1375014556087316115617)
            ·
              rfl

theorem cell23_650713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 13].length) (baseStart_650713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650713 prefixEnd_650713 := by exact prefixLift 650713
  have htrace : WordTrace (prefixWord ++ tailWord_650713) baseStart_650713 baseEnd_650713 := by
    simpa [prefixWord, tailWord_650713, baseEnd_650713] using wordTrace_append hprefix tailTrace_650713
  have hstable : (prefixWord ++ tailWord_650713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650713).length < 2 ^ (prefixWord ++ tailWord_650713).sum := by decide
  have hdescent : baseEnd_650713 < baseStart_650713 := by decide
  rcases family_descends (prefixWord ++ tailWord_650713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650727 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_650727 : Nat := 118140960795 + 650727 * 2 ^ 59
def prefixEnd_650727 : Nat := 4983230072969 + 3 ^ 40 * 650727 * 2
def baseEnd_650727 : Nat := 334135725858380761319867

theorem tailTrace_650727 : CollatzResearch.WordTrace tailWord_650727 prefixEnd_650727 334135725858380761319867 := by
  unfold tailWord_650727
  simp only [CollatzResearch.WordTrace]
  refine ⟨23733963513534689168774435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15822642342356459445849623 23733963513534689168774435)
  ·
    refine ⟨35600945270302033753161653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23733963513534689168774435 35600945270302033753161653)
    ·
      refine ⟨3337588619090815664358905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35600945270302033753161653 3337588619090815664358905)
      ·
        refine ⟨2503191464318111748269179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3337588619090815664358905 2503191464318111748269179)
        ·
          refine ⟨3754787196477167622403769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2503191464318111748269179 3754787196477167622403769)
          ·
            refine ⟨2816090397357875716802827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3754787196477167622403769 2816090397357875716802827)
            ·
              refine ⟨4224135596036813575204241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816090397357875716802827 4224135596036813575204241)
              ·
                refine ⟨3168101697027610181403181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4224135596036813575204241 3168101697027610181403181)
                ·
                  refine ⟨1188038136385353818026193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3168101697027610181403181 1188038136385353818026193)
                  ·
                    refine ⟨891028602289015363519645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188038136385353818026193 891028602289015363519645)
                    ·
                      refine ⟨334135725858380761319867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 891028602289015363519645 334135725858380761319867)
                      ·
                        rfl

theorem cell23_650727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_650727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650727 prefixEnd_650727 := by exact prefixLift 650727
  have htrace : WordTrace (prefixWord ++ tailWord_650727) baseStart_650727 baseEnd_650727 := by
    simpa [prefixWord, tailWord_650727, baseEnd_650727] using wordTrace_append hprefix tailTrace_650727
  have hstable : (prefixWord ++ tailWord_650727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650727).length < 2 ^ (prefixWord ++ tailWord_650727).sum := by decide
  have hdescent : baseEnd_650727 < baseStart_650727 := by decide
  rcases family_descends (prefixWord ++ tailWord_650727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650737 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_650737 : Nat := 118140960795 + 650737 * 2 ^ 59
def prefixEnd_650737 : Nat := 4983230072969 + 3 ^ 40 * 650737 * 2
def baseEnd_650737 : Nat := 334140860664925722194821

theorem tailTrace_650737 : CollatzResearch.WordTrace tailWord_650737 prefixEnd_650737 334140860664925722194821 := by
  unfold tailWord_650737
  simp only [CollatzResearch.WordTrace]
  refine ⟨23734328243498460876638465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15822885495665640584425643 23734328243498460876638465)
  ·
    refine ⟨17800746182623845657478849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23734328243498460876638465 17800746182623845657478849)
    ·
      refine ⟨13350559636967884243109137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17800746182623845657478849 13350559636967884243109137)
      ·
        refine ⟨10012919727725913182331853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13350559636967884243109137 10012919727725913182331853)
        ·
          refine ⟨3754844897897217443374445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10012919727725913182331853 3754844897897217443374445)
          ·
            refine ⟨1408066836711456541265417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3754844897897217443374445 1408066836711456541265417)
            ·
              refine ⟨1056050127533592405949063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408066836711456541265417 1056050127533592405949063)
              ·
                refine ⟨1584075191300388608923595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056050127533592405949063 1584075191300388608923595)
                ·
                  refine ⟨2376112786950582913385393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584075191300388608923595 2376112786950582913385393)
                  ·
                    refine ⟨1782084590212937185039045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2376112786950582913385393 1782084590212937185039045)
                    ·
                      refine ⟨334140860664925722194821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1782084590212937185039045 334140860664925722194821)
                      ·
                        rfl

theorem cell23_650737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_650737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650737 prefixEnd_650737 := by exact prefixLift 650737
  have htrace : WordTrace (prefixWord ++ tailWord_650737) baseStart_650737 baseEnd_650737 := by
    simpa [prefixWord, tailWord_650737, baseEnd_650737] using wordTrace_append hprefix tailTrace_650737
  have hstable : (prefixWord ++ tailWord_650737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650737).length < 2 ^ (prefixWord ++ tailWord_650737).sum := by decide
  have hdescent : baseEnd_650737 < baseStart_650737 := by decide
  rcases family_descends (prefixWord ++ tailWord_650737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650741 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_650741 : Nat := 118140960795 + 650741 * 2 ^ 59
def prefixEnd_650741 : Nat := 4983230072969 + 3 ^ 40 * 650741 * 2
def baseEnd_650741 : Nat := 334142914587543706544803

theorem tailTrace_650741 : CollatzResearch.WordTrace tailWord_650741 prefixEnd_650741 334142914587543706544803 := by
  unfold tailWord_650741
  simp only [CollatzResearch.WordTrace]
  refine ⟨23734474135483969559784077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15822982756989313039856051 23734474135483969559784077)
  ·
    refine ⟨8900427800806488584919029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23734474135483969559784077 8900427800806488584919029)
    ·
      refine ⟨834415106325608304836159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8900427800806488584919029 834415106325608304836159)
      ·
        refine ⟨1251622659488412457254239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834415106325608304836159 1251622659488412457254239)
        ·
          refine ⟨1877433989232618685881359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251622659488412457254239 1877433989232618685881359)
          ·
            refine ⟨2816150983848928028822039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877433989232618685881359 2816150983848928028822039)
            ·
              refine ⟨4224226475773392043233059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816150983848928028822039 4224226475773392043233059)
              ·
                refine ⟨6336339713660088064849589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224226475773392043233059 6336339713660088064849589)
                ·
                  refine ⟨594031848155633256079649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6336339713660088064849589 594031848155633256079649)
                  ·
                    refine ⟨445523886116724942059737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 594031848155633256079649 445523886116724942059737)
                    ·
                      refine ⟨334142914587543706544803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 445523886116724942059737 334142914587543706544803)
                      ·
                        rfl

theorem cell23_650741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_650741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650741 prefixEnd_650741 := by exact prefixLift 650741
  have htrace : WordTrace (prefixWord ++ tailWord_650741) baseStart_650741 baseEnd_650741 := by
    simpa [prefixWord, tailWord_650741, baseEnd_650741] using wordTrace_append hprefix tailTrace_650741
  have hstable : (prefixWord ++ tailWord_650741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650741).length < 2 ^ (prefixWord ++ tailWord_650741).sum := by decide
  have hdescent : baseEnd_650741 < baseStart_650741 := by decide
  rcases family_descends (prefixWord ++ tailWord_650741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650754 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_650754 : Nat := 118140960795 + 650754 * 2 ^ 59
def prefixEnd_650754 : Nat := 4983230072969 + 3 ^ 40 * 650754 * 2
def baseEnd_650754 : Nat := 334149589836052155682243

theorem tailTrace_650754 : CollatzResearch.WordTrace tailWord_650754 prefixEnd_650754 334149589836052155682243 := by
  unfold tailWord_650754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933737071109218195001829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15823298856291248520004877 5933737071109218195001829)
  ·
    refine ⟨1112575700832978411562843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5933737071109218195001829 1112575700832978411562843)
    ·
      refine ⟨1668863551249467617344265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112575700832978411562843 1668863551249467617344265)
      ·
        refine ⟨1251647663437100713008199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1668863551249467617344265 1251647663437100713008199)
        ·
          refine ⟨1877471495155651069512299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251647663437100713008199 1877471495155651069512299)
          ·
            refine ⟨2816207242733476604268449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877471495155651069512299 2816207242733476604268449)
            ·
              refine ⟨2112155432050107453201337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2816207242733476604268449 2112155432050107453201337)
              ·
                refine ⟨1584116574037580589901003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112155432050107453201337 1584116574037580589901003)
                ·
                  refine ⟨2376174861056370884851505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584116574037580589901003 2376174861056370884851505)
                  ·
                    refine ⟨1782131145792278163638629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2376174861056370884851505 1782131145792278163638629)
                    ·
                      refine ⟨334149589836052155682243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1782131145792278163638629 334149589836052155682243)
                      ·
                        rfl

theorem cell23_650754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_650754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650754 prefixEnd_650754 := by exact prefixLift 650754
  have htrace : WordTrace (prefixWord ++ tailWord_650754) baseStart_650754 baseEnd_650754 := by
    simpa [prefixWord, tailWord_650754, baseEnd_650754] using wordTrace_append hprefix tailTrace_650754
  have hstable : (prefixWord ++ tailWord_650754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650754).length < 2 ^ (prefixWord ++ tailWord_650754).sum := by decide
  have hdescent : baseEnd_650754 < baseStart_650754 := by decide
  rcases family_descends (prefixWord ++ tailWord_650754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650757 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_650757 : Nat := 118140960795 + 650757 * 2 ^ 59
def prefixEnd_650757 : Nat := 4983230072969 + 3 ^ 40 * 650757 * 2
def baseEnd_650757 : Nat := 334151130278015643944729

theorem tailTrace_650757 : CollatzResearch.WordTrace tailWord_650757 prefixEnd_650757 334151130278015643944729 := by
  unfold tailWord_650757
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735057703426004292366525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15823371802284002861577683 23735057703426004292366525)
  ·
    refine ⟨8900646638784751609637447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23735057703426004292366525 8900646638784751609637447)
    ·
      refine ⟨13350969958177127414456171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8900646638784751609637447 13350969958177127414456171)
      ·
        refine ⟨20026454937265691121684257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13350969958177127414456171 20026454937265691121684257)
        ·
          refine ⟨15019841202949268341263193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20026454937265691121684257 15019841202949268341263193)
          ·
            refine ⟨11264880902211951255947395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15019841202949268341263193 11264880902211951255947395)
            ·
              refine ⟨16897321353317926883921093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11264880902211951255947395 16897321353317926883921093)
              ·
                refine ⟨3168247753747111290735205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16897321353317926883921093 3168247753747111290735205)
                ·
                  refine ⟨594046453827583367012851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3168247753747111290735205 594046453827583367012851)
                  ·
                    refine ⟨891069680741375050519277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 594046453827583367012851 891069680741375050519277)
                    ·
                      refine ⟨334151130278015643944729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 891069680741375050519277 334151130278015643944729)
                      ·
                        rfl

theorem cell23_650757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_650757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_650757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_650757 prefixEnd_650757 := by exact prefixLift 650757
  have htrace : WordTrace (prefixWord ++ tailWord_650757) baseStart_650757 baseEnd_650757 := by
    simpa [prefixWord, tailWord_650757, baseEnd_650757] using wordTrace_append hprefix tailTrace_650757
  have hstable : (prefixWord ++ tailWord_650757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650757).length < 2 ^ (prefixWord ++ tailWord_650757).sum := by decide
  have hdescent : baseEnd_650757 < baseStart_650757 := by decide
  rcases family_descends (prefixWord ++ tailWord_650757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
