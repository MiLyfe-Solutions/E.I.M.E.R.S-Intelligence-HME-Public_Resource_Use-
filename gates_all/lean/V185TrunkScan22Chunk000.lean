import V185TrunkScan21Incremental

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_14 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_14 : Nat := 118140960795 + 14 * 2 ^ 59
def prefixEnd_14 : Nat := 4983230072969 + 3 ^ 40 * 14 * 2
def baseEnd_14 : Nat := 1597495392928649987

theorem tailTrace_14 : CollatzResearch.WordTrace tailWord_14 prefixEnd_14 1597495392928649987 := by
  unfold tailWord_14
  simp only [CollatzResearch.WordTrace]
  refine ⟨63827744594404514887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 340414637836824079397 63827744594404514887)
  ·
    refine ⟨95741616891606772331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63827744594404514887 95741616891606772331)
    ·
      refine ⟨143612425337410158497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95741616891606772331 143612425337410158497)
      ·
        refine ⟨107709319003057618873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143612425337410158497 107709319003057618873)
        ·
          refine ⟨80781989252293214155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107709319003057618873 80781989252293214155)
          ·
            refine ⟨121172983878439821233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80781989252293214155 121172983878439821233)
            ·
              refine ⟨90879737908829865925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121172983878439821233 90879737908829865925)
              ·
                refine ⟨17039950857905599861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90879737908829865925 17039950857905599861)
                ·
                  refine ⟨1597495392928649987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17039950857905599861 1597495392928649987)
                  ·
                    rfl

theorem cell22_14_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_14 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14 prefixEnd_14 := by exact prefixLift 14
  have htrace : WordTrace (prefixWord ++ tailWord_14) baseStart_14 baseEnd_14 := by
    simpa [prefixWord, tailWord_14, baseEnd_14] using wordTrace_append hprefix tailTrace_14
  have hstable : (prefixWord ++ tailWord_14).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14).length < 2 ^ (prefixWord ++ tailWord_14).sum := by decide
  have hdescent : baseEnd_14 < baseStart_14 := by decide
  rcases family_descends (prefixWord ++ tailWord_14) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_44 : Nat := 118140960795 + 44 * 2 ^ 59
def prefixEnd_44 : Nat := 4983230072969 + 3 ^ 40 * 44 * 2
def baseEnd_44 : Nat := 15062099268707699869

theorem tailTrace_44 : CollatzResearch.WordTrace tailWord_44 prefixEnd_44 15062099268707699869 := by
  unfold tailWord_44
  simp only [CollatzResearch.WordTrace]
  refine ⟨802405924035179855593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1069874565380239807457 802405924035179855593)
  ·
    refine ⟨601804443026384891695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 802405924035179855593 601804443026384891695)
    ·
      refine ⟨902706664539577337543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601804443026384891695 902706664539577337543)
      ·
        refine ⟨1354059996809366006315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902706664539577337543 1354059996809366006315)
        ·
          refine ⟨2031089995214049009473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354059996809366006315 2031089995214049009473)
          ·
            refine ⟨1523317496410536757105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2031089995214049009473 1523317496410536757105)
            ·
              refine ⟨1142488122307902567829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523317496410536757105 1142488122307902567829)
              ·
                refine ⟨53554130733182932867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1142488122307902567829 53554130733182932867)
                ·
                  refine ⟨80331196099774399301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53554130733182932867 80331196099774399301)
                  ·
                    refine ⟨15062099268707699869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80331196099774399301 15062099268707699869)
                    ·
                      rfl

theorem cell22_44_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_44 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44 prefixEnd_44 := by exact prefixLift 44
  have htrace : WordTrace (prefixWord ++ tailWord_44) baseStart_44 baseEnd_44 := by
    simpa [prefixWord, tailWord_44, baseEnd_44] using wordTrace_append hprefix tailTrace_44
  have hstable : (prefixWord ++ tailWord_44).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44).length < 2 ^ (prefixWord ++ tailWord_44).sum := by decide
  have hdescent : baseEnd_44 < baseStart_44 := by decide
  rcases family_descends (prefixWord ++ tailWord_44) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_106 : Nat := 118140960795 + 106 * 2 ^ 59
def prefixEnd_106 : Nat := 4983230072969 + 3 ^ 40 * 106 * 2
def baseEnd_106 : Nat := 36285966321212649679

theorem tailTrace_106 : CollatzResearch.WordTrace tailWord_106 prefixEnd_106 36285966321212649679 := by
  unfold tailWord_106
  simp only [CollatzResearch.WordTrace]
  refine ⟨966534405863737117043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2577425082303298978781 966534405863737117043)
  ·
    refine ⟨1449801608795605675565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 966534405863737117043 1449801608795605675565)
    ·
      refine ⟨543675603298352128337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1449801608795605675565 543675603298352128337)
      ·
        refine ⟨407756702473764096253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543675603298352128337 407756702473764096253)
        ·
          refine ⟨152908763427661536095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407756702473764096253 152908763427661536095)
          ·
            refine ⟨229363145141492304143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152908763427661536095 229363145141492304143)
            ·
              refine ⟨344044717712238456215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229363145141492304143 344044717712238456215)
              ·
                refine ⟨516067076568357684323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344044717712238456215 516067076568357684323)
                ·
                  refine ⟨774100614852536526485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516067076568357684323 774100614852536526485)
                  ·
                    refine ⟨36285966321212649679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 774100614852536526485 36285966321212649679)
                    ·
                      rfl

theorem cell22_106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106 prefixEnd_106 := by exact prefixLift 106
  have htrace : WordTrace (prefixWord ++ tailWord_106) baseStart_106 baseEnd_106 := by
    simpa [prefixWord, tailWord_106, baseEnd_106] using wordTrace_append hprefix tailTrace_106
  have hstable : (prefixWord ++ tailWord_106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106).length < 2 ^ (prefixWord ++ tailWord_106).sum := by decide
  have hdescent : baseEnd_106 < baseStart_106 := by decide
  rcases family_descends (prefixWord ++ tailWord_106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 5, 4]
def baseStart_179 : Nat := 118140960795 + 179 * 2 ^ 59
def prefixEnd_179 : Nat := 4983230072969 + 3 ^ 40 * 179 * 2
def baseEnd_179 : Nat := 61275358173355574455

theorem tailTrace_179 : CollatzResearch.WordTrace tailWord_179 prefixEnd_179 61275358173355574455 := by
  unfold tailWord_179
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528666358988415875591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4352444239325610583727 6528666358988415875591)
  ·
    refine ⟨9792999538482623813387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6528666358988415875591 9792999538482623813387)
    ·
      refine ⟨14689499307723935720081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792999538482623813387 14689499307723935720081)
      ·
        refine ⟨11017124480792951790061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14689499307723935720081 11017124480792951790061)
        ·
          refine ⟨4131421680297356921273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11017124480792951790061 4131421680297356921273)
          ·
            refine ⟨3098566260223017690955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4131421680297356921273 3098566260223017690955)
            ·
              refine ⟨4647849390334526536433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098566260223017690955 4647849390334526536433)
              ·
                refine ⟨3485887042750894902325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647849390334526536433 3485887042750894902325)
                ·
                  refine ⟨326801910257896397093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3485887042750894902325 326801910257896397093)
                  ·
                    refine ⟨61275358173355574455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326801910257896397093 61275358173355574455)
                    ·
                      rfl

theorem cell22_179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179 prefixEnd_179 := by exact prefixLift 179
  have htrace : WordTrace (prefixWord ++ tailWord_179) baseStart_179 baseEnd_179 := by
    simpa [prefixWord, tailWord_179, baseEnd_179] using wordTrace_append hprefix tailTrace_179
  have hstable : (prefixWord ++ tailWord_179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179).length < 2 ^ (prefixWord ++ tailWord_179).sum := by decide
  have hdescent : baseEnd_179 < baseStart_179 := by decide
  rcases family_descends (prefixWord ++ tailWord_179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_213 : Nat := 118140960795 + 213 * 2 ^ 59
def prefixEnd_213 : Nat := 4983230072969 + 3 ^ 40 * 213 * 2
def baseEnd_213 : Nat := 72914253008600224351

theorem tailTrace_213 : CollatzResearch.WordTrace tailWord_213 prefixEnd_213 72914253008600224351 := by
  unfold tailWord_213
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768748235812222613293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5179165490541481742195 7768748235812222613293)
  ·
    refine ⟨2913280588429583479985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7768748235812222613293 2913280588429583479985)
    ·
      refine ⟨2184960441322187609989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2913280588429583479985 2184960441322187609989)
      ·
        refine ⟨409680082747910176873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2184960441322187609989 409680082747910176873)
        ·
          refine ⟨307260062060932632655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409680082747910176873 307260062060932632655)
          ·
            refine ⟨460890093091398948983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307260062060932632655 460890093091398948983)
            ·
              refine ⟨691335139637098423475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460890093091398948983 691335139637098423475)
              ·
                refine ⟨1037002709455647635213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691335139637098423475 1037002709455647635213)
                ·
                  refine ⟨388876016045867863205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037002709455647635213 388876016045867863205)
                  ·
                    refine ⟨72914253008600224351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 388876016045867863205 72914253008600224351)
                    ·
                      rfl

theorem cell22_213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_213 prefixEnd_213 := by exact prefixLift 213
  have htrace : WordTrace (prefixWord ++ tailWord_213) baseStart_213 baseEnd_213 := by
    simpa [prefixWord, tailWord_213, baseEnd_213] using wordTrace_append hprefix tailTrace_213
  have hstable : (prefixWord ++ tailWord_213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213).length < 2 ^ (prefixWord ++ tailWord_213).sum := by decide
  have hdescent : baseEnd_213 < baseStart_213 := by decide
  rcases family_descends (prefixWord ++ tailWord_213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239 : List Nat := [1, 1, 2, 1, 6, 11]
def baseStart_239 : Nat := 118140960795 + 239 * 2 ^ 59
def prefixEnd_239 : Nat := 4983230072969 + 3 ^ 40 * 239 * 2
def baseEnd_239 : Nat := 1010056596953074991

theorem tailTrace_239 : CollatzResearch.WordTrace tailWord_239 prefixEnd_239 1010056596953074991 := by
  unfold tailWord_239
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717046141618663059771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5811364094412442039847 8717046141618663059771)
  ·
    refine ⟨13075569212427994589657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717046141618663059771 13075569212427994589657)
    ·
      refine ⟨9806676909320995942243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13075569212427994589657 9806676909320995942243)
      ·
        refine ⟨14710015363981493913365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9806676909320995942243 14710015363981493913365)
        ·
          refine ⟨689531970186632527189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14710015363981493913365 689531970186632527189)
          ·
            refine ⟨1010056596953074991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 689531970186632527189 1010056596953074991)
            ·
              rfl

theorem cell22_239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 11].length) (baseStart_239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239 prefixEnd_239 := by exact prefixLift 239
  have htrace : WordTrace (prefixWord ++ tailWord_239) baseStart_239 baseEnd_239 := by
    simpa [prefixWord, tailWord_239, baseEnd_239] using wordTrace_append hprefix tailTrace_239
  have hstable : (prefixWord ++ tailWord_239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239).length < 2 ^ (prefixWord ++ tailWord_239).sum := by decide
  have hdescent : baseEnd_239 < baseStart_239 := by decide
  rcases family_descends (prefixWord ++ tailWord_239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_241 : Nat := 118140960795 + 241 * 2 ^ 59
def prefixEnd_241 : Nat := 4983230072969 + 3 ^ 40 * 241 * 2
def baseEnd_241 : Nat := 82499225225860524265

theorem tailTrace_241 : CollatzResearch.WordTrace tailWord_241 prefixEnd_241 82499225225860524265 := by
  unfold tailWord_241
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789992134373004632577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5859994756248669755051 8789992134373004632577)
  ·
    refine ⟨6592494100779753474433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8789992134373004632577 6592494100779753474433)
    ·
      refine ⟨4944370575584815105825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6592494100779753474433 4944370575584815105825)
      ·
        refine ⟨3708277931688611329369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4944370575584815105825 3708277931688611329369)
        ·
          refine ⟨2781208448766458497027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3708277931688611329369 2781208448766458497027)
          ·
            refine ⟨4171812673149687745541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781208448766458497027 4171812673149687745541)
            ·
              refine ⟨782214876215566452289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4171812673149687745541 782214876215566452289)
              ·
                refine ⟨586661157161674839217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782214876215566452289 586661157161674839217)
                ·
                  refine ⟨439995867871256129413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586661157161674839217 439995867871256129413)
                  ·
                    refine ⟨82499225225860524265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439995867871256129413 82499225225860524265)
                    ·
                      rfl

theorem cell22_241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241 prefixEnd_241 := by exact prefixLift 241
  have htrace : WordTrace (prefixWord ++ tailWord_241) baseStart_241 baseEnd_241 := by
    simpa [prefixWord, tailWord_241, baseEnd_241] using wordTrace_append hprefix tailTrace_241
  have hstable : (prefixWord ++ tailWord_241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241).length < 2 ^ (prefixWord ++ tailWord_241).sum := by decide
  have hdescent : baseEnd_241 < baseStart_241 := by decide
  rcases family_descends (prefixWord ++ tailWord_241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 2, 3]
def baseStart_243 : Nat := 118140960795 + 243 * 2 ^ 59
def prefixEnd_243 : Nat := 4983230072969 + 3 ^ 40 * 243 * 2
def baseEnd_243 : Nat := 83183866098521974259

theorem tailTrace_243 : CollatzResearch.WordTrace tailWord_243 prefixEnd_243 83183866098521974259 := by
  unfold tailWord_243
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862938127127346205383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5908625418084897470255 8862938127127346205383)
  ·
    refine ⟨13294407190691019308075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8862938127127346205383 13294407190691019308075)
    ·
      refine ⟨19941610786036528962113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13294407190691019308075 19941610786036528962113)
      ·
        refine ⟨14956208089527396721585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19941610786036528962113 14956208089527396721585)
        ·
          refine ⟨11217156067145547541189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14956208089527396721585 11217156067145547541189)
          ·
            refine ⟨2103216762589790163973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11217156067145547541189 2103216762589790163973)
            ·
              refine ⟨394353142985585655745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2103216762589790163973 394353142985585655745)
              ·
                refine ⟨295764857239189241809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394353142985585655745 295764857239189241809)
                ·
                  refine ⟨221823642929391931357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295764857239189241809 221823642929391931357)
                  ·
                    refine ⟨83183866098521974259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221823642929391931357 83183866098521974259)
                    ·
                      rfl

theorem cell22_243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 3].length) (baseStart_243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243 prefixEnd_243 := by exact prefixLift 243
  have htrace : WordTrace (prefixWord ++ tailWord_243) baseStart_243 baseEnd_243 := by
    simpa [prefixWord, tailWord_243, baseEnd_243] using wordTrace_append hprefix tailTrace_243
  have hstable : (prefixWord ++ tailWord_243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243).length < 2 ^ (prefixWord ++ tailWord_243).sum := by decide
  have hdescent : baseEnd_243 < baseStart_243 := by decide
  rcases family_descends (prefixWord ++ tailWord_243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 3, 3]
def baseStart_305 : Nat := 118140960795 + 305 * 2 ^ 59
def prefixEnd_305 : Nat := 4983230072969 + 3 ^ 40 * 305 * 2
def baseEnd_305 : Nat := 104407733151026924069

theorem tailTrace_305 : CollatzResearch.WordTrace tailWord_305 prefixEnd_305 104407733151026924069 := by
  unfold tailWord_305
  simp only [CollatzResearch.WordTrace]
  refine ⟨11124263902511934962369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7416175935007956641579 11124263902511934962369)
  ·
    refine ⟨8343197926883951221777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11124263902511934962369 8343197926883951221777)
    ·
      refine ⟨6257398445162963416333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8343197926883951221777 6257398445162963416333)
      ·
        refine ⟨2346524416936111281125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6257398445162963416333 2346524416936111281125)
        ·
          refine ⟨439973328175520865211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2346524416936111281125 439973328175520865211)
          ·
            refine ⟨659959992263281297817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439973328175520865211 659959992263281297817)
            ·
              refine ⟨494969994197460973363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659959992263281297817 494969994197460973363)
              ·
                refine ⟨742454991296191460045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494969994197460973363 742454991296191460045)
                ·
                  refine ⟨278420621736071797517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742454991296191460045 278420621736071797517)
                  ·
                    refine ⟨104407733151026924069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278420621736071797517 104407733151026924069)
                    ·
                      rfl

theorem cell22_305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305 prefixEnd_305 := by exact prefixLift 305
  have htrace : WordTrace (prefixWord ++ tailWord_305) baseStart_305 baseEnd_305 := by
    simpa [prefixWord, tailWord_305, baseEnd_305] using wordTrace_append hprefix tailTrace_305
  have hstable : (prefixWord ++ tailWord_305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305).length < 2 ^ (prefixWord ++ tailWord_305).sum := by decide
  have hdescent : baseEnd_305 < baseStart_305 := by decide
  rcases family_descends (prefixWord ++ tailWord_305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_316 : Nat := 118140960795 + 316 * 2 ^ 59
def prefixEnd_316 : Nat := 4983230072969 + 3 ^ 40 * 316 * 2
def baseEnd_316 : Nat := 108173257950664899035

theorem tailTrace_316 : CollatzResearch.WordTrace tailWord_316 prefixEnd_316 108173257950664899035 := by
  unfold tailWord_316
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762733431330406806401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7683644575107209075201 5762733431330406806401)
  ·
    refine ⟨4322050073497805104801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5762733431330406806401 4322050073497805104801)
    ·
      refine ⟨3241537555123353828601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4322050073497805104801 3241537555123353828601)
      ·
        refine ⟨2431153166342515371451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3241537555123353828601 2431153166342515371451)
        ·
          refine ⟨3646729749513773057177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431153166342515371451 3646729749513773057177)
          ·
            refine ⟨2735047312135329792883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3646729749513773057177 2735047312135329792883)
            ·
              refine ⟨4102570968202994689325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735047312135329792883 4102570968202994689325)
              ·
                refine ⟨1538464113076123008497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4102570968202994689325 1538464113076123008497)
                ·
                  refine ⟨1153848084807092256373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538464113076123008497 1153848084807092256373)
                  ·
                    refine ⟨108173257950664899035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1153848084807092256373 108173257950664899035)
                    ·
                      rfl

theorem cell22_316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316 prefixEnd_316 := by exact prefixLift 316
  have htrace : WordTrace (prefixWord ++ tailWord_316) baseStart_316 baseEnd_316 := by
    simpa [prefixWord, tailWord_316, baseEnd_316] using wordTrace_append hprefix tailTrace_316
  have hstable : (prefixWord ++ tailWord_316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316).length < 2 ^ (prefixWord ++ tailWord_316).sum := by decide
  have hdescent : baseEnd_316 < baseStart_316 := by decide
  rcases family_descends (prefixWord ++ tailWord_316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391 : List Nat := [1, 1, 4, 2, 2, 1, 1, 10]
def baseStart_391 : Nat := 118140960795 + 391 * 2 ^ 59
def prefixEnd_391 : Nat := 4983230072969 + 3 ^ 40 * 391 * 2
def baseEnd_391 : Nat := 14871921186163252645

theorem tailTrace_391 : CollatzResearch.WordTrace tailWord_391 prefixEnd_391 14871921186163252645 := by
  unfold tailWord_391
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260941590948622593027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9507294393965748395351 14260941590948622593027)
  ·
    refine ⟨21391412386422933889541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14260941590948622593027 21391412386422933889541)
    ·
      refine ⟨4010889822454300104289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21391412386422933889541 4010889822454300104289)
      ·
        refine ⟨3008167366840725078217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4010889822454300104289 3008167366840725078217)
        ·
          refine ⟨2256125525130543808663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008167366840725078217 2256125525130543808663)
          ·
            refine ⟨3384188287695815712995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256125525130543808663 3384188287695815712995)
            ·
              refine ⟨5076282431543723569493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384188287695815712995 5076282431543723569493)
              ·
                refine ⟨14871921186163252645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5076282431543723569493 14871921186163252645)
                ·
                  rfl

theorem cell22_391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 10].length) (baseStart_391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391 prefixEnd_391 := by exact prefixLift 391
  have htrace : WordTrace (prefixWord ++ tailWord_391) baseStart_391 baseEnd_391 := by
    simpa [prefixWord, tailWord_391, baseEnd_391] using wordTrace_append hprefix tailTrace_391
  have hstable : (prefixWord ++ tailWord_391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391).length < 2 ^ (prefixWord ++ tailWord_391).sum := by decide
  have hdescent : baseEnd_391 < baseStart_391 := by decide
  rcases family_descends (prefixWord ++ tailWord_391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_393 : Nat := 118140960795 + 393 * 2 ^ 59
def prefixEnd_393 : Nat := 4983230072969 + 3 ^ 40 * 393 * 2
def baseEnd_393 : Nat := 134531931548130723799

theorem tailTrace_393 : CollatzResearch.WordTrace tailWord_393 prefixEnd_393 134531931548130723799 := by
  unfold tailWord_393
  simp only [CollatzResearch.WordTrace]
  refine ⟨14333887583702964165833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9555925055801976110555 14333887583702964165833)
  ·
    refine ⟨10750415687777223124375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14333887583702964165833 10750415687777223124375)
    ·
      refine ⟨16125623531665834686563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750415687777223124375 16125623531665834686563)
      ·
        refine ⟨24188435297498752029845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16125623531665834686563 24188435297498752029845)
        ·
          refine ⟨1133832904570254001399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24188435297498752029845 1133832904570254001399)
          ·
            refine ⟨1700749356855381002099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133832904570254001399 1700749356855381002099)
            ·
              refine ⟨2551124035283071503149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700749356855381002099 2551124035283071503149)
              ·
                refine ⟨956671513231151813681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2551124035283071503149 956671513231151813681)
                ·
                  refine ⟨717503634923363860261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956671513231151813681 717503634923363860261)
                  ·
                    refine ⟨134531931548130723799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717503634923363860261 134531931548130723799)
                    ·
                      rfl

theorem cell22_393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393 prefixEnd_393 := by exact prefixLift 393
  have htrace : WordTrace (prefixWord ++ tailWord_393) baseStart_393 baseEnd_393 := by
    simpa [prefixWord, tailWord_393, baseEnd_393] using wordTrace_append hprefix tailTrace_393
  have hstable : (prefixWord ++ tailWord_393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393).length < 2 ^ (prefixWord ++ tailWord_393).sum := by decide
  have hdescent : baseEnd_393 < baseStart_393 := by decide
  rcases family_descends (prefixWord ++ tailWord_393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414 : List Nat := [4, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_414 : Nat := 118140960795 + 414 * 2 ^ 59
def prefixEnd_414 : Nat := 4983230072969 + 3 ^ 40 * 414 * 2
def baseEnd_414 : Nat := 47240220237025316245

theorem tailTrace_414 : CollatzResearch.WordTrace tailWord_414 prefixEnd_414 47240220237025316245 := by
  unfold tailWord_414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887477563452943835037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10066547005082367120197 1887477563452943835037)
  ·
    refine ⟨707804086294853938139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1887477563452943835037 707804086294853938139)
    ·
      refine ⟨1061706129442280907209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707804086294853938139 1061706129442280907209)
      ·
        refine ⟨796279597081710680407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061706129442280907209 796279597081710680407)
        ·
          refine ⟨1194419395622566020611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796279597081710680407 1194419395622566020611)
          ·
            refine ⟨1791629093433849030917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194419395622566020611 1791629093433849030917)
            ·
              refine ⟨335930455018846693297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1791629093433849030917 335930455018846693297)
              ·
                refine ⟨251947841264135019973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335930455018846693297 251947841264135019973)
                ·
                  refine ⟨47240220237025316245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251947841264135019973 47240220237025316245)
                  ·
                    rfl

theorem cell22_414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414 prefixEnd_414 := by exact prefixLift 414
  have htrace : WordTrace (prefixWord ++ tailWord_414) baseStart_414 baseEnd_414 := by
    simpa [prefixWord, tailWord_414, baseEnd_414] using wordTrace_append hprefix tailTrace_414
  have hstable : (prefixWord ++ tailWord_414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414).length < 2 ^ (prefixWord ++ tailWord_414).sum := by decide
  have hdescent : baseEnd_414 < baseStart_414 := by decide
  rcases family_descends (prefixWord ++ tailWord_414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_421 : Nat := 118140960795 + 421 * 2 ^ 59
def prefixEnd_421 : Nat := 4983230072969 + 3 ^ 40 * 421 * 2
def baseEnd_421 : Nat := 144116903765391023713

theorem tailTrace_421 : CollatzResearch.WordTrace tailWord_421 prefixEnd_421 144116903765391023713 := by
  unfold tailWord_421
  simp only [CollatzResearch.WordTrace]
  refine ⟨15355131482263746185117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10236754321509164123411 15355131482263746185117)
  ·
    refine ⟨5758174305848904819419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15355131482263746185117 5758174305848904819419)
    ·
      refine ⟨8637261458773357229129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5758174305848904819419 8637261458773357229129)
      ·
        refine ⟨6477946094080017921847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8637261458773357229129 6477946094080017921847)
        ·
          refine ⟨9716919141120026882771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477946094080017921847 9716919141120026882771)
          ·
            refine ⟨14575378711680040324157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716919141120026882771 14575378711680040324157)
            ·
              refine ⟨5465767016880015121559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14575378711680040324157 5465767016880015121559)
              ·
                refine ⟨8198650525320022682339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465767016880015121559 8198650525320022682339)
                ·
                  refine ⟨12297975787980034023509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8198650525320022682339 12297975787980034023509)
                  ·
                    refine ⟨144116903765391023713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12297975787980034023509 144116903765391023713)
                    ·
                      rfl

theorem cell22_421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421 prefixEnd_421 := by exact prefixLift 421
  have htrace : WordTrace (prefixWord ++ tailWord_421) baseStart_421 baseEnd_421 := by
    simpa [prefixWord, tailWord_421, baseEnd_421] using wordTrace_append hprefix tailTrace_421
  have hstable : (prefixWord ++ tailWord_421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421).length < 2 ^ (prefixWord ++ tailWord_421).sum := by decide
  have hdescent : baseEnd_421 < baseStart_421 := by decide
  rcases family_descends (prefixWord ++ tailWord_421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 3, 7]
def baseStart_451 : Nat := 118140960795 + 451 * 2 ^ 59
def prefixEnd_451 : Nat := 4983230072969 + 3 ^ 40 * 451 * 2
def baseEnd_451 : Nat := 154386516855312773621

theorem tailTrace_451 : CollatzResearch.WordTrace tailWord_451 prefixEnd_451 154386516855312773621 := by
  unfold tailWord_451
  simp only [CollatzResearch.WordTrace]
  refine ⟨16449321373578869777207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10966214249052579851471 16449321373578869777207)
  ·
    refine ⟨24673982060368304665811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16449321373578869777207 24673982060368304665811)
    ·
      refine ⟨37010973090552456998717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24673982060368304665811 37010973090552456998717)
      ·
        refine ⟨13879114908957171374519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37010973090552456998717 13879114908957171374519)
        ·
          refine ⟨20818672363435757061779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13879114908957171374519 20818672363435757061779)
          ·
            refine ⟨31228008545153635592669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20818672363435757061779 31228008545153635592669)
            ·
              refine ⟨11710503204432613347251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31228008545153635592669 11710503204432613347251)
              ·
                refine ⟨17565754806648920020877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11710503204432613347251 17565754806648920020877)
                ·
                  refine ⟨6587158052493345007829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17565754806648920020877 6587158052493345007829)
                  ·
                    refine ⟨154386516855312773621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6587158052493345007829 154386516855312773621)
                    ·
                      rfl

theorem cell22_451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451 prefixEnd_451 := by exact prefixLift 451
  have htrace : WordTrace (prefixWord ++ tailWord_451) baseStart_451 baseEnd_451 := by
    simpa [prefixWord, tailWord_451, baseEnd_451] using wordTrace_append hprefix tailTrace_451
  have hstable : (prefixWord ++ tailWord_451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451).length < 2 ^ (prefixWord ++ tailWord_451).sum := by decide
  have hdescent : baseEnd_451 < baseStart_451 := by decide
  rcases family_descends (prefixWord ++ tailWord_451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_470 : Nat := 118140960795 + 470 * 2 ^ 59
def prefixEnd_470 : Nat := 4983230072969 + 3 ^ 40 * 470 * 2
def baseEnd_470 : Nat := 53630201715198849521

theorem tailTrace_470 : CollatzResearch.WordTrace tailWord_470 prefixEnd_470 53630201715198849521 := by
  unfold tailWord_470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071394269046569669929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11428205536496743145909 1071394269046569669929)
  ·
    refine ⟨803545701784927252447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1071394269046569669929 803545701784927252447)
    ·
      refine ⟨1205318552677390878671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803545701784927252447 1205318552677390878671)
      ·
        refine ⟨1807977829016086318007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205318552677390878671 1807977829016086318007)
        ·
          refine ⟨2711966743524129477011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807977829016086318007 2711966743524129477011)
          ·
            refine ⟨4067950115286194215517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711966743524129477011 4067950115286194215517)
            ·
              refine ⟨1525481293232322830819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4067950115286194215517 1525481293232322830819)
              ·
                refine ⟨2288221939848484246229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525481293232322830819 2288221939848484246229)
                ·
                  refine ⟨53630201715198849521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2288221939848484246229 53630201715198849521)
                  ·
                    rfl

theorem cell22_470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470 prefixEnd_470 := by exact prefixLift 470
  have htrace : WordTrace (prefixWord ++ tailWord_470) baseStart_470 baseEnd_470 := by
    simpa [prefixWord, tailWord_470, baseEnd_470] using wordTrace_append hprefix tailTrace_470
  have hstable : (prefixWord ++ tailWord_470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470).length < 2 ^ (prefixWord ++ tailWord_470).sum := by decide
  have hdescent : baseEnd_470 < baseStart_470 := by decide
  rcases family_descends (prefixWord ++ tailWord_470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 6]
def baseStart_532 : Nat := 118140960795 + 532 * 2 ^ 59
def prefixEnd_532 : Nat := 4983230072969 + 3 ^ 40 * 532 * 2
def baseEnd_532 : Nat := 60704824066033832791

theorem tailTrace_532 : CollatzResearch.WordTrace tailWord_532 prefixEnd_532 60704824066033832791 := by
  unfold tailWord_532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9701817040064851737925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12935756053419802317233 9701817040064851737925)
  ·
    refine ⟨1819090695012159700861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9701817040064851737925 1819090695012159700861)
    ·
      refine ⟨682159010629559887823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1819090695012159700861 682159010629559887823)
      ·
        refine ⟨1023238515944339831735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682159010629559887823 1023238515944339831735)
        ·
          refine ⟨1534857773916509747603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023238515944339831735 1534857773916509747603)
          ·
            refine ⟨2302286660874764621405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534857773916509747603 2302286660874764621405)
            ·
              refine ⟨863357497828036733027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2302286660874764621405 863357497828036733027)
              ·
                refine ⟨1295036246742055099541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863357497828036733027 1295036246742055099541)
                ·
                  refine ⟨60704824066033832791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1295036246742055099541 60704824066033832791)
                  ·
                    rfl

theorem cell22_532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532 prefixEnd_532 := by exact prefixLift 532
  have htrace : WordTrace (prefixWord ++ tailWord_532) baseStart_532 baseEnd_532 := by
    simpa [prefixWord, tailWord_532, baseEnd_532] using wordTrace_append hprefix tailTrace_532
  have hstable : (prefixWord ++ tailWord_532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532).length < 2 ^ (prefixWord ++ tailWord_532).sum := by decide
  have hdescent : baseEnd_532 < baseStart_532 := by decide
  rcases family_descends (prefixWord ++ tailWord_532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 2, 3]
def baseStart_547 : Nat := 118140960795 + 547 * 2 ^ 59
def prefixEnd_547 : Nat := 4983230072969 + 3 ^ 40 * 547 * 2
def baseEnd_547 : Nat := 187249278743062373327

theorem tailTrace_547 : CollatzResearch.WordTrace tailWord_547 prefixEnd_547 187249278743062373327 := by
  unfold tailWord_547
  simp only [CollatzResearch.WordTrace]
  refine ⟨19950729025787265271895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13300486017191510181263 19950729025787265271895)
  ·
    refine ⟨29926093538680897907843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19950729025787265271895 29926093538680897907843)
    ·
      refine ⟨44889140308021346861765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29926093538680897907843 44889140308021346861765)
      ·
        refine ⟨8416713807754002536581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44889140308021346861765 8416713807754002536581)
        ·
          refine ⟨1578133838953875475609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8416713807754002536581 1578133838953875475609)
          ·
            refine ⟨1183600379215406606707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578133838953875475609 1183600379215406606707)
            ·
              refine ⟨1775400568823109910061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183600379215406606707 1775400568823109910061)
              ·
                refine ⟨665775213308666216273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775400568823109910061 665775213308666216273)
                ·
                  refine ⟨499331409981499662205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 665775213308666216273 499331409981499662205)
                  ·
                    refine ⟨187249278743062373327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 499331409981499662205 187249278743062373327)
                    ·
                      rfl

theorem cell22_547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 3].length) (baseStart_547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_547 prefixEnd_547 := by exact prefixLift 547
  have htrace : WordTrace (prefixWord ++ tailWord_547) baseStart_547 baseEnd_547 := by
    simpa [prefixWord, tailWord_547, baseEnd_547] using wordTrace_append hprefix tailTrace_547
  have hstable : (prefixWord ++ tailWord_547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547).length < 2 ^ (prefixWord ++ tailWord_547).sum := by decide
  have hdescent : baseEnd_547 < baseStart_547 := by decide
  rcases family_descends (prefixWord ++ tailWord_547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 1, 4]
def baseStart_551 : Nat := 118140960795 + 551 * 2 ^ 59
def prefixEnd_551 : Nat := 4983230072969 + 3 ^ 40 * 551 * 2
def baseEnd_551 : Nat := 188618560488385273315

theorem tailTrace_551 : CollatzResearch.WordTrace tailWord_551 prefixEnd_551 188618560488385273315 := by
  unfold tailWord_551
  simp only [CollatzResearch.WordTrace]
  refine ⟨20096621011295948417507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13397747340863965611671 20096621011295948417507)
  ·
    refine ⟨30144931516943922626261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20096621011295948417507 30144931516943922626261)
    ·
      refine ⟨706521832428373186553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30144931516943922626261 706521832428373186553)
      ·
        refine ⟨529891374321279889915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706521832428373186553 529891374321279889915)
        ·
          refine ⟨794837061481919834873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529891374321279889915 794837061481919834873)
          ·
            refine ⟨596127796111439876155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794837061481919834873 596127796111439876155)
            ·
              refine ⟨894191694167159814233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596127796111439876155 894191694167159814233)
              ·
                refine ⟨670643770625369860675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894191694167159814233 670643770625369860675)
                ·
                  refine ⟨1005965655938054791013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670643770625369860675 1005965655938054791013)
                  ·
                    refine ⟨188618560488385273315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005965655938054791013 188618560488385273315)
                    ·
                      rfl

theorem cell22_551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551 prefixEnd_551 := by exact prefixLift 551
  have htrace : WordTrace (prefixWord ++ tailWord_551) baseStart_551 baseEnd_551 := by
    simpa [prefixWord, tailWord_551, baseEnd_551] using wordTrace_append hprefix tailTrace_551
  have hstable : (prefixWord ++ tailWord_551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551).length < 2 ^ (prefixWord ++ tailWord_551).sum := by decide
  have hdescent : baseEnd_551 < baseStart_551 := by decide
  rcases family_descends (prefixWord ++ tailWord_551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_564 : Nat := 118140960795 + 564 * 2 ^ 59
def prefixEnd_564 : Nat := 4983230072969 + 3 ^ 40 * 564 * 2
def baseEnd_564 : Nat := 193068726160684698275

theorem tailTrace_564 : CollatzResearch.WordTrace tailWord_564 prefixEnd_564 193068726160684698275 := by
  unfold tailWord_564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10285384982099584320373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13713846642799445760497 10285384982099584320373)
  ·
    refine ⟨964254842071836030035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10285384982099584320373 964254842071836030035)
    ·
      refine ⟨1446382263107754045053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964254842071836030035 1446382263107754045053)
      ·
        refine ⟨542393348665407766895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1446382263107754045053 542393348665407766895)
        ·
          refine ⟨813590022998111650343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542393348665407766895 813590022998111650343)
          ·
            refine ⟨1220385034497167475515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813590022998111650343 1220385034497167475515)
            ·
              refine ⟨1830577551745751213273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220385034497167475515 1830577551745751213273)
              ·
                refine ⟨1372933163809313409955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830577551745751213273 1372933163809313409955)
                ·
                  refine ⟨2059399745713970114933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372933163809313409955 2059399745713970114933)
                  ·
                    refine ⟨193068726160684698275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2059399745713970114933 193068726160684698275)
                    ·
                      rfl

theorem cell22_564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_564 prefixEnd_564 := by exact prefixLift 564
  have htrace : WordTrace (prefixWord ++ tailWord_564) baseStart_564 baseEnd_564 := by
    simpa [prefixWord, tailWord_564, baseEnd_564] using wordTrace_append hprefix tailTrace_564
  have hstable : (prefixWord ++ tailWord_564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564).length < 2 ^ (prefixWord ++ tailWord_564).sum := by decide
  have hdescent : baseEnd_564 < baseStart_564 := by decide
  rcases family_descends (prefixWord ++ tailWord_564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626 : List Nat := [3, 2, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_626 : Nat := 118140960795 + 626 * 2 ^ 59
def prefixEnd_626 : Nat := 4983230072969 + 3 ^ 40 * 626 * 2
def baseEnd_626 : Nat := 214292593213189648085

theorem tailTrace_626 : CollatzResearch.WordTrace tailWord_626 prefixEnd_626 214292593213189648085 := by
  unfold tailWord_626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708023934895939349433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15221397159722504931821 5708023934895939349433)
  ·
    refine ⟨4281017951171954512075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5708023934895939349433 4281017951171954512075)
    ·
      refine ⟨6421526926757931768113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4281017951171954512075 6421526926757931768113)
      ·
        refine ⟨4816145195068448826085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6421526926757931768113 4816145195068448826085)
        ·
          refine ⟨903027224075334154891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4816145195068448826085 903027224075334154891)
          ·
            refine ⟨1354540836113001232337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903027224075334154891 1354540836113001232337)
            ·
              refine ⟨1015905627084750924253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354540836113001232337 1015905627084750924253)
              ·
                refine ⟨380964610156781596595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1015905627084750924253 380964610156781596595)
                ·
                  refine ⟨571446915235172394893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380964610156781596595 571446915235172394893)
                  ·
                    refine ⟨214292593213189648085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571446915235172394893 214292593213189648085)
                    ·
                      rfl

theorem cell22_626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626 prefixEnd_626 := by exact prefixLift 626
  have htrace : WordTrace (prefixWord ++ tailWord_626) baseStart_626 baseEnd_626 := by
    simpa [prefixWord, tailWord_626, baseEnd_626] using wordTrace_append hprefix tailTrace_626
  have hstable : (prefixWord ++ tailWord_626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626).length < 2 ^ (prefixWord ++ tailWord_626).sum := by decide
  have hdescent : baseEnd_626 < baseStart_626 := by decide
  rcases family_descends (prefixWord ++ tailWord_626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_716 : Nat := 118140960795 + 716 * 2 ^ 59
def prefixEnd_716 : Nat := 4983230072969 + 3 ^ 40 * 716 * 2
def baseEnd_716 : Nat := 245101432482954897809

theorem tailTrace_716 : CollatzResearch.WordTrace tailWord_716 prefixEnd_716 245101432482954897809 := by
  unfold tailWord_716
  simp only [CollatzResearch.WordTrace]
  refine ⟨13057332706764564087001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17409776942352752116001 13057332706764564087001)
  ·
    refine ⟨9792999530073423065251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13057332706764564087001 9792999530073423065251)
    ·
      refine ⟨14689499295110134597877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792999530073423065251 14689499295110134597877)
      ·
        refine ⟨1377140558916575118551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14689499295110134597877 1377140558916575118551)
        ·
          refine ⟨2065710838374862677827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377140558916575118551 2065710838374862677827)
          ·
            refine ⟨3098566257562294016741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065710838374862677827 3098566257562294016741)
            ·
              refine ⟨580981173292930128139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3098566257562294016741 580981173292930128139)
              ·
                refine ⟨871471759939395192209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580981173292930128139 871471759939395192209)
                ·
                  refine ⟨653603819954546394157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 871471759939395192209 653603819954546394157)
                  ·
                    refine ⟨245101432482954897809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653603819954546394157 245101432482954897809)
                    ·
                      rfl

theorem cell22_716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716 prefixEnd_716 := by exact prefixLift 716
  have htrace : WordTrace (prefixWord ++ tailWord_716) baseStart_716 baseEnd_716 := by
    simpa [prefixWord, tailWord_716, baseEnd_716] using wordTrace_append hprefix tailTrace_716
  have hstable : (prefixWord ++ tailWord_716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716).length < 2 ^ (prefixWord ++ tailWord_716).sum := by decide
  have hdescent : baseEnd_716 < baseStart_716 := by decide
  rcases family_descends (prefixWord ++ tailWord_716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 2, 5]
def baseStart_755 : Nat := 118140960795 + 755 * 2 ^ 59
def prefixEnd_755 : Nat := 4983230072969 + 3 ^ 40 * 755 * 2
def baseEnd_755 : Nat := 258451929499853172689

theorem tailTrace_755 : CollatzResearch.WordTrace tailWord_755 prefixEnd_755 258451929499853172689 := by
  unfold tailWord_755
  simp only [CollatzResearch.WordTrace]
  refine ⟨27537112272238788843719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18358074848159192562479 27537112272238788843719)
  ·
    refine ⟨41305668408358183265579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27537112272238788843719 41305668408358183265579)
    ·
      refine ⟨61958502612537274898369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41305668408358183265579 61958502612537274898369)
      ·
        refine ⟨46468876959402956173777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61958502612537274898369 46468876959402956173777)
        ·
          refine ⟨34851657719552217130333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46468876959402956173777 34851657719552217130333)
          ·
            refine ⟨13069371644832081423875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34851657719552217130333 13069371644832081423875)
            ·
              refine ⟨19604057467248122135813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13069371644832081423875 19604057467248122135813)
              ·
                refine ⟨3675760775109022900465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19604057467248122135813 3675760775109022900465)
                ·
                  refine ⟨2756820581331767175349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675760775109022900465 2756820581331767175349)
                  ·
                    refine ⟨258451929499853172689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2756820581331767175349 258451929499853172689)
                    ·
                      rfl

theorem cell22_755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755 prefixEnd_755 := by exact prefixLift 755
  have htrace : WordTrace (prefixWord ++ tailWord_755) baseStart_755 baseEnd_755 := by
    simpa [prefixWord, tailWord_755, baseEnd_755] using wordTrace_append hprefix tailTrace_755
  have hstable : (prefixWord ++ tailWord_755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755).length < 2 ^ (prefixWord ++ tailWord_755).sum := by decide
  have hdescent : baseEnd_755 < baseStart_755 := by decide
  rcases family_descends (prefixWord ++ tailWord_755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_772 : Nat := 118140960795 + 772 * 2 ^ 59
def prefixEnd_772 : Nat := 4983230072969 + 3 ^ 40 * 772 * 2
def baseEnd_772 : Nat := 264271376917475497637

theorem tailTrace_772 : CollatzResearch.WordTrace tailWord_772 prefixEnd_772 264271376917475497637 := by
  unfold tailWord_772
  simp only [CollatzResearch.WordTrace]
  refine ⟨14078576605325346106285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18771435473767128141713 14078576605325346106285)
  ·
    refine ⟨5279466226997004789857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14078576605325346106285 5279466226997004789857)
    ·
      refine ⟨3959599670247753592393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5279466226997004789857 3959599670247753592393)
      ·
        refine ⟨2969699752685815194295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3959599670247753592393 2969699752685815194295)
        ·
          refine ⟨4454549629028722791443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969699752685815194295 4454549629028722791443)
          ·
            refine ⟨6681824443543084187165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454549629028722791443 6681824443543084187165)
            ·
              refine ⟨2505684166328656570187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6681824443543084187165 2505684166328656570187)
              ·
                refine ⟨3758526249492984855281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505684166328656570187 3758526249492984855281)
                ·
                  refine ⟨2818894687119738641461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758526249492984855281 2818894687119738641461)
                  ·
                    refine ⟨264271376917475497637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2818894687119738641461 264271376917475497637)
                    ·
                      rfl

theorem cell22_772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_772 prefixEnd_772 := by exact prefixLift 772
  have htrace : WordTrace (prefixWord ++ tailWord_772) baseStart_772 baseEnd_772 := by
    simpa [prefixWord, tailWord_772, baseEnd_772] using wordTrace_append hprefix tailTrace_772
  have hstable : (prefixWord ++ tailWord_772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772).length < 2 ^ (prefixWord ++ tailWord_772).sum := by decide
  have hdescent : baseEnd_772 < baseStart_772 := by decide
  rcases family_descends (prefixWord ++ tailWord_772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 8]
def baseStart_785 : Nat := 118140960795 + 785 * 2 ^ 59
def prefixEnd_785 : Nat := 4983230072969 + 3 ^ 40 * 785 * 2
def baseEnd_785 : Nat := 89573847529924974199

theorem tailTrace_785 : CollatzResearch.WordTrace tailWord_785 prefixEnd_785 89573847529924974199 := by
  unfold tailWord_785
  simp only [CollatzResearch.WordTrace]
  refine ⟨28631302163553912435809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19087534775702608290539 28631302163553912435809)
  ·
    refine ⟨21473476622665434326857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28631302163553912435809 21473476622665434326857)
    ·
      refine ⟨16105107466999075745143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21473476622665434326857 16105107466999075745143)
      ·
        refine ⟨24157661200498613617715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16105107466999075745143 24157661200498613617715)
        ·
          refine ⟨36236491800747920426573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24157661200498613617715 36236491800747920426573)
          ·
            refine ⟨13588684425280470159965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36236491800747920426573 13588684425280470159965)
            ·
              refine ⟨5095756659480176309987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13588684425280470159965 5095756659480176309987)
              ·
                refine ⟨7643634989220264464981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095756659480176309987 7643634989220264464981)
                ·
                  refine ⟨89573847529924974199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7643634989220264464981 89573847529924974199)
                  ·
                    rfl

theorem cell22_785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785 prefixEnd_785 := by exact prefixLift 785
  have htrace : WordTrace (prefixWord ++ tailWord_785) baseStart_785 baseEnd_785 := by
    simpa [prefixWord, tailWord_785, baseEnd_785] using wordTrace_append hprefix tailTrace_785
  have hstable : (prefixWord ++ tailWord_785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785).length < 2 ^ (prefixWord ++ tailWord_785).sum := by decide
  have hdescent : baseEnd_785 < baseStart_785 := by decide
  rcases family_descends (prefixWord ++ tailWord_785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 1, 4]
def baseStart_787 : Nat := 118140960795 + 787 * 2 ^ 59
def prefixEnd_787 : Nat := 4983230072969 + 3 ^ 40 * 787 * 2
def baseEnd_787 : Nat := 269406183462436372591

theorem tailTrace_787 : CollatzResearch.WordTrace tailWord_787 prefixEnd_787 269406183462436372591 := by
  unfold tailWord_787
  simp only [CollatzResearch.WordTrace]
  refine ⟨28704248156308254008615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19136165437538836005743 28704248156308254008615)
  ·
    refine ⟨43056372234462381012923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28704248156308254008615 43056372234462381012923)
    ·
      refine ⟨64584558351693571519385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43056372234462381012923 64584558351693571519385)
      ·
        refine ⟨48438418763770178639539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64584558351693571519385 48438418763770178639539)
        ·
          refine ⟨72657628145655267959309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48438418763770178639539 72657628145655267959309)
          ·
            refine ⟨27246610554620725484741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72657628145655267959309 27246610554620725484741)
            ·
              refine ⟨5108739478991386028389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27246610554620725484741 5108739478991386028389)
              ·
                refine ⟨957888652310884880323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5108739478991386028389 957888652310884880323)
                ·
                  refine ⟨1436832978466327320485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957888652310884880323 1436832978466327320485)
                  ·
                    refine ⟨269406183462436372591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1436832978466327320485 269406183462436372591)
                    ·
                      rfl

theorem cell22_787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 4].length) (baseStart_787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787 prefixEnd_787 := by exact prefixLift 787
  have htrace : WordTrace (prefixWord ++ tailWord_787) baseStart_787 baseEnd_787 := by
    simpa [prefixWord, tailWord_787, baseEnd_787] using wordTrace_append hprefix tailTrace_787
  have hstable : (prefixWord ++ tailWord_787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787).length < 2 ^ (prefixWord ++ tailWord_787).sum := by decide
  have hdescent : baseEnd_787 < baseStart_787 := by decide
  rcases family_descends (prefixWord ++ tailWord_787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 5, 6]
def baseStart_815 : Nat := 118140960795 + 815 * 2 ^ 59
def prefixEnd_815 : Nat := 4983230072969 + 3 ^ 40 * 815 * 2
def baseEnd_815 : Nat := 278991155679696672505

theorem tailTrace_815 : CollatzResearch.WordTrace tailWord_815 prefixEnd_815 278991155679696672505 := by
  unfold tailWord_815
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725492054869036027899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19816994703246024018599 29725492054869036027899)
  ·
    refine ⟨44588238082303554041849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29725492054869036027899 44588238082303554041849)
    ·
      refine ⟨33441178561727665531387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44588238082303554041849 33441178561727665531387)
      ·
        refine ⟨50161767842591498297081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33441178561727665531387 50161767842591498297081)
        ·
          refine ⟨37621325881943623722811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50161767842591498297081 37621325881943623722811)
          ·
            refine ⟨56431988822915435584217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37621325881943623722811 56431988822915435584217)
            ·
              refine ⟨42323991617186576688163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56431988822915435584217 42323991617186576688163)
              ·
                refine ⟨63485987425779865032245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42323991617186576688163 63485987425779865032245)
                ·
                  refine ⟨5951811321166862346773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63485987425779865032245 5951811321166862346773)
                  ·
                    refine ⟨278991155679696672505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5951811321166862346773 278991155679696672505)
                    ·
                      rfl

theorem cell22_815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815 prefixEnd_815 := by exact prefixLift 815
  have htrace : WordTrace (prefixWord ++ tailWord_815) baseStart_815 baseEnd_815 := by
    simpa [prefixWord, tailWord_815, baseEnd_815] using wordTrace_append hprefix tailTrace_815
  have hstable : (prefixWord ++ tailWord_815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815).length < 2 ^ (prefixWord ++ tailWord_815).sum := by decide
  have hdescent : baseEnd_815 < baseStart_815 := by decide
  rcases family_descends (prefixWord ++ tailWord_815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819 : List Nat := [1, 1, 1, 2, 6, 1, 2, 4, 4]
def baseStart_819 : Nat := 118140960795 + 819 * 2 ^ 59
def prefixEnd_819 : Nat := 4983230072969 + 3 ^ 40 * 819 * 2
def baseEnd_819 : Nat := 93453479141673190831

theorem tailTrace_819 : CollatzResearch.WordTrace tailWord_819 prefixEnd_819 93453479141673190831 := by
  unfold tailWord_819
  simp only [CollatzResearch.WordTrace]
  refine ⟨29871384040377719173511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19914256026918479449007 29871384040377719173511)
  ·
    refine ⟨44807076060566578760267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29871384040377719173511 44807076060566578760267)
    ·
      refine ⟨67210614090849868140401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44807076060566578760267 67210614090849868140401)
      ·
        refine ⟨50407960568137401105301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67210614090849868140401 50407960568137401105301)
        ·
          refine ⟨2362873151631440676811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50407960568137401105301 2362873151631440676811)
          ·
            refine ⟨3544309727447161015217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362873151631440676811 3544309727447161015217)
            ·
              refine ⟨2658232295585370761413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544309727447161015217 2658232295585370761413)
              ·
                refine ⟨498418555422257017765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2658232295585370761413 498418555422257017765)
                ·
                  refine ⟨93453479141673190831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498418555422257017765 93453479141673190831)
                  ·
                    rfl

theorem cell22_819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 4].length) (baseStart_819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819 prefixEnd_819 := by exact prefixLift 819
  have htrace : WordTrace (prefixWord ++ tailWord_819) baseStart_819 baseEnd_819 := by
    simpa [prefixWord, tailWord_819, baseEnd_819] using wordTrace_append hprefix tailTrace_819
  have hstable : (prefixWord ++ tailWord_819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819).length < 2 ^ (prefixWord ++ tailWord_819).sum := by decide
  have hdescent : baseEnd_819 < baseStart_819 := by decide
  rcases family_descends (prefixWord ++ tailWord_819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_866 : Nat := 118140960795 + 866 * 2 ^ 59
def prefixEnd_866 : Nat := 4983230072969 + 3 ^ 40 * 866 * 2
def baseEnd_866 : Nat := 296449497932563647349

theorem tailTrace_866 : CollatzResearch.WordTrace tailWord_866 prefixEnd_866 296449497932563647349 := by
  unfold tailWord_866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896403717526186533613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21057076580069830756301 7896403717526186533613)
  ·
    refine ⟨2961151394072319950105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7896403717526186533613 2961151394072319950105)
    ·
      refine ⟨2220863545554239962579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2961151394072319950105 2220863545554239962579)
      ·
        refine ⟨3331295318331359943869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220863545554239962579 3331295318331359943869)
        ·
          refine ⟨1249235744374259978951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3331295318331359943869 1249235744374259978951)
          ·
            refine ⟨1873853616561389968427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249235744374259978951 1873853616561389968427)
            ·
              refine ⟨2810780424842084952641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873853616561389968427 2810780424842084952641)
              ·
                refine ⟨2108085318631563714481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810780424842084952641 2108085318631563714481)
                ·
                  refine ⟨1581063988973672785861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108085318631563714481 1581063988973672785861)
                  ·
                    refine ⟨296449497932563647349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1581063988973672785861 296449497932563647349)
                    ·
                      rfl

theorem cell22_866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866 prefixEnd_866 := by exact prefixLift 866
  have htrace : WordTrace (prefixWord ++ tailWord_866) baseStart_866 baseEnd_866 := by
    simpa [prefixWord, tailWord_866, baseEnd_866] using wordTrace_append hprefix tailTrace_866
  have hstable : (prefixWord ++ tailWord_866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866).length < 2 ^ (prefixWord ++ tailWord_866).sum := by decide
  have hdescent : baseEnd_866 < baseStart_866 := by decide
  rcases family_descends (prefixWord ++ tailWord_866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_877 : Nat := 118140960795 + 877 * 2 ^ 59
def prefixEnd_877 : Nat := 4983230072969 + 3 ^ 40 * 877 * 2
def baseEnd_877 : Nat := 300215022732201622315

theorem tailTrace_877 : CollatzResearch.WordTrace tailWord_877 prefixEnd_877 300215022732201622315 := by
  unfold tailWord_877
  simp only [CollatzResearch.WordTrace]
  refine ⟨31986817830253624784885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21324545220169083189923 31986817830253624784885)
  ·
    refine ⟨2998764171586277323583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31986817830253624784885 2998764171586277323583)
    ·
      refine ⟨4498146257379415985375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998764171586277323583 4498146257379415985375)
      ·
        refine ⟨6747219386069123978063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498146257379415985375 6747219386069123978063)
        ·
          refine ⟨10120829079103685967095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747219386069123978063 10120829079103685967095)
          ·
            refine ⟨15181243618655528950643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120829079103685967095 15181243618655528950643)
            ·
              refine ⟨22771865427983293425965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181243618655528950643 22771865427983293425965)
              ·
                refine ⟨8539449535493735034737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22771865427983293425965 8539449535493735034737)
                ·
                  refine ⟨6404587151620301276053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539449535493735034737 6404587151620301276053)
                  ·
                    refine ⟨300215022732201622315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6404587151620301276053 300215022732201622315)
                    ·
                      rfl

theorem cell22_877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877 prefixEnd_877 := by exact prefixLift 877
  have htrace : WordTrace (prefixWord ++ tailWord_877) baseStart_877 baseEnd_877 := by
    simpa [prefixWord, tailWord_877, baseEnd_877] using wordTrace_append hprefix tailTrace_877
  have hstable : (prefixWord ++ tailWord_877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877).length < 2 ^ (prefixWord ++ tailWord_877).sum := by decide
  have hdescent : baseEnd_877 < baseStart_877 := by decide
  rcases family_descends (prefixWord ++ tailWord_877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930 : List Nat := [3, 3, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_930 : Nat := 118140960795 + 930 * 2 ^ 59
def prefixEnd_930 : Nat := 4983230072969 + 3 ^ 40 * 930 * 2
def baseEnd_930 : Nat := 318358005857730047153

theorem tailTrace_930 : CollatzResearch.WordTrace tailWord_930 prefixEnd_930 318358005857730047153 := by
  unfold tailWord_930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479971659560919116061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22613257758829117642829 8479971659560919116061)
  ·
    refine ⟨3179989372335344668523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8479971659560919116061 3179989372335344668523)
    ·
      refine ⟨4769984058503017002785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3179989372335344668523 4769984058503017002785)
      ·
        refine ⟨3577488043877262752089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4769984058503017002785 3577488043877262752089)
        ·
          refine ⟨2683116032907947064067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3577488043877262752089 2683116032907947064067)
          ·
            refine ⟨4024674049361920596101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683116032907947064067 4024674049361920596101)
            ·
              refine ⟨754626384255360111769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4024674049361920596101 754626384255360111769)
              ·
                refine ⟨565969788191520083827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754626384255360111769 565969788191520083827)
                ·
                  refine ⟨848954682287280125741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565969788191520083827 848954682287280125741)
                  ·
                    refine ⟨318358005857730047153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 848954682287280125741 318358005857730047153)
                    ·
                      rfl

theorem cell22_930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930 prefixEnd_930 := by exact prefixLift 930
  have htrace : WordTrace (prefixWord ++ tailWord_930) baseStart_930 baseEnd_930 := by
    simpa [prefixWord, tailWord_930, baseEnd_930] using wordTrace_append hprefix tailTrace_930
  have hstable : (prefixWord ++ tailWord_930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930).length < 2 ^ (prefixWord ++ tailWord_930).sum := by decide
  have hdescent : baseEnd_930 < baseStart_930 := by decide
  rcases family_descends (prefixWord ++ tailWord_930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 6]
def baseStart_937 : Nat := 118140960795 + 937 * 2 ^ 59
def prefixEnd_937 : Nat := 4983230072969 + 3 ^ 40 * 937 * 2
def baseEnd_937 : Nat := 106918082970681707377

theorem tailTrace_937 : CollatzResearch.WordTrace tailWord_937 prefixEnd_937 106918082970681707377 := by
  unfold tailWord_937
  simp only [CollatzResearch.WordTrace]
  refine ⟨34175197612883871969065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22783465075255914646043 34175197612883871969065)
  ·
    refine ⟨25631398209662903976799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34175197612883871969065 25631398209662903976799)
    ·
      refine ⟨38447097314494355965199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25631398209662903976799 38447097314494355965199)
      ·
        refine ⟨57670645971741533947799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38447097314494355965199 57670645971741533947799)
        ·
          refine ⟨86505968957612300921699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57670645971741533947799 86505968957612300921699)
          ·
            refine ⟨129758953436418451382549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86505968957612300921699 129758953436418451382549)
            ·
              refine ⟨6082450942332114908557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129758953436418451382549 6082450942332114908557)
              ·
                refine ⟨2280919103374543090709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6082450942332114908557 2280919103374543090709)
                ·
                  refine ⟨106918082970681707377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2280919103374543090709 106918082970681707377)
                  ·
                    rfl

theorem cell22_937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937 prefixEnd_937 := by exact prefixLift 937
  have htrace : WordTrace (prefixWord ++ tailWord_937) baseStart_937 baseEnd_937 := by
    simpa [prefixWord, tailWord_937, baseEnd_937] using wordTrace_append hprefix tailTrace_937
  have hstable : (prefixWord ++ tailWord_937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937).length < 2 ^ (prefixWord ++ tailWord_937).sum := by decide
  have hdescent : baseEnd_937 < baseStart_937 := by decide
  rcases family_descends (prefixWord ++ tailWord_937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971 : List Nat := [1, 1, 1, 1, 3, 6, 2, 3, 4]
def baseStart_971 : Nat := 118140960795 + 971 * 2 ^ 59
def prefixEnd_971 : Nat := 4983230072969 + 3 ^ 40 * 971 * 2
def baseEnd_971 : Nat := 110797714582429924009

theorem tailTrace_971 : CollatzResearch.WordTrace tailWord_971 prefixEnd_971 110797714582429924009 := by
  unfold tailWord_971
  simp only [CollatzResearch.WordTrace]
  refine ⟨35415279489707678706767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23610186326471785804511 35415279489707678706767)
  ·
    refine ⟨53122919234561518060151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35415279489707678706767 53122919234561518060151)
    ·
      refine ⟨79684378851842277090227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53122919234561518060151 79684378851842277090227)
      ·
        refine ⟨119526568277763415635341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79684378851842277090227 119526568277763415635341)
        ·
          refine ⟨44822463104161280863253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119526568277763415635341 44822463104161280863253)
          ·
            refine ⟨2101052958007560040465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44822463104161280863253 2101052958007560040465)
            ·
              refine ⟨1575789718505670030349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101052958007560040465 1575789718505670030349)
              ·
                refine ⟨590921144439626261381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575789718505670030349 590921144439626261381)
                ·
                  refine ⟨110797714582429924009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590921144439626261381 110797714582429924009)
                  ·
                    rfl

theorem cell22_971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 4].length) (baseStart_971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971 prefixEnd_971 := by exact prefixLift 971
  have htrace : WordTrace (prefixWord ++ tailWord_971) baseStart_971 baseEnd_971 := by
    simpa [prefixWord, tailWord_971, baseEnd_971] using wordTrace_append hprefix tailTrace_971
  have hstable : (prefixWord ++ tailWord_971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971).length < 2 ^ (prefixWord ++ tailWord_971).sum := by decide
  have hdescent : baseEnd_971 < baseStart_971 := by decide
  rcases family_descends (prefixWord ++ tailWord_971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_986 : Nat := 118140960795 + 986 * 2 ^ 59
def prefixEnd_986 : Nat := 4983230072969 + 3 ^ 40 * 986 * 2
def baseEnd_986 : Nat := 337527950292250646981

theorem tailTrace_986 : CollatzResearch.WordTrace tailWord_986 prefixEnd_986 337527950292250646981 := by
  unfold tailWord_986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990593608841310125703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23974916290243493668541 8990593608841310125703)
  ·
    refine ⟨13485890413261965188555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8990593608841310125703 13485890413261965188555)
    ·
      refine ⟨20228835619892947782833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13485890413261965188555 20228835619892947782833)
      ·
        refine ⟨15171626714919710837125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20228835619892947782833 15171626714919710837125)
        ·
          refine ⟨2844680009047445781961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15171626714919710837125 2844680009047445781961)
          ·
            refine ⟨2133510006785584336471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844680009047445781961 2133510006785584336471)
            ·
              refine ⟨3200265010178376504707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133510006785584336471 3200265010178376504707)
              ·
                refine ⟨4800397515267564757061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200265010178376504707 4800397515267564757061)
                ·
                  refine ⟨900074534112668391949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4800397515267564757061 900074534112668391949)
                  ·
                    refine ⟨337527950292250646981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900074534112668391949 337527950292250646981)
                    ·
                      rfl

theorem cell22_986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986 prefixEnd_986 := by exact prefixLift 986
  have htrace : WordTrace (prefixWord ++ tailWord_986) baseStart_986 baseEnd_986 := by
    simpa [prefixWord, tailWord_986, baseEnd_986] using wordTrace_append hprefix tailTrace_986
  have hstable : (prefixWord ++ tailWord_986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986).length < 2 ^ (prefixWord ++ tailWord_986).sum := by decide
  have hdescent : baseEnd_986 < baseStart_986 := by decide
  rcases family_descends (prefixWord ++ tailWord_986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022 : List Nat := [4, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1022 : Nat := 118140960795 + 1022 * 2 ^ 59
def prefixEnd_1022 : Nat := 4983230072969 + 3 ^ 40 * 1022 * 2
def baseEnd_1022 : Nat := 116617162000052248957

theorem tailTrace_1022 : CollatzResearch.WordTrace tailWord_1022 prefixEnd_1022 116617162000052248957 := by
  unfold tailWord_1022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659425288117923601665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24850268203295592542213 4659425288117923601665)
  ·
    refine ⟨3494568966088442701249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4659425288117923601665 3494568966088442701249)
    ·
      refine ⟨2620926724566332025937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3494568966088442701249 2620926724566332025937)
      ·
        refine ⟨1965695043424749019453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2620926724566332025937 1965695043424749019453)
        ·
          refine ⟨737135641284280882295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1965695043424749019453 737135641284280882295)
          ·
            refine ⟨1105703461926421323443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737135641284280882295 1105703461926421323443)
            ·
              refine ⟨1658555192889631985165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105703461926421323443 1658555192889631985165)
              ·
                refine ⟨621958197333611994437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1658555192889631985165 621958197333611994437)
                ·
                  refine ⟨116617162000052248957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 621958197333611994437 116617162000052248957)
                  ·
                    rfl

theorem cell22_1022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022 prefixEnd_1022 := by exact prefixLift 1022
  have htrace : WordTrace (prefixWord ++ tailWord_1022) baseStart_1022 baseEnd_1022 := by
    simpa [prefixWord, tailWord_1022, baseEnd_1022] using wordTrace_append hprefix tailTrace_1022
  have hstable : (prefixWord ++ tailWord_1022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022).length < 2 ^ (prefixWord ++ tailWord_1022).sum := by decide
  have hdescent : baseEnd_1022 < baseStart_1022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 3, 3]
def baseStart_1048 : Nat := 118140960795 + 1048 * 2 ^ 59
def prefixEnd_1048 : Nat := 4983230072969 + 3 ^ 40 * 1048 * 2
def baseEnd_1048 : Nat := 358751817344755596791

theorem tailTrace_1048 : CollatzResearch.WordTrace tailWord_1048 prefixEnd_1048 358751817344755596791 := by
  unfold tailWord_1048
  simp only [CollatzResearch.WordTrace]
  refine ⟨19111850105374914629899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25482466807166552839865 19111850105374914629899)
  ·
    refine ⟨28667775158062371944849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19111850105374914629899 28667775158062371944849)
    ·
      refine ⟨21500831368546778958637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28667775158062371944849 21500831368546778958637)
      ·
        refine ⟨8062811763205042109489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21500831368546778958637 8062811763205042109489)
        ·
          refine ⟨6047108822403781582117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8062811763205042109489 6047108822403781582117)
          ·
            refine ⟨1133832904200709046647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6047108822403781582117 1133832904200709046647)
            ·
              refine ⟨1700749356301063569971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133832904200709046647 1700749356301063569971)
              ·
                refine ⟨2551124034451595354957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700749356301063569971 2551124034451595354957)
                ·
                  refine ⟨956671512919348258109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2551124034451595354957 956671512919348258109)
                  ·
                    refine ⟨358751817344755596791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956671512919348258109 358751817344755596791)
                    ·
                      rfl

theorem cell22_1048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_1048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048 prefixEnd_1048 := by exact prefixLift 1048
  have htrace : WordTrace (prefixWord ++ tailWord_1048) baseStart_1048 baseEnd_1048 := by
    simpa [prefixWord, tailWord_1048, baseEnd_1048] using wordTrace_append hprefix tailTrace_1048
  have hstable : (prefixWord ++ tailWord_1048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048).length < 2 ^ (prefixWord ++ tailWord_1048).sum := by decide
  have hdescent : baseEnd_1048 < baseStart_1048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1110 : Nat := 118140960795 + 1110 * 2 ^ 59
def prefixEnd_1110 : Nat := 4983230072969 + 3 ^ 40 * 1110 * 2
def baseEnd_1110 : Nat := 379975684397260546601

theorem tailTrace_1110 : CollatzResearch.WordTrace tailWord_1110 prefixEnd_1110 379975684397260546601 := by
  unfold tailWord_1110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530314124133401126049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26990017324089612011189 2530314124133401126049)
  ·
    refine ⟨1897735593100050844537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2530314124133401126049 1897735593100050844537)
    ·
      refine ⟨1423301694825038133403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1897735593100050844537 1423301694825038133403)
      ·
        refine ⟨2134952542237557200105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423301694825038133403 2134952542237557200105)
        ·
          refine ⟨1601214406678167900079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134952542237557200105 1601214406678167900079)
          ·
            refine ⟨2401821610017251850119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601214406678167900079 2401821610017251850119)
            ·
              refine ⟨3602732415025877775179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401821610017251850119 3602732415025877775179)
              ·
                refine ⟨5404098622538816662769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602732415025877775179 5404098622538816662769)
                ·
                  refine ⟨4053073966904112497077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404098622538816662769 4053073966904112497077)
                  ·
                    refine ⟨379975684397260546601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4053073966904112497077 379975684397260546601)
                    ·
                      rfl

theorem cell22_1110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110 prefixEnd_1110 := by exact prefixLift 1110
  have htrace : WordTrace (prefixWord ++ tailWord_1110) baseStart_1110 baseEnd_1110 := by
    simpa [prefixWord, tailWord_1110, baseEnd_1110] using wordTrace_append hprefix tailTrace_1110
  have hstable : (prefixWord ++ tailWord_1110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110).length < 2 ^ (prefixWord ++ tailWord_1110).sum := by decide
  have hdescent : baseEnd_1110 < baseStart_1110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 1, 6]
def baseStart_1119 : Nat := 118140960795 + 1119 * 2 ^ 59
def prefixEnd_1119 : Nat := 4983230072969 + 3 ^ 40 * 1119 * 2
def baseEnd_1119 : Nat := 383056568324237071573

theorem tailTrace_1119 : CollatzResearch.WordTrace tailWord_1119 prefixEnd_1119 383056568324237071573 := by
  unfold tailWord_1119
  simp only [CollatzResearch.WordTrace]
  refine ⟨40813282953528955094411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27208855302352636729607 40813282953528955094411)
  ·
    refine ⟨61219924430293432641617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40813282953528955094411 61219924430293432641617)
    ·
      refine ⟨45914943322720074481213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61219924430293432641617 45914943322720074481213)
      ·
        refine ⟨17218103746020027930455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45914943322720074481213 17218103746020027930455)
        ·
          refine ⟨25827155619030041895683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17218103746020027930455 25827155619030041895683)
          ·
            refine ⟨38740733428545062843525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25827155619030041895683 38740733428545062843525)
            ·
              refine ⟨7263887517852199283161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38740733428545062843525 7263887517852199283161)
              ·
                refine ⟨5447915638389149462371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7263887517852199283161 5447915638389149462371)
                ·
                  refine ⟨8171873457583724193557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5447915638389149462371 8171873457583724193557)
                  ·
                    refine ⟨383056568324237071573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8171873457583724193557 383056568324237071573)
                    ·
                      rfl

theorem cell22_1119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_1119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119 prefixEnd_1119 := by exact prefixLift 1119
  have htrace : WordTrace (prefixWord ++ tailWord_1119) baseStart_1119 baseEnd_1119 := by
    simpa [prefixWord, tailWord_1119, baseEnd_1119] using wordTrace_append hprefix tailTrace_1119
  have hstable : (prefixWord ++ tailWord_1119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119).length < 2 ^ (prefixWord ++ tailWord_1119).sum := by decide
  have hdescent : baseEnd_1119 < baseStart_1119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1164 : Nat := 118140960795 + 1164 * 2 ^ 59
def prefixEnd_1164 : Nat := 4983230072969 + 3 ^ 40 * 1164 * 2
def baseEnd_1164 : Nat := 398460987959119696435

theorem tailTrace_1164 : CollatzResearch.WordTrace tailWord_1164 prefixEnd_1164 398460987959119696435 := by
  unfold tailWord_1164
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227283895250820241273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28303045193667760321697 21227283895250820241273)
  ·
    refine ⟨15920462921438115180955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21227283895250820241273 15920462921438115180955)
    ·
      refine ⟨23880694382157172771433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15920462921438115180955 23880694382157172771433)
      ·
        refine ⟨17910520786617879578575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23880694382157172771433 17910520786617879578575)
        ·
          refine ⟨26865781179926819367863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17910520786617879578575 26865781179926819367863)
          ·
            refine ⟨40298671769890229051795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26865781179926819367863 40298671769890229051795)
            ·
              refine ⟨60448007654835343577693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40298671769890229051795 60448007654835343577693)
              ·
                refine ⟨22668002870563253841635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60448007654835343577693 22668002870563253841635)
                ·
                  refine ⟨34002004305844880762453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22668002870563253841635 34002004305844880762453)
                  ·
                    refine ⟨398460987959119696435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34002004305844880762453 398460987959119696435)
                    ·
                      rfl

theorem cell22_1164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164 prefixEnd_1164 := by exact prefixLift 1164
  have htrace : WordTrace (prefixWord ++ tailWord_1164) baseStart_1164 baseEnd_1164 := by
    simpa [prefixWord, tailWord_1164, baseEnd_1164] using wordTrace_append hprefix tailTrace_1164
  have hstable : (prefixWord ++ tailWord_1164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164).length < 2 ^ (prefixWord ++ tailWord_1164).sum := by decide
  have hdescent : baseEnd_1164 < baseStart_1164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1217 : Nat := 118140960795 + 1217 * 2 ^ 59
def prefixEnd_1217 : Nat := 4983230072969 + 3 ^ 40 * 1217 * 2
def baseEnd_1217 : Nat := 416603971084648121273

theorem tailTrace_1217 : CollatzResearch.WordTrace tailWord_1217 prefixEnd_1217 416603971084648121273 := by
  unfold tailWord_1217
  simp only [CollatzResearch.WordTrace]
  refine ⟨44387636598491692161905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29591757732327794774603 44387636598491692161905)
  ·
    refine ⟨33290727448868769121429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44387636598491692161905 33290727448868769121429)
    ·
      refine ⟨1560502849165723552567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33290727448868769121429 1560502849165723552567)
      ·
        refine ⟨2340754273748585328851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560502849165723552567 2340754273748585328851)
        ·
          refine ⟨3511131410622877993277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340754273748585328851 3511131410622877993277)
          ·
            refine ⟨1316674278983579247479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3511131410622877993277 1316674278983579247479)
            ·
              refine ⟨1975011418475368871219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316674278983579247479 1975011418475368871219)
              ·
                refine ⟨2962517127713053306829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975011418475368871219 2962517127713053306829)
                ·
                  refine ⟨1110943922892394990061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2962517127713053306829 1110943922892394990061)
                  ·
                    refine ⟨416603971084648121273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110943922892394990061 416603971084648121273)
                    ·
                      rfl

theorem cell22_1217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217 prefixEnd_1217 := by exact prefixLift 1217
  have htrace : WordTrace (prefixWord ++ tailWord_1217) baseStart_1217 baseEnd_1217 := by
    simpa [prefixWord, tailWord_1217, baseEnd_1217] using wordTrace_append hprefix tailTrace_1217
  have hstable : (prefixWord ++ tailWord_1217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217).length < 2 ^ (prefixWord ++ tailWord_1217).sum := by decide
  have hdescent : baseEnd_1217 < baseStart_1217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_1260 : Nat := 118140960795 + 1260 * 2 ^ 59
def prefixEnd_1260 : Nat := 4983230072969 + 3 ^ 40 * 1260 * 2
def baseEnd_1260 : Nat := 431323749846869296141

theorem tailTrace_1260 : CollatzResearch.WordTrace tailWord_1260 prefixEnd_1260 431323749846869296141 := by
  unfold tailWord_1260
  simp only [CollatzResearch.WordTrace]
  refine ⟨22977987721355017988617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30637316961806690651489 22977987721355017988617)
  ·
    refine ⟨17233490791016263491463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22977987721355017988617 17233490791016263491463)
    ·
      refine ⟨25850236186524395237195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17233490791016263491463 25850236186524395237195)
      ·
        refine ⟨38775354279786592855793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25850236186524395237195 38775354279786592855793)
        ·
          refine ⟨29081515709839944641845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38775354279786592855793 29081515709839944641845)
          ·
            refine ⟨2726392097797494810173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29081515709839944641845 2726392097797494810173)
            ·
              refine ⟨1022397036674060553815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2726392097797494810173 1022397036674060553815)
              ·
                refine ⟨1533595555011090830723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022397036674060553815 1533595555011090830723)
                ·
                  refine ⟨2300393332516636246085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533595555011090830723 2300393332516636246085)
                  ·
                    refine ⟨431323749846869296141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2300393332516636246085 431323749846869296141)
                    ·
                      rfl

theorem cell22_1260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_1260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1260 prefixEnd_1260 := by exact prefixLift 1260
  have htrace : WordTrace (prefixWord ++ tailWord_1260) baseStart_1260 baseEnd_1260 := by
    simpa [prefixWord, tailWord_1260, baseEnd_1260] using wordTrace_append hprefix tailTrace_1260
  have hstable : (prefixWord ++ tailWord_1260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260).length < 2 ^ (prefixWord ++ tailWord_1260).sum := by decide
  have hdescent : baseEnd_1260 < baseStart_1260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303 : List Nat := [1, 1, 3, 4, 1, 1, 5, 6]
def baseStart_1303 : Nat := 118140960795 + 1303 * 2 ^ 59
def prefixEnd_1303 : Nat := 4983230072969 + 3 ^ 40 * 1303 * 2
def baseEnd_1303 : Nat := 49560392067676719001

theorem tailTrace_1303 : CollatzResearch.WordTrace tailWord_1303 prefixEnd_1303 49560392067676719001 := by
  unfold tailWord_1303
  simp only [CollatzResearch.WordTrace]
  refine ⟨47524314286928379792563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31682876191285586528375 47524314286928379792563)
  ·
    refine ⟨71286471430392569688845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47524314286928379792563 71286471430392569688845)
    ·
      refine ⟨26732426786397213633317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71286471430392569688845 26732426786397213633317)
      ·
        refine ⟨5012330022449477556247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26732426786397213633317 5012330022449477556247)
        ·
          refine ⟨7518495033674216334371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012330022449477556247 7518495033674216334371)
          ·
            refine ⟨11277742550511324501557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7518495033674216334371 11277742550511324501557)
            ·
              refine ⟨1057288364110436672021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11277742550511324501557 1057288364110436672021)
              ·
                refine ⟨49560392067676719001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1057288364110436672021 49560392067676719001)
                ·
                  rfl

theorem cell22_1303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 6].length) (baseStart_1303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303 prefixEnd_1303 := by exact prefixLift 1303
  have htrace : WordTrace (prefixWord ++ tailWord_1303) baseStart_1303 baseEnd_1303 := by
    simpa [prefixWord, tailWord_1303, baseEnd_1303] using wordTrace_append hprefix tailTrace_1303
  have hstable : (prefixWord ++ tailWord_1303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303).length < 2 ^ (prefixWord ++ tailWord_1303).sum := by decide
  have hdescent : baseEnd_1303 < baseStart_1303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386 : List Nat := [3, 1, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1386 : Nat := 118140960795 + 1386 * 2 ^ 59
def prefixEnd_1386 : Nat := 4983230072969 + 3 ^ 40 * 1386 * 2
def baseEnd_1386 : Nat := 474456124824540645755

theorem tailTrace_1386 : CollatzResearch.WordTrace tailWord_1386 prefixEnd_1386 474456124824540645755 := by
  unfold tailWord_1386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12637893246558388766003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33701048657489036709341 12637893246558388766003)
  ·
    refine ⟨18956839869837583149005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12637893246558388766003 18956839869837583149005)
    ·
      refine ⟨7108814951189093680877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18956839869837583149005 7108814951189093680877)
      ·
        refine ⟨2665805606695910130329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7108814951189093680877 2665805606695910130329)
        ·
          refine ⟨1999354205021932597747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665805606695910130329 1999354205021932597747)
          ·
            refine ⟨2999031307532898896621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999354205021932597747 2999031307532898896621)
            ·
              refine ⟨1124636740324837086233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2999031307532898896621 1124636740324837086233)
              ·
                refine ⟨843477555243627814675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124636740324837086233 843477555243627814675)
                ·
                  refine ⟨1265216332865441722013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843477555243627814675 1265216332865441722013)
                  ·
                    refine ⟨474456124824540645755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1265216332865441722013 474456124824540645755)
                    ·
                      rfl

theorem cell22_1386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1386 prefixEnd_1386 := by exact prefixLift 1386
  have htrace : WordTrace (prefixWord ++ tailWord_1386) baseStart_1386 baseEnd_1386 := by
    simpa [prefixWord, tailWord_1386, baseEnd_1386] using wordTrace_append hprefix tailTrace_1386
  have hstable : (prefixWord ++ tailWord_1386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386).length < 2 ^ (prefixWord ++ tailWord_1386).sum := by decide
  have hdescent : baseEnd_1386 < baseStart_1386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 6]
def baseStart_1393 : Nat := 118140960795 + 1393 * 2 ^ 59
def prefixEnd_1393 : Nat := 4983230072969 + 3 ^ 40 * 1393 * 2
def baseEnd_1393 : Nat := 158950789292951906911

theorem tailTrace_1393 : CollatzResearch.WordTrace tailWord_1393 prefixEnd_1393 158950789292951906911 := by
  unfold tailWord_1393
  simp only [CollatzResearch.WordTrace]
  refine ⟨50806883960873750568833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33871255973915833712555 50806883960873750568833)
  ·
    refine ⟨38105162970655312926625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50806883960873750568833 38105162970655312926625)
    ·
      refine ⟨28578872227991484694969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38105162970655312926625 28578872227991484694969)
      ·
        refine ⟨21434154170993613521227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28578872227991484694969 21434154170993613521227)
        ·
          refine ⟨32151231256490420281841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21434154170993613521227 32151231256490420281841)
          ·
            refine ⟨24113423442367815211381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32151231256490420281841 24113423442367815211381)
            ·
              refine ⟨2260633447721982676067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24113423442367815211381 2260633447721982676067)
              ·
                refine ⟨3390950171582974014101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260633447721982676067 3390950171582974014101)
                ·
                  refine ⟨158950789292951906911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3390950171582974014101 158950789292951906911)
                  ·
                    rfl

theorem cell22_1393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_1393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393 prefixEnd_1393 := by exact prefixLift 1393
  have htrace : WordTrace (prefixWord ++ tailWord_1393) baseStart_1393 baseEnd_1393 := by
    simpa [prefixWord, tailWord_1393, baseEnd_1393] using wordTrace_append hprefix tailTrace_1393
  have hstable : (prefixWord ++ tailWord_1393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393).length < 2 ^ (prefixWord ++ tailWord_1393).sum := by decide
  have hdescent : baseEnd_1393 < baseStart_1393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1412 : Nat := 118140960795 + 1412 * 2 ^ 59
def prefixEnd_1412 : Nat := 4983230072969 + 3 ^ 40 * 1412 * 2
def baseEnd_1412 : Nat := 483356456169139495675

theorem tailTrace_1412 : CollatzResearch.WordTrace tailWord_1412 prefixEnd_1412 483356456169139495675 := by
  unfold tailWord_1412
  simp only [CollatzResearch.WordTrace]
  refine ⟨25749935446019997755245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34333247261359997006993 25749935446019997755245)
  ·
    refine ⟨9656225792257499158217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25749935446019997755245 9656225792257499158217)
    ·
      refine ⟨7242169344193124368663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9656225792257499158217 7242169344193124368663)
      ·
        refine ⟨10863254016289686552995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7242169344193124368663 10863254016289686552995)
        ·
          refine ⟨16294881024434529829493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10863254016289686552995 16294881024434529829493)
          ·
            refine ⟨1527645096040737171515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16294881024434529829493 1527645096040737171515)
            ·
              refine ⟨2291467644061105757273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527645096040737171515 2291467644061105757273)
              ·
                refine ⟨1718600733045829317955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291467644061105757273 1718600733045829317955)
                ·
                  refine ⟨2577901099568743976933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718600733045829317955 2577901099568743976933)
                  ·
                    refine ⟨483356456169139495675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2577901099568743976933 483356456169139495675)
                    ·
                      rfl

theorem cell22_1412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412 prefixEnd_1412 := by exact prefixLift 1412
  have htrace : WordTrace (prefixWord ++ tailWord_1412) baseStart_1412 baseEnd_1412 := by
    simpa [prefixWord, tailWord_1412, baseEnd_1412] using wordTrace_append hprefix tailTrace_1412
  have hstable : (prefixWord ++ tailWord_1412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412).length < 2 ^ (prefixWord ++ tailWord_1412).sum := by decide
  have hdescent : baseEnd_1412 < baseStart_1412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1442 : Nat := 118140960795 + 1442 * 2 ^ 59
def prefixEnd_1442 : Nat := 4983230072969 + 3 ^ 40 * 1442 * 2
def baseEnd_1442 : Nat := 493626069259061245583

theorem tailTrace_1442 : CollatzResearch.WordTrace tailWord_1442 prefixEnd_1442 493626069259061245583 := by
  unfold tailWord_1442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13148515195838779775645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35062707188903412735053 13148515195838779775645)
  ·
    refine ⟨4930693198439542415867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13148515195838779775645 4930693198439542415867)
    ·
      refine ⟨7396039797659313623801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4930693198439542415867 7396039797659313623801)
      ·
        refine ⟨5547029848244485217851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7396039797659313623801 5547029848244485217851)
        ·
          refine ⟨8320544772366727826777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5547029848244485217851 8320544772366727826777)
          ·
            refine ⟨6240408579275045870083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8320544772366727826777 6240408579275045870083)
            ·
              refine ⟨9360612868912568805125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6240408579275045870083 9360612868912568805125)
              ·
                refine ⟨1755114912921106650961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9360612868912568805125 1755114912921106650961)
                ·
                  refine ⟨1316336184690829988221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1755114912921106650961 1316336184690829988221)
                  ·
                    refine ⟨493626069259061245583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1316336184690829988221 493626069259061245583)
                    ·
                      rfl

theorem cell22_1442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1442 prefixEnd_1442 := by exact prefixLift 1442
  have htrace : WordTrace (prefixWord ++ tailWord_1442) baseStart_1442 baseEnd_1442 := by
    simpa [prefixWord, tailWord_1442, baseEnd_1442] using wordTrace_append hprefix tailTrace_1442
  have hstable : (prefixWord ++ tailWord_1442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442).length < 2 ^ (prefixWord ++ tailWord_1442).sum := by decide
  have hdescent : baseEnd_1442 < baseStart_1442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487 : List Nat := [1, 1, 2, 1, 1, 4, 3, 5, 1, 3]
def baseStart_1487 : Nat := 118140960795 + 1487 * 2 ^ 59
def prefixEnd_1487 : Nat := 4983230072969 + 3 ^ 40 * 1487 * 2
def baseEnd_1487 : Nat := 509030488893943870445

theorem tailTrace_1487 : CollatzResearch.WordTrace tailWord_1487 prefixEnd_1487 509030488893943870445 := by
  unfold tailWord_1487
  simp only [CollatzResearch.WordTrace]
  refine ⟨54235345620327804490715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36156897080218536327143 54235345620327804490715)
  ·
    refine ⟨81353018430491706736073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54235345620327804490715 81353018430491706736073)
    ·
      refine ⟨61014763822868780052055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81353018430491706736073 61014763822868780052055)
      ·
        refine ⟨91522145734303170078083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61014763822868780052055 91522145734303170078083)
        ·
          refine ⟨137283218601454755117125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91522145734303170078083 137283218601454755117125)
          ·
            refine ⟨25740603487772766584461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137283218601454755117125 25740603487772766584461)
            ·
              refine ⟨9652726307914787469173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25740603487772766584461 9652726307914787469173)
              ·
                refine ⟨904943091367011325235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9652726307914787469173 904943091367011325235)
                ·
                  refine ⟨1357414637050516987853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904943091367011325235 1357414637050516987853)
                  ·
                    refine ⟨509030488893943870445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357414637050516987853 509030488893943870445)
                    ·
                      rfl

theorem cell22_1487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 3].length) (baseStart_1487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487 prefixEnd_1487 := by exact prefixLift 1487
  have htrace : WordTrace (prefixWord ++ tailWord_1487) baseStart_1487 baseEnd_1487 := by
    simpa [prefixWord, tailWord_1487, baseEnd_1487] using wordTrace_append hprefix tailTrace_1487
  have hstable : (prefixWord ++ tailWord_1487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487).length < 2 ^ (prefixWord ++ tailWord_1487).sum := by decide
  have hdescent : baseEnd_1487 < baseStart_1487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538 : List Nat := [3, 4, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1538 : Nat := 118140960795 + 1538 * 2 ^ 59
def prefixEnd_1538 : Nat := 4983230072969 + 3 ^ 40 * 1538 * 2
def baseEnd_1538 : Nat := 526488831146810845289

theorem tailTrace_1538 : CollatzResearch.WordTrace tailWord_1538 prefixEnd_1538 526488831146810845289 := by
  unfold tailWord_1538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14023867108890878649317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37396978957042343064845 14023867108890878649317)
  ·
    refine ⟨2629475082917039746747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14023867108890878649317 2629475082917039746747)
    ·
      refine ⟨3944212624375559620121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629475082917039746747 3944212624375559620121)
      ·
        refine ⟨2958159468281669715091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3944212624375559620121 2958159468281669715091)
        ·
          refine ⟨4437239202422504572637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958159468281669715091 4437239202422504572637)
          ·
            refine ⟨1663964700908439214739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4437239202422504572637 1663964700908439214739)
            ·
              refine ⟨2495947051362658822109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663964700908439214739 2495947051362658822109)
              ·
                refine ⟨935980144260997058291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2495947051362658822109 935980144260997058291)
                ·
                  refine ⟨1403970216391495587437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935980144260997058291 1403970216391495587437)
                  ·
                    refine ⟨526488831146810845289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403970216391495587437 526488831146810845289)
                    ·
                      rfl

theorem cell22_1538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538 prefixEnd_1538 := by exact prefixLift 1538
  have htrace : WordTrace (prefixWord ++ tailWord_1538) baseStart_1538 baseEnd_1538 := by
    simpa [prefixWord, tailWord_1538, baseEnd_1538] using wordTrace_append hprefix tailTrace_1538
  have hstable : (prefixWord ++ tailWord_1538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538).length < 2 ^ (prefixWord ++ tailWord_1538).sum := by decide
  have hdescent : baseEnd_1538 < baseStart_1538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1592 : Nat := 118140960795 + 1592 * 2 ^ 59
def prefixEnd_1592 : Nat := 4983230072969 + 3 ^ 40 * 1592 * 2
def baseEnd_1592 : Nat := 544974134708669995123

theorem tailTrace_1592 : CollatzResearch.WordTrace tailWord_1592 prefixEnd_1592 544974134708669995123 := by
  unfold tailWord_1592
  simp only [CollatzResearch.WordTrace]
  refine ⟨29032505119965368531515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38710006826620491375353 29032505119965368531515)
  ·
    refine ⟨43548757679948052797273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29032505119965368531515 43548757679948052797273)
    ·
      refine ⟨32661568259961039597955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43548757679948052797273 32661568259961039597955)
      ·
        refine ⟨48992352389941559396933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32661568259961039597955 48992352389941559396933)
        ·
          refine ⟨9186066073114042386925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48992352389941559396933 9186066073114042386925)
          ·
            refine ⟨3444774777417765895097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9186066073114042386925 3444774777417765895097)
            ·
              refine ⟨2583581083063324421323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444774777417765895097 2583581083063324421323)
              ·
                refine ⟨3875371624594986631985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583581083063324421323 3875371624594986631985)
                ·
                  refine ⟨2906528718446239973989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875371624594986631985 2906528718446239973989)
                  ·
                    refine ⟨544974134708669995123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906528718446239973989 544974134708669995123)
                    ·
                      rfl

theorem cell22_1592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1592 prefixEnd_1592 := by exact prefixLift 1592
  have htrace : WordTrace (prefixWord ++ tailWord_1592) baseStart_1592 baseEnd_1592 := by
    simpa [prefixWord, tailWord_1592, baseEnd_1592] using wordTrace_append hprefix tailTrace_1592
  have hstable : (prefixWord ++ tailWord_1592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592).length < 2 ^ (prefixWord ++ tailWord_1592).sum := by decide
  have hdescent : baseEnd_1592 < baseStart_1592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613 : List Nat := [1, 6, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1613 : Nat := 118140960795 + 1613 * 2 ^ 59
def prefixEnd_1613 : Nat := 4983230072969 + 3 ^ 40 * 1613 * 2
def baseEnd_1613 : Nat := 184054287957205073353

theorem tailTrace_1613 : CollatzResearch.WordTrace tailWord_1613 prefixEnd_1613 184054287957205073353 := by
  unfold tailWord_1613
  simp only [CollatzResearch.WordTrace]
  refine ⟨58830943163851323577493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39220628775900882384995 58830943163851323577493)
  ·
    refine ⟨2757700460805530792695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58830943163851323577493 2757700460805530792695)
    ·
      refine ⟨4136550691208296189043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757700460805530792695 4136550691208296189043)
      ·
        refine ⟨6204826036812444283565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136550691208296189043 6204826036812444283565)
        ·
          refine ⟨2326809763804666606337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6204826036812444283565 2326809763804666606337)
          ·
            refine ⟨1745107322853499954753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326809763804666606337 1745107322853499954753)
            ·
              refine ⟨1308830492140124966065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745107322853499954753 1308830492140124966065)
              ·
                refine ⟨981622869105093724549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308830492140124966065 981622869105093724549)
                ·
                  refine ⟨184054287957205073353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981622869105093724549 184054287957205073353)
                  ·
                    rfl

theorem cell22_1613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613 prefixEnd_1613 := by exact prefixLift 1613
  have htrace : WordTrace (prefixWord ++ tailWord_1613) baseStart_1613 baseEnd_1613 := by
    simpa [prefixWord, tailWord_1613, baseEnd_1613] using wordTrace_append hprefix tailTrace_1613
  have hstable : (prefixWord ++ tailWord_1613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613).length < 2 ^ (prefixWord ++ tailWord_1613).sum := by decide
  have hdescent : baseEnd_1613 < baseStart_1613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1620 : Nat := 118140960795 + 1620 * 2 ^ 59
def prefixEnd_1620 : Nat := 4983230072969 + 3 ^ 40 * 1620 * 2
def baseEnd_1620 : Nat := 554559106925930295037

theorem tailTrace_1620 : CollatzResearch.WordTrace tailWord_1620 prefixEnd_1620 554559106925930295037 := by
  unfold tailWord_1620
  simp only [CollatzResearch.WordTrace]
  refine ⟨29543127069245759541157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39390836092327679388209 29543127069245759541157)
  ·
    refine ⟨5539336325483579913967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29543127069245759541157 5539336325483579913967)
    ·
      refine ⟨8309004488225369870951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5539336325483579913967 8309004488225369870951)
      ·
        refine ⟨12463506732338054806427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309004488225369870951 12463506732338054806427)
        ·
          refine ⟨18695260098507082209641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12463506732338054806427 18695260098507082209641)
          ·
            refine ⟨14021445073880311657231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18695260098507082209641 14021445073880311657231)
            ·
              refine ⟨21032167610820467485847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14021445073880311657231 21032167610820467485847)
              ·
                refine ⟨31548251416230701228771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21032167610820467485847 31548251416230701228771)
                ·
                  refine ⟨47322377124346051843157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31548251416230701228771 47322377124346051843157)
                  ·
                    refine ⟨554559106925930295037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47322377124346051843157 554559106925930295037)
                    ·
                      rfl

theorem cell22_1620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620 prefixEnd_1620 := by exact prefixLift 1620
  have htrace : WordTrace (prefixWord ++ tailWord_1620) baseStart_1620 baseEnd_1620 := by
    simpa [prefixWord, tailWord_1620, baseEnd_1620] using wordTrace_append hprefix tailTrace_1620
  have hstable : (prefixWord ++ tailWord_1620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620).length < 2 ^ (prefixWord ++ tailWord_1620).sum := by decide
  have hdescent : baseEnd_1620 < baseStart_1620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 6]
def baseStart_1697 : Nat := 118140960795 + 1697 * 2 ^ 59
def prefixEnd_1697 : Nat := 4983230072969 + 3 ^ 40 * 1697 * 2
def baseEnd_1697 : Nat := 193639260174465373267

theorem tailTrace_1697 : CollatzResearch.WordTrace tailWord_1697 prefixEnd_1697 193639260174465373267 := by
  unfold tailWord_1697
  simp only [CollatzResearch.WordTrace]
  refine ⟨61894674859533669635345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41263116573022446423563 61894674859533669635345)
  ·
    refine ⟨46421006144650252226509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61894674859533669635345 46421006144650252226509)
    ·
      refine ⟨17407877304243844584941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46421006144650252226509 17407877304243844584941)
      ·
        refine ⟨6527953989091441719353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17407877304243844584941 6527953989091441719353)
        ·
          refine ⟨4895965491818581289515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6527953989091441719353 4895965491818581289515)
          ·
            refine ⟨7343948237727871934273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895965491818581289515 7343948237727871934273)
            ·
              refine ⟨5507961178295903950705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343948237727871934273 5507961178295903950705)
              ·
                refine ⟨4130970883721927963029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507961178295903950705 4130970883721927963029)
                ·
                  refine ⟨193639260174465373267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4130970883721927963029 193639260174465373267)
                  ·
                    rfl

theorem cell22_1697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_1697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697 prefixEnd_1697 := by exact prefixLift 1697
  have htrace : WordTrace (prefixWord ++ tailWord_1697) baseStart_1697 baseEnd_1697 := by
    simpa [prefixWord, tailWord_1697, baseEnd_1697] using wordTrace_append hprefix tailTrace_1697
  have hstable : (prefixWord ++ tailWord_1697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697).length < 2 ^ (prefixWord ++ tailWord_1697).sum := by decide
  have hdescent : baseEnd_1697 < baseStart_1697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 4, 3]
def baseStart_1712 : Nat := 118140960795 + 1712 * 2 ^ 59
def prefixEnd_1712 : Nat := 4983230072969 + 3 ^ 40 * 1712 * 2
def baseEnd_1712 : Nat := 586052587068356994755

theorem tailTrace_1712 : CollatzResearch.WordTrace tailWord_1712 prefixEnd_1712 586052587068356994755 := by
  unfold tailWord_1712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31220884902595615715695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41627846536794154287593 31220884902595615715695)
  ·
    refine ⟨46831327353893423573543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31220884902595615715695 46831327353893423573543)
    ·
      refine ⟨70246991030840135360315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46831327353893423573543 70246991030840135360315)
      ·
        refine ⟨105370486546260203040473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70246991030840135360315 105370486546260203040473)
        ·
          refine ⟨79027864909695152280355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105370486546260203040473 79027864909695152280355)
          ·
            refine ⟨118541797364542728420533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79027864909695152280355 118541797364542728420533)
            ·
              refine ⟨11113293502925880789425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118541797364542728420533 11113293502925880789425)
              ·
                refine ⟨8334970127194410592069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11113293502925880789425 8334970127194410592069)
                ·
                  refine ⟨1562806898848951986013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8334970127194410592069 1562806898848951986013)
                  ·
                    refine ⟨586052587068356994755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562806898848951986013 586052587068356994755)
                    ·
                      rfl

theorem cell22_1712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_1712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712 prefixEnd_1712 := by exact prefixLift 1712
  have htrace : WordTrace (prefixWord ++ tailWord_1712) baseStart_1712 baseEnd_1712 := by
    simpa [prefixWord, tailWord_1712, baseEnd_1712] using wordTrace_append hprefix tailTrace_1712
  have hstable : (prefixWord ++ tailWord_1712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712).length < 2 ^ (prefixWord ++ tailWord_1712).sum := by decide
  have hdescent : baseEnd_1712 < baseStart_1712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714 : List Nat := [3, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_1714 : Nat := 118140960795 + 1714 * 2 ^ 59
def prefixEnd_1714 : Nat := 4983230072969 + 3 ^ 40 * 1714 * 2
def baseEnd_1714 : Nat := 195579075980339481583

theorem tailTrace_1714 : CollatzResearch.WordTrace tailWord_1714 prefixEnd_1714 195579075980339481583 := by
  unfold tailWord_1714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15628678949486393251049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41676477198630382002797 15628678949486393251049)
  ·
    refine ⟨11721509212114794938287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15628678949486393251049 11721509212114794938287)
    ·
      refine ⟨17582263818172192407431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11721509212114794938287 17582263818172192407431)
      ·
        refine ⟨26373395727258288611147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17582263818172192407431 26373395727258288611147)
        ·
          refine ⟨39560093590887432916721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26373395727258288611147 39560093590887432916721)
          ·
            refine ⟨29670070193165574687541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39560093590887432916721 29670070193165574687541)
            ·
              refine ⟨2781569080609272626957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29670070193165574687541 2781569080609272626957)
              ·
                refine ⟨1043088405228477235109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2781569080609272626957 1043088405228477235109)
                ·
                  refine ⟨195579075980339481583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043088405228477235109 195579075980339481583)
                  ·
                    rfl

theorem cell22_1714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_1714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714 prefixEnd_1714 := by exact prefixLift 1714
  have htrace : WordTrace (prefixWord ++ tailWord_1714) baseStart_1714 baseEnd_1714 := by
    simpa [prefixWord, tailWord_1714, baseEnd_1714] using wordTrace_append hprefix tailTrace_1714
  have hstable : (prefixWord ++ tailWord_1714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714).length < 2 ^ (prefixWord ++ tailWord_1714).sum := by decide
  have hdescent : baseEnd_1714 < baseStart_1714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 2, 4]
def baseStart_1727 : Nat := 118140960795 + 1727 * 2 ^ 59
def prefixEnd_1727 : Nat := 4983230072969 + 3 ^ 40 * 1727 * 2
def baseEnd_1727 : Nat := 591187393613317869709

theorem tailTrace_1727 : CollatzResearch.WordTrace tailWord_1727 prefixEnd_1727 591187393613317869709 := by
  unfold tailWord_1727
  simp only [CollatzResearch.WordTrace]
  refine ⟨62988864750848793227435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41992576500565862151623 62988864750848793227435)
  ·
    refine ⟨94483297126273189841153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62988864750848793227435 94483297126273189841153)
    ·
      refine ⟨70862472844704892380865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94483297126273189841153 70862472844704892380865)
      ·
        refine ⟨53146854633528669285649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70862472844704892380865 53146854633528669285649)
        ·
          refine ⟨39860140975146501964237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53146854633528669285649 39860140975146501964237)
          ·
            refine ⟨14947552865679938236589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39860140975146501964237 14947552865679938236589)
            ·
              refine ⟨5605332324629976838721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14947552865679938236589 5605332324629976838721)
              ·
                refine ⟨4203999243472482629041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5605332324629976838721 4203999243472482629041)
                ·
                  refine ⟨3152999432604361971781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4203999243472482629041 3152999432604361971781)
                  ·
                    refine ⟨591187393613317869709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3152999432604361971781 591187393613317869709)
                    ·
                      rfl

theorem cell22_1727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_1727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727 prefixEnd_1727 := by exact prefixLift 1727
  have htrace : WordTrace (prefixWord ++ tailWord_1727) baseStart_1727 baseEnd_1727 := by
    simpa [prefixWord, tailWord_1727, baseEnd_1727] using wordTrace_append hprefix tailTrace_1727
  have hstable : (prefixWord ++ tailWord_1727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727).length < 2 ^ (prefixWord ++ tailWord_1727).sum := by decide
  have hdescent : baseEnd_1727 < baseStart_1727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742 : List Nat := [4, 1, 1, 1, 3, 1, 4, 7]
def baseStart_1742 : Nat := 118140960795 + 1742 * 2 ^ 59
def prefixEnd_1742 : Nat := 4983230072969 + 3 ^ 40 * 1742 * 2
def baseEnd_1742 : Nat := 66258022239808749407

theorem tailTrace_1742 : CollatzResearch.WordTrace tailWord_1742 prefixEnd_1742 66258022239808749407 := by
  unfold tailWord_1742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941994962063294377935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42357306464337570015653 7941994962063294377935)
  ·
    refine ⟨11912992443094941566903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7941994962063294377935 11912992443094941566903)
    ·
      refine ⟨17869488664642412350355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11912992443094941566903 17869488664642412350355)
      ·
        refine ⟨26804232996963618525533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17869488664642412350355 26804232996963618525533)
        ·
          refine ⟨10051587373861356947075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26804232996963618525533 10051587373861356947075)
          ·
            refine ⟨15077381060792035420613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10051587373861356947075 15077381060792035420613)
            ·
              refine ⟨2827008948898506641365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15077381060792035420613 2827008948898506641365)
              ·
                refine ⟨66258022239808749407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2827008948898506641365 66258022239808749407)
                ·
                  rfl

theorem cell22_1742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_1742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742 prefixEnd_1742 := by exact prefixLift 1742
  have htrace : WordTrace (prefixWord ++ tailWord_1742) baseStart_1742 baseEnd_1742 := by
    simpa [prefixWord, tailWord_1742, baseEnd_1742] using wordTrace_append hprefix tailTrace_1742
  have hstable : (prefixWord ++ tailWord_1742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742).length < 2 ^ (prefixWord ++ tailWord_1742).sum := by decide
  have hdescent : baseEnd_1742 < baseStart_1742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_1746 : Nat := 118140960795 + 1746 * 2 ^ 59
def prefixEnd_1746 : Nat := 4983230072969 + 3 ^ 40 * 1746 * 2
def baseEnd_1746 : Nat := 597691481903601644651

theorem tailTrace_1746 : CollatzResearch.WordTrace tailWord_1746 prefixEnd_1746 597691481903601644651 := by
  unfold tailWord_1746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920462920503759542273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42454567788010025446061 15920462920503759542273)
  ·
    refine ⟨11940347190377819656705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15920462920503759542273 11940347190377819656705)
    ·
      refine ⟨8955260392783364742529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11940347190377819656705 8955260392783364742529)
      ·
        refine ⟨6716445294587523556897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8955260392783364742529 6716445294587523556897)
        ·
          refine ⟨5037333970940642667673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6716445294587523556897 5037333970940642667673)
          ·
            refine ⟨3778000478205482000755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5037333970940642667673 3778000478205482000755)
            ·
              refine ⟨5667000717308223001133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778000478205482000755 5667000717308223001133)
              ·
                refine ⟨2125125268990583625425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5667000717308223001133 2125125268990583625425)
                ·
                  refine ⟨1593843951742937719069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2125125268990583625425 1593843951742937719069)
                  ·
                    refine ⟨597691481903601644651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593843951742937719069 597691481903601644651)
                    ·
                      rfl

theorem cell22_1746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_1746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746 prefixEnd_1746 := by exact prefixLift 1746
  have htrace : WordTrace (prefixWord ++ tailWord_1746) baseStart_1746 baseEnd_1746 := by
    simpa [prefixWord, tailWord_1746, baseEnd_1746] using wordTrace_append hprefix tailTrace_1746
  have hstable : (prefixWord ++ tailWord_1746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746).length < 2 ^ (prefixWord ++ tailWord_1746).sum := by decide
  have hdescent : baseEnd_1746 < baseStart_1746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1750 : Nat := 118140960795 + 1750 * 2 ^ 59
def prefixEnd_1750 : Nat := 4983230072969 + 3 ^ 40 * 1750 * 2
def baseEnd_1750 : Nat := 599060763648924544639

theorem tailTrace_1750 : CollatzResearch.WordTrace tailWord_1750 prefixEnd_1750 599060763648924544639 := by
  unfold tailWord_1750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989233979220232582169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42551829111682480876469 3989233979220232582169)
  ·
    refine ⟨2991925484415174436627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3989233979220232582169 2991925484415174436627)
    ·
      refine ⟨4487888226622761654941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991925484415174436627 4487888226622761654941)
      ·
        refine ⟨1682958084983535620603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4487888226622761654941 1682958084983535620603)
        ·
          refine ⟨2524437127475303430905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682958084983535620603 2524437127475303430905)
          ·
            refine ⟨1893327845606477573179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2524437127475303430905 1893327845606477573179)
            ·
              refine ⟨2839991768409716359769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893327845606477573179 2839991768409716359769)
              ·
                refine ⟨2129993826307287269827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2839991768409716359769 2129993826307287269827)
                ·
                  refine ⟨3194990739460930904741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129993826307287269827 3194990739460930904741)
                  ·
                    refine ⟨599060763648924544639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194990739460930904741 599060763648924544639)
                    ·
                      rfl

theorem cell22_1750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750 prefixEnd_1750 := by exact prefixLift 1750
  have htrace : WordTrace (prefixWord ++ tailWord_1750) baseStart_1750 baseEnd_1750 := by
    simpa [prefixWord, tailWord_1750, baseEnd_1750] using wordTrace_append hprefix tailTrace_1750
  have hstable : (prefixWord ++ tailWord_1750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750).length < 2 ^ (prefixWord ++ tailWord_1750).sum := by decide
  have hdescent : baseEnd_1750 < baseStart_1750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1780 : Nat := 118140960795 + 1780 * 2 ^ 59
def prefixEnd_1780 : Nat := 4983230072969 + 3 ^ 40 * 1780 * 2
def baseEnd_1780 : Nat := 609330376738846294547

theorem tailTrace_1780 : CollatzResearch.WordTrace tailWord_1780 prefixEnd_1780 609330376738846294547 := by
  unfold tailWord_1780
  simp only [CollatzResearch.WordTrace]
  refine ⟨32460966779419422453397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43281289039225896604529 32460966779419422453397)
  ·
    refine ⟨1521607817785285427503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32460966779419422453397 1521607817785285427503)
    ·
      refine ⟨2282411726677928141255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521607817785285427503 2282411726677928141255)
      ·
        refine ⟨3423617590016892211883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282411726677928141255 3423617590016892211883)
        ·
          refine ⟨5135426385025338317825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423617590016892211883 5135426385025338317825)
          ·
            refine ⟨3851569788769003738369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5135426385025338317825 3851569788769003738369)
            ·
              refine ⟨2888677341576752803777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851569788769003738369 2888677341576752803777)
              ·
                refine ⟨2166508006182564602833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888677341576752803777 2166508006182564602833)
                ·
                  refine ⟨1624881004636923452125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166508006182564602833 1624881004636923452125)
                  ·
                    refine ⟨609330376738846294547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624881004636923452125 609330376738846294547)
                    ·
                      rfl

theorem cell22_1780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780 prefixEnd_1780 := by exact prefixLift 1780
  have htrace : WordTrace (prefixWord ++ tailWord_1780) baseStart_1780 baseEnd_1780 := by
    simpa [prefixWord, tailWord_1780, baseEnd_1780] using wordTrace_append hprefix tailTrace_1780
  have hstable : (prefixWord ++ tailWord_1780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780).length < 2 ^ (prefixWord ++ tailWord_1780).sum := by decide
  have hdescent : baseEnd_1780 < baseStart_1780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1802 : Nat := 118140960795 + 1802 * 2 ^ 59
def prefixEnd_1802 : Nat := 4983230072969 + 3 ^ 40 * 1802 * 2
def baseEnd_1802 : Nat := 616861426338122244479

theorem tailTrace_1802 : CollatzResearch.WordTrace tailWord_1802 prefixEnd_1802 616861426338122244479 := by
  unfold tailWord_1802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16431084869784150551915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43816226319424401471773 16431084869784150551915)
  ·
    refine ⟨24646627304676225827873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16431084869784150551915 24646627304676225827873)
    ·
      refine ⟨18484970478507169370905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24646627304676225827873 18484970478507169370905)
      ·
        refine ⟨13863727858880377028179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18484970478507169370905 13863727858880377028179)
        ·
          refine ⟨20795591788320565542269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13863727858880377028179 20795591788320565542269)
          ·
            refine ⟨7798346920620212078351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20795591788320565542269 7798346920620212078351)
            ·
              refine ⟨11697520380930318117527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7798346920620212078351 11697520380930318117527)
              ·
                refine ⟨17546280571395477176291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11697520380930318117527 17546280571395477176291)
                ·
                  refine ⟨26319420857093215764437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17546280571395477176291 26319420857093215764437)
                  ·
                    refine ⟨616861426338122244479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26319420857093215764437 616861426338122244479)
                    ·
                      rfl

theorem cell22_1802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1802 prefixEnd_1802 := by exact prefixLift 1802
  have htrace : WordTrace (prefixWord ++ tailWord_1802) baseStart_1802 baseEnd_1802 := by
    simpa [prefixWord, tailWord_1802, baseEnd_1802] using wordTrace_append hprefix tailTrace_1802
  have hstable : (prefixWord ++ tailWord_1802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802).length < 2 ^ (prefixWord ++ tailWord_1802).sum := by decide
  have hdescent : baseEnd_1802 < baseStart_1802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1812 : Nat := 118140960795 + 1812 * 2 ^ 59
def prefixEnd_1812 : Nat := 4983230072969 + 3 ^ 40 * 1812 * 2
def baseEnd_1812 : Nat := 620284630701429494449

theorem tailTrace_1812 : CollatzResearch.WordTrace tailWord_1812 prefixEnd_1812 620284630701429494449 := by
  unfold tailWord_1812
  simp only [CollatzResearch.WordTrace]
  refine ⟨33044534721454155035845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44059379628605540047793 33044534721454155035845)
  ·
    refine ⟨6195850260272654069221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33044534721454155035845 6195850260272654069221)
    ·
      refine ⟨1161721923801122637979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6195850260272654069221 1161721923801122637979)
      ·
        refine ⟨1742582885701683956969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161721923801122637979 1742582885701683956969)
        ·
          refine ⟨1306937164276262967727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1742582885701683956969 1306937164276262967727)
          ·
            refine ⟨1960405746414394451591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306937164276262967727 1960405746414394451591)
            ·
              refine ⟨2940608619621591677387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960405746414394451591 2940608619621591677387)
              ·
                refine ⟨4410912929432387516081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940608619621591677387 4410912929432387516081)
                ·
                  refine ⟨3308184697074290637061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4410912929432387516081 3308184697074290637061)
                  ·
                    refine ⟨620284630701429494449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3308184697074290637061 620284630701429494449)
                    ·
                      rfl

theorem cell22_1812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1812 prefixEnd_1812 := by exact prefixLift 1812
  have htrace : WordTrace (prefixWord ++ tailWord_1812) baseStart_1812 baseEnd_1812 := by
    simpa [prefixWord, tailWord_1812, baseEnd_1812] using wordTrace_append hprefix tailTrace_1812
  have hstable : (prefixWord ++ tailWord_1812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812).length < 2 ^ (prefixWord ++ tailWord_1812).sum := by decide
  have hdescent : baseEnd_1812 < baseStart_1812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1838 : Nat := 118140960795 + 1838 * 2 ^ 59
def prefixEnd_1838 : Nat := 4983230072969 + 3 ^ 40 * 1838 * 2
def baseEnd_1838 : Nat := 209728320682009448123

theorem tailTrace_1838 : CollatzResearch.WordTrace tailWord_1838 prefixEnd_1838 209728320682009448123 := by
  unfold tailWord_1838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379670918589343814771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44691578232476500345445 8379670918589343814771)
  ·
    refine ⟨12569506377884015722157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8379670918589343814771 12569506377884015722157)
    ·
      refine ⟨4713564891706505895809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12569506377884015722157 4713564891706505895809)
      ·
        refine ⟨3535173668779879421857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4713564891706505895809 3535173668779879421857)
        ·
          refine ⟨2651380251584909566393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535173668779879421857 2651380251584909566393)
          ·
            refine ⟨1988535188688682174795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2651380251584909566393 1988535188688682174795)
            ·
              refine ⟨2982802783033023262193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988535188688682174795 2982802783033023262193)
              ·
                refine ⟨2237102087274767446645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982802783033023262193 2237102087274767446645)
                ·
                  refine ⟨209728320682009448123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2237102087274767446645 209728320682009448123)
                  ·
                    rfl

theorem cell22_1838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838 prefixEnd_1838 := by exact prefixLift 1838
  have htrace : WordTrace (prefixWord ++ tailWord_1838) baseStart_1838 baseEnd_1838 := by
    simpa [prefixWord, tailWord_1838, baseEnd_1838] using wordTrace_append hprefix tailTrace_1838
  have hstable : (prefixWord ++ tailWord_1838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838).length < 2 ^ (prefixWord ++ tailWord_1838).sum := by decide
  have hdescent : baseEnd_1838 < baseStart_1838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1864 : Nat := 118140960795 + 1864 * 2 ^ 59
def prefixEnd_1864 : Nat := 4983230072969 + 3 ^ 40 * 1864 * 2
def baseEnd_1864 : Nat := 638085293390627194289

theorem tailTrace_1864 : CollatzResearch.WordTrace tailWord_1864 prefixEnd_1864 638085293390627194289 := by
  unfold tailWord_1864
  simp only [CollatzResearch.WordTrace]
  refine ⟨33992832627260595482323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45323776836347460643097 33992832627260595482323)
  ·
    refine ⟨50989248940890893223485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33992832627260595482323 50989248940890893223485)
    ·
      refine ⟨19120968352834084958807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50989248940890893223485 19120968352834084958807)
      ·
        refine ⟨28681452529251127438211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19120968352834084958807 28681452529251127438211)
        ·
          refine ⟨43022178793876691157317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28681452529251127438211 43022178793876691157317)
          ·
            refine ⟨8066658523851879591997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43022178793876691157317 8066658523851879591997)
            ·
              refine ⟨3024996946444454846999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8066658523851879591997 3024996946444454846999)
              ·
                refine ⟨4537495419666682270499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024996946444454846999 4537495419666682270499)
                ·
                  refine ⟨6806243129500023405749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537495419666682270499 6806243129500023405749)
                  ·
                    refine ⟨638085293390627194289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6806243129500023405749 638085293390627194289)
                    ·
                      rfl

theorem cell22_1864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864 prefixEnd_1864 := by exact prefixLift 1864
  have htrace : WordTrace (prefixWord ++ tailWord_1864) baseStart_1864 baseEnd_1864 := by
    simpa [prefixWord, tailWord_1864, baseEnd_1864] using wordTrace_append hprefix tailTrace_1864
  have hstable : (prefixWord ++ tailWord_1864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864).length < 2 ^ (prefixWord ++ tailWord_1864).sum := by decide
  have hdescent : baseEnd_1864 < baseStart_1864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 2, 6]
def baseStart_1907 : Nat := 118140960795 + 1907 * 2 ^ 59
def prefixEnd_1907 : Nat := 4983230072969 + 3 ^ 40 * 1907 * 2
def baseEnd_1907 : Nat := 652805072152848369157

theorem tailTrace_1907 : CollatzResearch.WordTrace tailWord_1907 prefixEnd_1907 652805072152848369157 := by
  unfold tailWord_1907
  simp only [CollatzResearch.WordTrace]
  refine ⟨69554004098739534779975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46369336065826356519983 69554004098739534779975)
  ·
    refine ⟨104331006148109302169963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69554004098739534779975 104331006148109302169963)
    ·
      refine ⟨156496509222163953254945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104331006148109302169963 156496509222163953254945)
      ·
        refine ⟨117372381916622964941209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156496509222163953254945 117372381916622964941209)
        ·
          refine ⟨88029286437467223705907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117372381916622964941209 88029286437467223705907)
          ·
            refine ⟨132043929656200835558861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88029286437467223705907 132043929656200835558861)
            ·
              refine ⟨49516473621075313334573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132043929656200835558861 49516473621075313334573)
              ·
                refine ⟨18568677607903242500465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49516473621075313334573 18568677607903242500465)
                ·
                  refine ⟨13926508205927431875349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18568677607903242500465 13926508205927431875349)
                  ·
                    refine ⟨652805072152848369157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13926508205927431875349 652805072152848369157)
                    ·
                      rfl

theorem cell22_1907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_1907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907 prefixEnd_1907 := by exact prefixLift 1907
  have htrace : WordTrace (prefixWord ++ tailWord_1907) baseStart_1907 baseEnd_1907 := by
    simpa [prefixWord, tailWord_1907, baseEnd_1907] using wordTrace_append hprefix tailTrace_1907
  have hstable : (prefixWord ++ tailWord_1907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907).length < 2 ^ (prefixWord ++ tailWord_1907).sum := by decide
  have hdescent : baseEnd_1907 < baseStart_1907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 5]
def baseStart_1956 : Nat := 118140960795 + 1956 * 2 ^ 59
def prefixEnd_1956 : Nat := 4983230072969 + 3 ^ 40 * 1956 * 2
def baseEnd_1956 : Nat := 223192924511017964669

theorem tailTrace_1956 : CollatzResearch.WordTrace tailWord_1956 prefixEnd_1956 223192924511017964669 := by
  unfold tailWord_1956
  simp only [CollatzResearch.WordTrace]
  refine ⟨35670590460610451656861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47560787280813935542481 35670590460610451656861)
  ·
    refine ⟨13376471422728919371323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35670590460610451656861 13376471422728919371323)
    ·
      refine ⟨20064707134093379056985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376471422728919371323 20064707134093379056985)
      ·
        refine ⟨15048530350570034292739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20064707134093379056985 15048530350570034292739)
        ·
          refine ⟨22572795525855051439109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15048530350570034292739 22572795525855051439109)
          ·
            refine ⟨4232399161097822144833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22572795525855051439109 4232399161097822144833)
            ·
              refine ⟨3174299370823366608625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232399161097822144833 3174299370823366608625)
              ·
                refine ⟨2380724528117524956469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174299370823366608625 2380724528117524956469)
                ·
                  refine ⟨223192924511017964669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380724528117524956469 223192924511017964669)
                  ·
                    rfl

theorem cell22_1956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_1956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1956 prefixEnd_1956 := by exact prefixLift 1956
  have htrace : WordTrace (prefixWord ++ tailWord_1956) baseStart_1956 baseEnd_1956 := by
    simpa [prefixWord, tailWord_1956, baseEnd_1956] using wordTrace_append hprefix tailTrace_1956
  have hstable : (prefixWord ++ tailWord_1956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956).length < 2 ^ (prefixWord ++ tailWord_1956).sum := by decide
  have hdescent : baseEnd_1956 < baseStart_1956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 6]
def baseStart_1984 : Nat := 118140960795 + 1984 * 2 ^ 59
def prefixEnd_1984 : Nat := 4983230072969 + 3 ^ 40 * 1984 * 2
def baseEnd_1984 : Nat := 226387915250104731307

theorem tailTrace_1984 : CollatzResearch.WordTrace tailWord_1984 prefixEnd_1984 226387915250104731307 := by
  unfold tailWord_1984
  simp only [CollatzResearch.WordTrace]
  refine ⟨36181212409890842666503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48241616546521123555337 36181212409890842666503)
  ·
    refine ⟨54271818614836263999755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36181212409890842666503 54271818614836263999755)
    ·
      refine ⟨81407727922254395999633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54271818614836263999755 81407727922254395999633)
      ·
        refine ⟨61055795941690796999725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81407727922254395999633 61055795941690796999725)
        ·
          refine ⟨22895923478134048874897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61055795941690796999725 22895923478134048874897)
          ·
            refine ⟨17171942608600536656173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22895923478134048874897 17171942608600536656173)
            ·
              refine ⟨6439478478225201246065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17171942608600536656173 6439478478225201246065)
              ·
                refine ⟨4829608858668900934549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439478478225201246065 4829608858668900934549)
                ·
                  refine ⟨226387915250104731307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4829608858668900934549 226387915250104731307)
                  ·
                    rfl

theorem cell22_1984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_1984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984 prefixEnd_1984 := by exact prefixLift 1984
  have htrace : WordTrace (prefixWord ++ tailWord_1984) baseStart_1984 baseEnd_1984 := by
    simpa [prefixWord, tailWord_1984, baseEnd_1984] using wordTrace_append hprefix tailTrace_1984
  have hstable : (prefixWord ++ tailWord_1984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984).length < 2 ^ (prefixWord ++ tailWord_1984).sum := by decide
  have hdescent : baseEnd_1984 < baseStart_1984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 1, 5]
def baseStart_1999 : Nat := 118140960795 + 1999 * 2 ^ 59
def prefixEnd_1999 : Nat := 4983230072969 + 3 ^ 40 * 1999 * 2
def baseEnd_1999 : Nat := 684298552295275068875

theorem tailTrace_1999 : CollatzResearch.WordTrace tailWord_1999 prefixEnd_1999 684298552295275068875 := by
  unfold tailWord_1999
  simp only [CollatzResearch.WordTrace]
  refine ⟨72909519765439247129051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48606346510292831419367 72909519765439247129051)
  ·
    refine ⟨109364279648158870693577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72909519765439247129051 109364279648158870693577)
    ·
      refine ⟨82023209736119153020183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109364279648158870693577 82023209736119153020183)
      ·
        refine ⟨123034814604178729530275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82023209736119153020183 123034814604178729530275)
        ·
          refine ⟨184552221906268094295413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123034814604178729530275 184552221906268094295413)
          ·
            refine ⟨17301770803712633840195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184552221906268094295413 17301770803712633840195)
            ·
              refine ⟨25952656205568950760293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17301770803712633840195 25952656205568950760293)
              ·
                refine ⟨4866123038544178267555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25952656205568950760293 4866123038544178267555)
                ·
                  refine ⟨7299184557816267401333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4866123038544178267555 7299184557816267401333)
                  ·
                    refine ⟨684298552295275068875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7299184557816267401333 684298552295275068875)
                    ·
                      rfl

theorem cell22_1999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_1999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999 prefixEnd_1999 := by exact prefixLift 1999
  have htrace : WordTrace (prefixWord ++ tailWord_1999) baseStart_1999 baseEnd_1999 := by
    simpa [prefixWord, tailWord_1999, baseEnd_1999] using wordTrace_append hprefix tailTrace_1999
  have hstable : (prefixWord ++ tailWord_1999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999).length < 2 ^ (prefixWord ++ tailWord_1999).sum := by decide
  have hdescent : baseEnd_1999 < baseStart_1999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 1, 5]
def baseStart_2033 : Nat := 118140960795 + 2033 * 2 ^ 59
def prefixEnd_2033 : Nat := 4983230072969 + 3 ^ 40 * 2033 * 2
def baseEnd_2033 : Nat := 695937447130519718771

theorem tailTrace_2033 : CollatzResearch.WordTrace tailWord_2033 prefixEnd_2033 695937447130519718771 := by
  unfold tailWord_2033
  simp only [CollatzResearch.WordTrace]
  refine ⟨74149601642263053866753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49433067761508702577835 74149601642263053866753)
  ·
    refine ⟨55612201231697290400065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74149601642263053866753 55612201231697290400065)
    ·
      refine ⟨41709150923772967800049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55612201231697290400065 41709150923772967800049)
      ·
        refine ⟨31281863192829725850037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41709150923772967800049 31281863192829725850037)
        ·
          refine ⟨2932674674327786798441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31281863192829725850037 2932674674327786798441)
          ·
            refine ⟨2199506005745840098831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2932674674327786798441 2199506005745840098831)
            ·
              refine ⟨3299259008618760148247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199506005745840098831 3299259008618760148247)
              ·
                refine ⟨4948888512928140222371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299259008618760148247 4948888512928140222371)
                ·
                  refine ⟨7423332769392210333557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948888512928140222371 7423332769392210333557)
                  ·
                    refine ⟨695937447130519718771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7423332769392210333557 695937447130519718771)
                    ·
                      rfl

theorem cell22_2033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_2033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033 prefixEnd_2033 := by exact prefixLift 2033
  have htrace : WordTrace (prefixWord ++ tailWord_2033) baseStart_2033 baseEnd_2033 := by
    simpa [prefixWord, tailWord_2033, baseEnd_2033] using wordTrace_append hprefix tailTrace_2033
  have hstable : (prefixWord ++ tailWord_2033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033).length < 2 ^ (prefixWord ++ tailWord_2033).sum := by decide
  have hdescent : baseEnd_2033 < baseStart_2033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2044 : Nat := 118140960795 + 2044 * 2 ^ 59
def prefixEnd_2044 : Nat := 4983230072969 + 3 ^ 40 * 2044 * 2
def baseEnd_2044 : Nat := 699702971930157693737

theorem tailTrace_2044 : CollatzResearch.WordTrace tailWord_2044 prefixEnd_2044 699702971930157693737 := by
  unfold tailWord_2044
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275402301205966258593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49700536401607955011457 37275402301205966258593)
  ·
    refine ⟨27956551725904474693945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37275402301205966258593 27956551725904474693945)
    ·
      refine ⟨20967413794428356020459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27956551725904474693945 20967413794428356020459)
      ·
        refine ⟨31451120691642534030689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20967413794428356020459 31451120691642534030689)
        ·
          refine ⟨23588340518731900523017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31451120691642534030689 23588340518731900523017)
          ·
            refine ⟨17691255389048925392263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23588340518731900523017 17691255389048925392263)
            ·
              refine ⟨26536883083573388088395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17691255389048925392263 26536883083573388088395)
              ·
                refine ⟨39805324625360082132593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26536883083573388088395 39805324625360082132593)
                ·
                  refine ⟨29853993469020061599445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39805324625360082132593 29853993469020061599445)
                  ·
                    refine ⟨699702971930157693737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29853993469020061599445 699702971930157693737)
                    ·
                      rfl

theorem cell22_2044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044 prefixEnd_2044 := by exact prefixLift 2044
  have htrace : WordTrace (prefixWord ++ tailWord_2044) baseStart_2044 baseEnd_2044 := by
    simpa [prefixWord, tailWord_2044, baseEnd_2044] using wordTrace_append hprefix tailTrace_2044
  have hstable : (prefixWord ++ tailWord_2044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044).length < 2 ^ (prefixWord ++ tailWord_2044).sum := by decide
  have hdescent : baseEnd_2044 < baseStart_2044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052 : List Nat := [2, 3, 2, 4, 1, 2, 1, 3, 4]
def baseStart_2052 : Nat := 118140960795 + 2052 * 2 ^ 59
def prefixEnd_2052 : Nat := 4983230072969 + 3 ^ 40 * 2052 * 2
def baseEnd_2052 : Nat := 234147178473601164571

theorem tailTrace_2052 : CollatzResearch.WordTrace tailWord_2052 prefixEnd_2052 234147178473601164571 := by
  unfold tailWord_2052
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421294286714649404205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49895059048952865872273 37421294286714649404205)
  ·
    refine ⟨14032985357517993526577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37421294286714649404205 14032985357517993526577)
    ·
      refine ⟨10524739018138495144933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14032985357517993526577 10524739018138495144933)
      ·
        refine ⟨1973388565900967839675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10524739018138495144933 1973388565900967839675)
        ·
          refine ⟨2960082848851451759513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973388565900967839675 2960082848851451759513)
          ·
            refine ⟨2220062136638588819635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960082848851451759513 2220062136638588819635)
            ·
              refine ⟨3330093204957883229453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220062136638588819635 3330093204957883229453)
              ·
                refine ⟨1248784951859206211045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3330093204957883229453 1248784951859206211045)
                ·
                  refine ⟨234147178473601164571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248784951859206211045 234147178473601164571)
                  ·
                    rfl

theorem cell22_2052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_2052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2052 prefixEnd_2052 := by exact prefixLift 2052
  have htrace : WordTrace (prefixWord ++ tailWord_2052) baseStart_2052 baseEnd_2052 := by
    simpa [prefixWord, tailWord_2052, baseEnd_2052] using wordTrace_append hprefix tailTrace_2052
  have hstable : (prefixWord ++ tailWord_2052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052).length < 2 ^ (prefixWord ++ tailWord_2052).sum := by decide
  have hdescent : baseEnd_2052 < baseStart_2052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_2084 : Nat := 118140960795 + 2084 * 2 ^ 59
def prefixEnd_2084 : Nat := 4983230072969 + 3 ^ 40 * 2084 * 2
def baseEnd_2084 : Nat := 713395789383386693615

theorem tailTrace_2084 : CollatzResearch.WordTrace tailWord_2084 prefixEnd_2084 713395789383386693615 := by
  unfold tailWord_2084
  simp only [CollatzResearch.WordTrace]
  refine ⟨38004862228749381986653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50673149638332509315537 38004862228749381986653)
  ·
    refine ⟨14251823335781018244995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38004862228749381986653 14251823335781018244995)
    ·
      refine ⟨21377735003671527367493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14251823335781018244995 21377735003671527367493)
      ·
        refine ⟨4008325313188411381405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21377735003671527367493 4008325313188411381405)
        ·
          refine ⟨1503121992445654268027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4008325313188411381405 1503121992445654268027)
          ·
            refine ⟨2254682988668481402041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503121992445654268027 2254682988668481402041)
            ·
              refine ⟨1691012241501361051531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2254682988668481402041 1691012241501361051531)
              ·
                refine ⟨2536518362252041577297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691012241501361051531 2536518362252041577297)
                ·
                  refine ⟨1902388771689031182973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2536518362252041577297 1902388771689031182973)
                  ·
                    refine ⟨713395789383386693615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902388771689031182973 713395789383386693615)
                    ·
                      rfl

theorem cell22_2084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_2084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084 prefixEnd_2084 := by exact prefixLift 2084
  have htrace : WordTrace (prefixWord ++ tailWord_2084) baseStart_2084 baseEnd_2084 := by
    simpa [prefixWord, tailWord_2084, baseEnd_2084] using wordTrace_append hprefix tailTrace_2084
  have hstable : (prefixWord ++ tailWord_2084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084).length < 2 ^ (prefixWord ++ tailWord_2084).sum := by decide
  have hdescent : baseEnd_2084 < baseStart_2084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_2089 : Nat := 118140960795 + 2089 * 2 ^ 59
def prefixEnd_2089 : Nat := 4983230072969 + 3 ^ 40 * 2089 * 2
def baseEnd_2089 : Nat := 715107391565040318599

theorem tailTrace_2089 : CollatzResearch.WordTrace tailWord_2089 prefixEnd_2089 715107391565040318599 := by
  unfold tailWord_2089
  simp only [CollatzResearch.WordTrace]
  refine ⟨76192089439384617905321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50794726292923078603547 76192089439384617905321)
  ·
    refine ⟨57144067079538463428991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76192089439384617905321 57144067079538463428991)
    ·
      refine ⟨85716100619307695143487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57144067079538463428991 85716100619307695143487)
      ·
        refine ⟨128574150928961542715231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85716100619307695143487 128574150928961542715231)
        ·
          refine ⟨192861226393442314072847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128574150928961542715231 192861226393442314072847)
          ·
            refine ⟨289291839590163471109271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192861226393442314072847 289291839590163471109271)
            ·
              refine ⟨433937759385245206663907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289291839590163471109271 433937759385245206663907)
              ·
                refine ⟨650906639077867809995861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433937759385245206663907 650906639077867809995861)
                ·
                  refine ⟨7627812176693763398389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 650906639077867809995861 7627812176693763398389)
                  ·
                    refine ⟨715107391565040318599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7627812176693763398389 715107391565040318599)
                    ·
                      rfl

theorem cell22_2089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_2089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2089 prefixEnd_2089 := by exact prefixLift 2089
  have htrace : WordTrace (prefixWord ++ tailWord_2089) baseStart_2089 baseEnd_2089 := by
    simpa [prefixWord, tailWord_2089, baseEnd_2089] using wordTrace_append hprefix tailTrace_2089
  have hstable : (prefixWord ++ tailWord_2089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089).length < 2 ^ (prefixWord ++ tailWord_2089).sum := by decide
  have hdescent : baseEnd_2089 < baseStart_2089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181 : List Nat := [1, 3, 1, 1, 5, 2, 9]
def baseStart_2181 : Nat := 118140960795 + 2181 * 2 ^ 59
def prefixEnd_2181 : Nat := 4983230072969 + 3 ^ 40 * 2181 * 2
def baseEnd_2181 : Nat := 27651884137313593271

theorem tailTrace_2181 : CollatzResearch.WordTrace tailWord_2181 prefixEnd_2181 27651884137313593271 := by
  unfold tailWord_2181
  simp only [CollatzResearch.WordTrace]
  refine ⟨79547605106084330254397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53031736737389553502931 79547605106084330254397)
  ·
    refine ⟨29830351914781623845399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79547605106084330254397 29830351914781623845399)
    ·
      refine ⟨44745527872172435768099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29830351914781623845399 44745527872172435768099)
      ·
        refine ⟨67118291808258653652149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44745527872172435768099 67118291808258653652149)
        ·
          refine ⟨6292339857024248779889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67118291808258653652149 6292339857024248779889)
          ·
            refine ⟨4719254892768186584917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6292339857024248779889 4719254892768186584917)
            ·
              refine ⟨27651884137313593271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4719254892768186584917 27651884137313593271)
              ·
                rfl

theorem cell22_2181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 9].length) (baseStart_2181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181 prefixEnd_2181 := by exact prefixLift 2181
  have htrace : WordTrace (prefixWord ++ tailWord_2181) baseStart_2181 baseEnd_2181 := by
    simpa [prefixWord, tailWord_2181, baseEnd_2181] using wordTrace_append hprefix tailTrace_2181
  have hstable : (prefixWord ++ tailWord_2181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181).length < 2 ^ (prefixWord ++ tailWord_2181).sum := by decide
  have hdescent : baseEnd_2181 < baseStart_2181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_2202 : Nat := 118140960795 + 2202 * 2 ^ 59
def prefixEnd_2202 : Nat := 4983230072969 + 3 ^ 40 * 2202 * 2
def baseEnd_2202 : Nat := 753789600870412243253

theorem tailTrace_2202 : CollatzResearch.WordTrace tailWord_2202 prefixEnd_2202 753789600870412243253 := by
  unfold tailWord_2202
  simp only [CollatzResearch.WordTrace]
  refine ⟨20078384507501229192215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53542358686669944512573 20078384507501229192215)
  ·
    refine ⟨30117576761251843788323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20078384507501229192215 30117576761251843788323)
    ·
      refine ⟨45176365141877765682485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30117576761251843788323 45176365141877765682485)
      ·
        refine ⟨4235284232051040532733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45176365141877765682485 4235284232051040532733)
        ·
          refine ⟨1588231587019140199775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4235284232051040532733 1588231587019140199775)
          ·
            refine ⟨2382347380528710299663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588231587019140199775 2382347380528710299663)
            ·
              refine ⟨3573521070793065449495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382347380528710299663 3573521070793065449495)
              ·
                refine ⟨5360281606189598174243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573521070793065449495 5360281606189598174243)
                ·
                  refine ⟨8040422409284397261365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360281606189598174243 8040422409284397261365)
                  ·
                    refine ⟨753789600870412243253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8040422409284397261365 753789600870412243253)
                    ·
                      rfl

theorem cell22_2202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_2202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2202 prefixEnd_2202 := by exact prefixLift 2202
  have htrace : WordTrace (prefixWord ++ tailWord_2202) baseStart_2202 baseEnd_2202 := by
    simpa [prefixWord, tailWord_2202, baseEnd_2202] using wordTrace_append hprefix tailTrace_2202
  have hstable : (prefixWord ++ tailWord_2202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202).length < 2 ^ (prefixWord ++ tailWord_2202).sum := by decide
  have hdescent : baseEnd_2202 < baseStart_2202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_2213 : Nat := 118140960795 + 2213 * 2 ^ 59
def prefixEnd_2213 : Nat := 4983230072969 + 3 ^ 40 * 2213 * 2
def baseEnd_2213 : Nat := 757555125670050218219

theorem tailTrace_2213 : CollatzResearch.WordTrace tailWord_2213 prefixEnd_2213 757555125670050218219 := by
  unfold tailWord_2213
  simp only [CollatzResearch.WordTrace]
  refine ⟨80714740990153795419293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53809827326769196946195 80714740990153795419293)
  ·
    refine ⟨30268027871307673282235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80714740990153795419293 30268027871307673282235)
    ·
      refine ⟨45402041806961509923353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30268027871307673282235 45402041806961509923353)
      ·
        refine ⟨34051531355221132442515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45402041806961509923353 34051531355221132442515)
        ·
          refine ⟨51077297032831698663773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34051531355221132442515 51077297032831698663773)
          ·
            refine ⟨19153986387311886998915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51077297032831698663773 19153986387311886998915)
            ·
              refine ⟨28730979580967830498373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19153986387311886998915 28730979580967830498373)
              ·
                refine ⟨5387058671431468218445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28730979580967830498373 5387058671431468218445)
                ·
                  refine ⟨2020147001786800581917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5387058671431468218445 2020147001786800581917)
                  ·
                    refine ⟨757555125670050218219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020147001786800581917 757555125670050218219)
                    ·
                      rfl

theorem cell22_2213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_2213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213 prefixEnd_2213 := by exact prefixLift 2213
  have htrace : WordTrace (prefixWord ++ tailWord_2213) baseStart_2213 baseEnd_2213 := by
    simpa [prefixWord, tailWord_2213, baseEnd_2213] using wordTrace_append hprefix tailTrace_2213
  have hstable : (prefixWord ++ tailWord_2213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213).length < 2 ^ (prefixWord ++ tailWord_2213).sum := by decide
  have hdescent : baseEnd_2213 < baseStart_2213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_2226 : Nat := 118140960795 + 2226 * 2 ^ 59
def prefixEnd_2226 : Nat := 4983230072969 + 3 ^ 40 * 2226 * 2
def baseEnd_2226 : Nat := 254001763780783214393

theorem tailTrace_2226 : CollatzResearch.WordTrace tailWord_2226 prefixEnd_2226 254001763780783214393 := by
  unfold tailWord_2226
  simp only [CollatzResearch.WordTrace]
  refine ⟨20297222485764253910633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54125926628704677095021 20297222485764253910633)
  ·
    refine ⟨15222916864323190432975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20297222485764253910633 15222916864323190432975)
    ·
      refine ⟨22834375296484785649463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15222916864323190432975 22834375296484785649463)
      ·
        refine ⟨34251562944727178474195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22834375296484785649463 34251562944727178474195)
        ·
          refine ⟨51377344417090767711293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34251562944727178474195 51377344417090767711293)
          ·
            refine ⟨19266504156409037891735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51377344417090767711293 19266504156409037891735)
            ·
              refine ⟨28899756234613556837603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19266504156409037891735 28899756234613556837603)
              ·
                refine ⟨43349634351920335256405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28899756234613556837603 43349634351920335256405)
                ·
                  refine ⟨254001763780783214393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43349634351920335256405 254001763780783214393)
                  ·
                    rfl

theorem cell22_2226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_2226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226 prefixEnd_2226 := by exact prefixLift 2226
  have htrace : WordTrace (prefixWord ++ tailWord_2226) baseStart_2226 baseEnd_2226 := by
    simpa [prefixWord, tailWord_2226, baseEnd_2226] using wordTrace_append hprefix tailTrace_2226
  have hstable : (prefixWord ++ tailWord_2226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226).length < 2 ^ (prefixWord ++ tailWord_2226).sum := by decide
  have hdescent : baseEnd_2226 < baseStart_2226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 8]
def baseStart_2271 : Nat := 118140960795 + 2271 * 2 ^ 59
def prefixEnd_2271 : Nat := 4983230072969 + 3 ^ 40 * 2271 * 2
def baseEnd_2271 : Nat := 259136570325744089347

theorem tailTrace_2271 : CollatzResearch.WordTrace tailWord_2271 prefixEnd_2271 259136570325744089347 := by
  unfold tailWord_2271
  simp only [CollatzResearch.WordTrace]
  refine ⟨82830174780029701030667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55220116520019800687111 82830174780029701030667)
  ·
    refine ⟨124245262170044551546001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82830174780029701030667 124245262170044551546001)
    ·
      refine ⟨93183946627533413659501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124245262170044551546001 93183946627533413659501)
      ·
        refine ⟨34943979985325030122313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93183946627533413659501 34943979985325030122313)
        ·
          refine ⟨26207984988993772591735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34943979985325030122313 26207984988993772591735)
          ·
            refine ⟨39311977483490658887603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26207984988993772591735 39311977483490658887603)
            ·
              refine ⟨58967966225235988331405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39311977483490658887603 58967966225235988331405)
              ·
                refine ⟨22112987334463495624277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58967966225235988331405 22112987334463495624277)
                ·
                  refine ⟨259136570325744089347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22112987334463495624277 259136570325744089347)
                  ·
                    rfl

theorem cell22_2271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 8].length) (baseStart_2271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271 prefixEnd_2271 := by exact prefixLift 2271
  have htrace : WordTrace (prefixWord ++ tailWord_2271) baseStart_2271 baseEnd_2271 := by
    simpa [prefixWord, tailWord_2271, baseEnd_2271] using wordTrace_append hprefix tailTrace_2271
  have hstable : (prefixWord ++ tailWord_2271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271).length < 2 ^ (prefixWord ++ tailWord_2271).sum := by decide
  have hdescent : baseEnd_2271 < baseStart_2271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_2273 : Nat := 118140960795 + 2273 * 2 ^ 59
def prefixEnd_2273 : Nat := 4983230072969 + 3 ^ 40 * 2273 * 2
def baseEnd_2273 : Nat := 778094351849893718035

theorem tailTrace_2273 : CollatzResearch.WordTrace tailWord_2273 prefixEnd_2273 778094351849893718035 := by
  unfold tailWord_2273
  simp only [CollatzResearch.WordTrace]
  refine ⟨82903120772784042603473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55268747181856028402315 82903120772784042603473)
  ·
    refine ⟨62177340579588031952605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82903120772784042603473 62177340579588031952605)
    ·
      refine ⟨23316502717345511982227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62177340579588031952605 23316502717345511982227)
      ·
        refine ⟨34974754076018267973341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23316502717345511982227 34974754076018267973341)
        ·
          refine ⟨13115532778506850490003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34974754076018267973341 13115532778506850490003)
          ·
            refine ⟨19673299167760275735005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13115532778506850490003 19673299167760275735005)
            ·
              refine ⟨7377487187910103400627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19673299167760275735005 7377487187910103400627)
              ·
                refine ⟨11066230781865155100941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7377487187910103400627 11066230781865155100941)
                ·
                  refine ⟨4149836543199433162853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11066230781865155100941 4149836543199433162853)
                  ·
                    refine ⟨778094351849893718035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149836543199433162853 778094351849893718035)
                    ·
                      rfl

theorem cell22_2273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_2273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273 prefixEnd_2273 := by exact prefixLift 2273
  have htrace : WordTrace (prefixWord ++ tailWord_2273) baseStart_2273 baseEnd_2273 := by
    simpa [prefixWord, tailWord_2273, baseEnd_2273] using wordTrace_append hprefix tailTrace_2273
  have hstable : (prefixWord ++ tailWord_2273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273).length < 2 ^ (prefixWord ++ tailWord_2273).sum := by decide
  have hdescent : baseEnd_2273 < baseStart_2273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2305 : List Nat := [1, 2, 4, 1, 1, 2, 3, 4, 4]
def baseStart_2305 : Nat := 118140960795 + 2305 * 2 ^ 59
def prefixEnd_2305 : Nat := 4983230072969 + 3 ^ 40 * 2305 * 2
def baseEnd_2305 : Nat := 263016201937492305979

theorem tailTrace_2305 : CollatzResearch.WordTrace tailWord_2305 prefixEnd_2305 263016201937492305979 := by
  unfold tailWord_2305
  simp only [CollatzResearch.WordTrace]
  refine ⟨84070256656853507768369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56046837771235671845579 84070256656853507768369)
  ·
    refine ⟨63052692492640130826277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84070256656853507768369 63052692492640130826277)
    ·
      refine ⟨11822379842370024529927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63052692492640130826277 11822379842370024529927)
      ·
        refine ⟨17733569763555036794891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11822379842370024529927 17733569763555036794891)
        ·
          refine ⟨26600354645332555192337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17733569763555036794891 26600354645332555192337)
          ·
            refine ⟨19950265983999416394253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26600354645332555192337 19950265983999416394253)
            ·
              refine ⟨7481349743999781147845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19950265983999416394253 7481349743999781147845)
              ·
                refine ⟨1402753076999958965221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7481349743999781147845 1402753076999958965221)
                ·
                  refine ⟨263016201937492305979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402753076999958965221 263016201937492305979)
                  ·
                    rfl

theorem cell22_2305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_2305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2305 prefixEnd_2305 := by exact prefixLift 2305
  have htrace : WordTrace (prefixWord ++ tailWord_2305) baseStart_2305 baseEnd_2305 := by
    simpa [prefixWord, tailWord_2305, baseEnd_2305] using wordTrace_append hprefix tailTrace_2305
  have hstable : (prefixWord ++ tailWord_2305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2305).length < 2 ^ (prefixWord ++ tailWord_2305).sum := by decide
  have hdescent : baseEnd_2305 < baseStart_2305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_2318 : Nat := 118140960795 + 2318 * 2 ^ 59
def prefixEnd_2318 : Nat := 4983230072969 + 3 ^ 40 * 2318 * 2
def baseEnd_2318 : Nat := 793498771484776342897

theorem tailTrace_2318 : CollatzResearch.WordTrace tailWord_2318 prefixEnd_2318 793498771484776342897 := by
  unfold tailWord_2318
  simp only [CollatzResearch.WordTrace]
  refine ⟨10568050701219590998951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56362937073171151994405 10568050701219590998951)
  ·
    refine ⟨15852076051829386498427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10568050701219590998951 15852076051829386498427)
    ·
      refine ⟨23778114077744079747641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15852076051829386498427 23778114077744079747641)
      ·
        refine ⟨17833585558308059810731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23778114077744079747641 17833585558308059810731)
        ·
          refine ⟨26750378337462089716097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17833585558308059810731 26750378337462089716097)
          ·
            refine ⟨20062783753096567287073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26750378337462089716097 20062783753096567287073)
            ·
              refine ⟨15047087814822425465305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20062783753096567287073 15047087814822425465305)
              ·
                refine ⟨11285315861116819098979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15047087814822425465305 11285315861116819098979)
                ·
                  refine ⟨16927973791675228648469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11285315861116819098979 16927973791675228648469)
                  ·
                    refine ⟨793498771484776342897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16927973791675228648469 793498771484776342897)
                    ·
                      rfl

theorem cell22_2318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_2318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318 prefixEnd_2318 := by exact prefixLift 2318
  have htrace : WordTrace (prefixWord ++ tailWord_2318) baseStart_2318 baseEnd_2318 := by
    simpa [prefixWord, tailWord_2318, baseEnd_2318] using wordTrace_append hprefix tailTrace_2318
  have hstable : (prefixWord ++ tailWord_2318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318).length < 2 ^ (prefixWord ++ tailWord_2318).sum := by decide
  have hdescent : baseEnd_2318 < baseStart_2318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 2, 4]
def baseStart_2335 : Nat := 118140960795 + 2335 * 2 ^ 59
def prefixEnd_2335 : Nat := 4983230072969 + 3 ^ 40 * 2335 * 2
def baseEnd_2335 : Nat := 799318218902398667845

theorem tailTrace_2335 : CollatzResearch.WordTrace tailWord_2335 prefixEnd_2335 799318218902398667845 := by
  unfold tailWord_2335
  simp only [CollatzResearch.WordTrace]
  refine ⟨85164446548168631360459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56776297698779087573639 85164446548168631360459)
  ·
    refine ⟨127746669822252947040689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85164446548168631360459 127746669822252947040689)
    ·
      refine ⟨95810002366689710280517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127746669822252947040689 95810002366689710280517)
      ·
        refine ⟨17964375443754320677597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95810002366689710280517 17964375443754320677597)
        ·
          refine ⟨6736640791407870254099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17964375443754320677597 6736640791407870254099)
          ·
            refine ⟨10104961187111805381149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736640791407870254099 10104961187111805381149)
            ·
              refine ⟨3789360445166927017931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10104961187111805381149 3789360445166927017931)
              ·
                refine ⟨5684040667750390526897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789360445166927017931 5684040667750390526897)
                ·
                  refine ⟨4263030500812792895173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5684040667750390526897 4263030500812792895173)
                  ·
                    refine ⟨799318218902398667845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4263030500812792895173 799318218902398667845)
                    ·
                      rfl

theorem cell22_2335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_2335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335 prefixEnd_2335 := by exact prefixLift 2335
  have htrace : WordTrace (prefixWord ++ tailWord_2335) baseStart_2335 baseEnd_2335 := by
    simpa [prefixWord, tailWord_2335, baseEnd_2335] using wordTrace_append hprefix tailTrace_2335
  have hstable : (prefixWord ++ tailWord_2335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335).length < 2 ^ (prefixWord ++ tailWord_2335).sum := by decide
  have hdescent : baseEnd_2335 < baseStart_2335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_2354 : Nat := 118140960795 + 2354 * 2 ^ 59
def prefixEnd_2354 : Nat := 4983230072969 + 3 ^ 40 * 2354 * 2
def baseEnd_2354 : Nat := 805822307192682442787

theorem tailTrace_2354 : CollatzResearch.WordTrace tailWord_2354 prefixEnd_2354 805822307192682442787 := by
  unfold tailWord_2354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21464358369833719075529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57238288986223250868077 21464358369833719075529)
  ·
    refine ⟨16098268777375289306647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21464358369833719075529 16098268777375289306647)
    ·
      refine ⟨24147403166062933959971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16098268777375289306647 24147403166062933959971)
      ·
        refine ⟨36221104749094400939957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24147403166062933959971 36221104749094400939957)
        ·
          refine ⟨3395728570227600088121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36221104749094400939957 3395728570227600088121)
          ·
            refine ⟨2546796427670700066091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3395728570227600088121 2546796427670700066091)
            ·
              refine ⟨3820194641506050099137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546796427670700066091 3820194641506050099137)
              ·
                refine ⟨2865145981129537574353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3820194641506050099137 2865145981129537574353)
                ·
                  refine ⟨2148859485847153180765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2865145981129537574353 2148859485847153180765)
                  ·
                    refine ⟨805822307192682442787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148859485847153180765 805822307192682442787)
                    ·
                      rfl

theorem cell22_2354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_2354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354 prefixEnd_2354 := by exact prefixLift 2354
  have htrace : WordTrace (prefixWord ++ tailWord_2354) baseStart_2354 baseEnd_2354 := by
    simpa [prefixWord, tailWord_2354, baseEnd_2354] using wordTrace_append hprefix tailTrace_2354
  have hstable : (prefixWord ++ tailWord_2354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354).length < 2 ^ (prefixWord ++ tailWord_2354).sum := by decide
  have hdescent : baseEnd_2354 < baseStart_2354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 6]
def baseStart_2423 : Nat := 118140960795 + 2423 * 2 ^ 59
def prefixEnd_2423 : Nat := 4983230072969 + 3 ^ 40 * 2423 * 2
def baseEnd_2423 : Nat := 276480805766500822525

theorem tailTrace_2423 : CollatzResearch.WordTrace tailWord_2423 prefixEnd_2423 276480805766500822525 := by
  unfold tailWord_2423
  simp only [CollatzResearch.WordTrace]
  refine ⟨88374070229359660563923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58916046819573107042615 88374070229359660563923)
  ·
    refine ⟨132561105344039490845885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88374070229359660563923 132561105344039490845885)
    ·
      refine ⟨49710414504014809067207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132561105344039490845885 49710414504014809067207)
      ·
        refine ⟨74565621756022213600811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49710414504014809067207 74565621756022213600811)
        ·
          refine ⟨111848432634033320401217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74565621756022213600811 111848432634033320401217)
          ·
            refine ⟨83886324475524990300913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111848432634033320401217 83886324475524990300913)
            ·
              refine ⟨62914743356643742725685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83886324475524990300913 62914743356643742725685)
              ·
                refine ⟨5898257189685350880533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62914743356643742725685 5898257189685350880533)
                ·
                  refine ⟨276480805766500822525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5898257189685350880533 276480805766500822525)
                  ·
                    rfl

theorem cell22_2423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 6].length) (baseStart_2423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423 prefixEnd_2423 := by exact prefixLift 2423
  have htrace : WordTrace (prefixWord ++ tailWord_2423) baseStart_2423 baseEnd_2423 := by
    simpa [prefixWord, tailWord_2423, baseEnd_2423] using wordTrace_append hprefix tailTrace_2423
  have hstable : (prefixWord ++ tailWord_2423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423).length < 2 ^ (prefixWord ++ tailWord_2423).sum := by decide
  have hdescent : baseEnd_2423 < baseStart_2423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 6, 3]
def baseStart_2455 : Nat := 118140960795 + 2455 * 2 ^ 59
def prefixEnd_2455 : Nat := 4983230072969 + 3 ^ 40 * 2455 * 2
def baseEnd_2455 : Nat := 840396671262085667477

theorem tailTrace_2455 : CollatzResearch.WordTrace tailWord_2455 prefixEnd_2455 840396671262085667477 := by
  unfold tailWord_2455
  simp only [CollatzResearch.WordTrace]
  refine ⟨89541206113429125728819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59694137408952750485879 89541206113429125728819)
  ·
    refine ⟨134311809170143688593229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89541206113429125728819 134311809170143688593229)
    ·
      refine ⟨50366928438803883222461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134311809170143688593229 50366928438803883222461)
      ·
        refine ⟨18887598164551456208423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50366928438803883222461 18887598164551456208423)
        ·
          refine ⟨28331397246827184312635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18887598164551456208423 28331397246827184312635)
          ·
            refine ⟨42497095870240776468953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28331397246827184312635 42497095870240776468953)
            ·
              refine ⟨31872821902680582351715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42497095870240776468953 31872821902680582351715)
              ·
                refine ⟨47809232854020873527573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31872821902680582351715 47809232854020873527573)
                ·
                  refine ⟨2241057790032228446605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47809232854020873527573 2241057790032228446605)
                  ·
                    refine ⟨840396671262085667477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241057790032228446605 840396671262085667477)
                    ·
                      rfl

theorem cell22_2455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_2455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455 prefixEnd_2455 := by exact prefixLift 2455
  have htrace : WordTrace (prefixWord ++ tailWord_2455) baseStart_2455 baseEnd_2455 := by
    simpa [prefixWord, tailWord_2455, baseEnd_2455] using wordTrace_append hprefix tailTrace_2455
  have hstable : (prefixWord ++ tailWord_2455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455).length < 2 ^ (prefixWord ++ tailWord_2455).sum := by decide
  have hdescent : baseEnd_2455 < baseStart_2455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 4, 7]
def baseStart_2483 : Nat := 118140960795 + 2483 * 2 ^ 59
def prefixEnd_2483 : Nat := 4983230072969 + 3 ^ 40 * 2483 * 2
def baseEnd_2483 : Nat := 849981643479345967391

theorem tailTrace_2483 : CollatzResearch.WordTrace tailWord_2483 prefixEnd_2483 849981643479345967391 := by
  unfold tailWord_2483
  simp only [CollatzResearch.WordTrace]
  refine ⟨90562450011989907748103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60374966674659938498735 90562450011989907748103)
  ·
    refine ⟨135843675017984861622155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90562450011989907748103 135843675017984861622155)
    ·
      refine ⟨203765512526977292433233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135843675017984861622155 203765512526977292433233)
      ·
        refine ⟨152824134395232969324925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203765512526977292433233 152824134395232969324925)
        ·
          refine ⟨57309050398212363496847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152824134395232969324925 57309050398212363496847)
          ·
            refine ⟨85963575597318545245271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57309050398212363496847 85963575597318545245271)
            ·
              refine ⟨128945363395977817867907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85963575597318545245271 128945363395977817867907)
              ·
                refine ⟨193418045093966726801861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128945363395977817867907 193418045093966726801861)
                ·
                  refine ⟨36265883455118761275349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193418045093966726801861 36265883455118761275349)
                  ·
                    refine ⟨849981643479345967391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36265883455118761275349 849981643479345967391)
                    ·
                      rfl

theorem cell22_2483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_2483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483 prefixEnd_2483 := by exact prefixLift 2483
  have htrace : WordTrace (prefixWord ++ tailWord_2483) baseStart_2483 baseEnd_2483 := by
    simpa [prefixWord, tailWord_2483, baseEnd_2483] using wordTrace_append hprefix tailTrace_2483
  have hstable : (prefixWord ++ tailWord_2483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483).length < 2 ^ (prefixWord ++ tailWord_2483).sum := by decide
  have hdescent : baseEnd_2483 < baseStart_2483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2545 : Nat := 118140960795 + 2545 * 2 ^ 59
def prefixEnd_2545 : Nat := 4983230072969 + 3 ^ 40 * 2545 * 2
def baseEnd_2545 : Nat := 871205510531850917201

theorem tailTrace_2545 : CollatzResearch.WordTrace tailWord_2545 prefixEnd_2545 871205510531850917201 := by
  unfold tailWord_2545
  simp only [CollatzResearch.WordTrace]
  refine ⟨92823775787374496505089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61882517191582997670059 92823775787374496505089)
  ·
    refine ⟨69617831840530872378817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92823775787374496505089 69617831840530872378817)
    ·
      refine ⟨52213373880398154284113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69617831840530872378817 52213373880398154284113)
      ·
        refine ⟨39160030410298615713085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52213373880398154284113 39160030410298615713085)
        ·
          refine ⟨14685011403861980892407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39160030410298615713085 14685011403861980892407)
          ·
            refine ⟨22027517105792971338611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14685011403861980892407 22027517105792971338611)
            ·
              refine ⟨33041275658689457007917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22027517105792971338611 33041275658689457007917)
              ·
                refine ⟨12390478372008546377969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33041275658689457007917 12390478372008546377969)
                ·
                  refine ⟨9292858779006409783477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12390478372008546377969 9292858779006409783477)
                  ·
                    refine ⟨871205510531850917201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9292858779006409783477 871205510531850917201)
                    ·
                      rfl

theorem cell22_2545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545 prefixEnd_2545 := by exact prefixLift 2545
  have htrace : WordTrace (prefixWord ++ tailWord_2545) baseStart_2545 baseEnd_2545 := by
    simpa [prefixWord, tailWord_2545, baseEnd_2545] using wordTrace_append hprefix tailTrace_2545
  have hstable : (prefixWord ++ tailWord_2545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545).length < 2 ^ (prefixWord ++ tailWord_2545).sum := by decide
  have hdescent : baseEnd_2545 < baseStart_2545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 5]
def baseStart_2547 : Nat := 118140960795 + 2547 * 2 ^ 59
def prefixEnd_2547 : Nat := 4983230072969 + 3 ^ 40 * 2547 * 2
def baseEnd_2547 : Nat := 290630050468170789065

theorem tailTrace_2547 : CollatzResearch.WordTrace tailWord_2547 prefixEnd_2547 290630050468170789065 := by
  unfold tailWord_2547
  simp only [CollatzResearch.WordTrace]
  refine ⟨92896721780128838077895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61931147853419225385263 92896721780128838077895)
  ·
    refine ⟨139345082670193257116843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92896721780128838077895 139345082670193257116843)
    ·
      refine ⟨209017624005289885675265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139345082670193257116843 209017624005289885675265)
      ·
        refine ⟨156763218003967414256449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209017624005289885675265 156763218003967414256449)
        ·
          refine ⟨117572413502975560692337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156763218003967414256449 117572413502975560692337)
          ·
            refine ⟨88179310127231670519253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117572413502975560692337 88179310127231670519253)
            ·
              refine ⟨2066702581106992277795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 88179310127231670519253 2066702581106992277795)
              ·
                refine ⟨3100053871660488416693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066702581106992277795 3100053871660488416693)
                ·
                  refine ⟨290630050468170789065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3100053871660488416693 290630050468170789065)
                  ·
                    rfl

theorem cell22_2547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 5].length) (baseStart_2547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547 prefixEnd_2547 := by exact prefixLift 2547
  have htrace : WordTrace (prefixWord ++ tailWord_2547) baseStart_2547 baseEnd_2547 := by
    simpa [prefixWord, tailWord_2547, baseEnd_2547] using wordTrace_append hprefix tailTrace_2547
  have hstable : (prefixWord ++ tailWord_2547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547).length < 2 ^ (prefixWord ++ tailWord_2547).sum := by decide
  have hdescent : baseEnd_2547 < baseStart_2547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637 : List Nat := [1, 6, 1, 1, 2, 11]
def baseStart_2637 : Nat := 118140960795 + 2637 * 2 ^ 59
def prefixEnd_2637 : Nat := 4983230072969 + 3 ^ 40 * 2637 * 2
def baseEnd_2637 : Nat := 11144431983633056999

theorem tailTrace_2637 : CollatzResearch.WordTrace tailWord_2637 prefixEnd_2637 11144431983633056999 := by
  unfold tailWord_2637
  simp only [CollatzResearch.WordTrace]
  refine ⟨96179291454074208854165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64119527636049472569443 96179291454074208854165)
  ·
    refine ⟨4508404286909728540039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96179291454074208854165 4508404286909728540039)
    ·
      refine ⟨6762606430364592810059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508404286909728540039 6762606430364592810059)
      ·
        refine ⟨10143909645546889215089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6762606430364592810059 10143909645546889215089)
        ·
          refine ⟨7607932234160166911317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10143909645546889215089 7607932234160166911317)
          ·
            refine ⟨11144431983633056999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7607932234160166911317 11144431983633056999)
            ·
              rfl

theorem cell22_2637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 11].length) (baseStart_2637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2637 prefixEnd_2637 := by exact prefixLift 2637
  have htrace : WordTrace (prefixWord ++ tailWord_2637) baseStart_2637 baseEnd_2637 := by
    simpa [prefixWord, tailWord_2637, baseEnd_2637] using wordTrace_append hprefix tailTrace_2637
  have hstable : (prefixWord ++ tailWord_2637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637).length < 2 ^ (prefixWord ++ tailWord_2637).sum := by decide
  have hdescent : baseEnd_2637 < baseStart_2637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 9]
def baseStart_2665 : Nat := 118140960795 + 2665 * 2 ^ 59
def prefixEnd_2665 : Nat := 4983230072969 + 3 ^ 40 * 2665 * 2
def baseEnd_2665 : Nat := 304094654297179305611

theorem tailTrace_2665 : CollatzResearch.WordTrace tailWord_2665 prefixEnd_2665 304094654297179305611 := by
  unfold tailWord_2665
  simp only [CollatzResearch.WordTrace]
  refine ⟨97200535352634990873449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64800356901756660582299 97200535352634990873449)
  ·
    refine ⟨72900401514476243155087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97200535352634990873449 72900401514476243155087)
    ·
      refine ⟨109350602271714364732631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72900401514476243155087 109350602271714364732631)
      ·
        refine ⟨164025903407571547098947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109350602271714364732631 164025903407571547098947)
        ·
          refine ⟨246038855111357320648421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164025903407571547098947 246038855111357320648421)
          ·
            refine ⟨46132285333379497621579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246038855111357320648421 46132285333379497621579)
            ·
              refine ⟨69198428000069246432369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46132285333379497621579 69198428000069246432369)
              ·
                refine ⟨51898821000051934824277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69198428000069246432369 51898821000051934824277)
                ·
                  refine ⟨304094654297179305611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51898821000051934824277 304094654297179305611)
                  ·
                    rfl

theorem cell22_2665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_2665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2665 prefixEnd_2665 := by exact prefixLift 2665
  have htrace : WordTrace (prefixWord ++ tailWord_2665) baseStart_2665 baseEnd_2665 := by
    simpa [prefixWord, tailWord_2665, baseEnd_2665] using wordTrace_append hprefix tailTrace_2665
  have hstable : (prefixWord ++ tailWord_2665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665).length < 2 ^ (prefixWord ++ tailWord_2665).sum := by decide
  have hdescent : baseEnd_2665 < baseStart_2665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2669 : Nat := 118140960795 + 2669 * 2 ^ 59
def prefixEnd_2669 : Nat := 4983230072969 + 3 ^ 40 * 2669 * 2
def baseEnd_2669 : Nat := 913653244636860816821

theorem tailTrace_2669 : CollatzResearch.WordTrace tailWord_2669 prefixEnd_2669 913653244636860816821 := by
  unfold tailWord_2669
  simp only [CollatzResearch.WordTrace]
  refine ⟨97346427338143674019061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64897618225429116012707 97346427338143674019061)
  ·
    refine ⟨9126227562950969439287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97346427338143674019061 9126227562950969439287)
    ·
      refine ⟨13689341344426454158931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9126227562950969439287 13689341344426454158931)
      ·
        refine ⟨20534012016639681238397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13689341344426454158931 20534012016639681238397)
        ·
          refine ⟨7700254506239880464399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20534012016639681238397 7700254506239880464399)
          ·
            refine ⟨11550381759359820696599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7700254506239880464399 11550381759359820696599)
            ·
              refine ⟨17325572639039731044899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11550381759359820696599 17325572639039731044899)
              ·
                refine ⟨25988358958559596567349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17325572639039731044899 25988358958559596567349)
                ·
                  refine ⟨2436408652364962178189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25988358958559596567349 2436408652364962178189)
                  ·
                    refine ⟨913653244636860816821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2436408652364962178189 913653244636860816821)
                    ·
                      rfl

theorem cell22_2669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2669 prefixEnd_2669 := by exact prefixLift 2669
  have htrace : WordTrace (prefixWord ++ tailWord_2669) baseStart_2669 baseEnd_2669 := by
    simpa [prefixWord, tailWord_2669, baseEnd_2669] using wordTrace_append hprefix tailTrace_2669
  have hstable : (prefixWord ++ tailWord_2669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669).length < 2 ^ (prefixWord ++ tailWord_2669).sum := by decide
  have hdescent : baseEnd_2669 < baseStart_2669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 5]
def baseStart_2716 : Nat := 118140960795 + 2716 * 2 ^ 59
def prefixEnd_2716 : Nat := 4983230072969 + 3 ^ 40 * 2716 * 2
def baseEnd_2716 : Nat := 309914101714801630559

theorem tailTrace_2716 : CollatzResearch.WordTrace tailWord_2716 prefixEnd_2716 309914101714801630559 := by
  unfold tailWord_2716
  simp only [CollatzResearch.WordTrace]
  refine ⟨49530329083935350490001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66040438778580467320001 49530329083935350490001)
  ·
    refine ⟨37147746812951512867501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49530329083935350490001 37147746812951512867501)
    ·
      refine ⟨13930405054856817325313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37147746812951512867501 13930405054856817325313)
      ·
        refine ⟨10447803791142612993985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13930405054856817325313 10447803791142612993985)
        ·
          refine ⟨7835852843356959745489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10447803791142612993985 7835852843356959745489)
          ·
            refine ⟨5876889632517719809117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7835852843356959745489 5876889632517719809117)
            ·
              refine ⟨2203833612194144928419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5876889632517719809117 2203833612194144928419)
              ·
                refine ⟨3305750418291217392629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203833612194144928419 3305750418291217392629)
                ·
                  refine ⟨309914101714801630559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3305750418291217392629 309914101714801630559)
                  ·
                    rfl

theorem cell22_2716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_2716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716 prefixEnd_2716 := by exact prefixLift 2716
  have htrace : WordTrace (prefixWord ++ tailWord_2716) baseStart_2716 baseEnd_2716 := by
    simpa [prefixWord, tailWord_2716, baseEnd_2716] using wordTrace_append hprefix tailTrace_2716
  have hstable : (prefixWord ++ tailWord_2716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716).length < 2 ^ (prefixWord ++ tailWord_2716).sum := by decide
  have hdescent : baseEnd_2716 < baseStart_2716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737 : List Nat := [1, 2, 2, 6, 2, 1, 1, 3, 1, 3]
def baseStart_2737 : Nat := 118140960795 + 2737 * 2 ^ 59
def prefixEnd_2737 : Nat := 4983230072969 + 3 ^ 40 * 2737 * 2
def baseEnd_2737 : Nat := 936931034307350116613

theorem tailTrace_2737 : CollatzResearch.WordTrace tailWord_2737 prefixEnd_2737 936931034307350116613 := by
  unfold tailWord_2737
  simp only [CollatzResearch.WordTrace]
  refine ⟨99826591091791287494465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66551060727860858329643 99826591091791287494465)
  ·
    refine ⟨74869943318843465620849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99826591091791287494465 74869943318843465620849)
    ·
      refine ⟨56152457489132599215637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74869943318843465620849 56152457489132599215637)
      ·
        refine ⟨2632146444803090588233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56152457489132599215637 2632146444803090588233)
        ·
          refine ⟨1974109833602317941175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632146444803090588233 1974109833602317941175)
          ·
            refine ⟨2961164750403476911763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974109833602317941175 2961164750403476911763)
            ·
              refine ⟨4441747125605215367645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961164750403476911763 4441747125605215367645)
              ·
                refine ⟨1665655172101955762867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4441747125605215367645 1665655172101955762867)
                ·
                  refine ⟨2498482758152933644301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665655172101955762867 2498482758152933644301)
                  ·
                    refine ⟨936931034307350116613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498482758152933644301 936931034307350116613)
                    ·
                      rfl

theorem cell22_2737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_2737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737 prefixEnd_2737 := by exact prefixLift 2737
  have htrace : WordTrace (prefixWord ++ tailWord_2737) baseStart_2737 baseEnd_2737 := by
    simpa [prefixWord, tailWord_2737, baseEnd_2737] using wordTrace_append hprefix tailTrace_2737
  have hstable : (prefixWord ++ tailWord_2737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737).length < 2 ^ (prefixWord ++ tailWord_2737).sum := by decide
  have hdescent : baseEnd_2737 < baseStart_2737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 2, 3]
def baseStart_2776 : Nat := 118140960795 + 2776 * 2 ^ 59
def prefixEnd_2776 : Nat := 4983230072969 + 3 ^ 40 * 2776 * 2
def baseEnd_2776 : Nat := 950281531324248391493

theorem tailTrace_2776 : CollatzResearch.WordTrace tailWord_2776 prefixEnd_2776 950281531324248391493 := by
  unfold tailWord_2776
  simp only [CollatzResearch.WordTrace]
  refine ⟨50624518975250474082091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67499358633667298776121 50624518975250474082091)
  ·
    refine ⟨75936778462875711123137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50624518975250474082091 75936778462875711123137)
    ·
      refine ⟨56952583847156783342353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75936778462875711123137 56952583847156783342353)
      ·
        refine ⟨42714437885367587506765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56952583847156783342353 42714437885367587506765)
        ·
          refine ⟨16017914207012845315037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42714437885367587506765 16017914207012845315037)
          ·
            refine ⟨6006717827629816993139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16017914207012845315037 6006717827629816993139)
            ·
              refine ⟨9010076741444725489709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6006717827629816993139 9010076741444725489709)
              ·
                refine ⟨3378778778041772058641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9010076741444725489709 3378778778041772058641)
                ·
                  refine ⟨2534084083531329043981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3378778778041772058641 2534084083531329043981)
                  ·
                    refine ⟨950281531324248391493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534084083531329043981 950281531324248391493)
                    ·
                      rfl

theorem cell22_2776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_2776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776 prefixEnd_2776 := by exact prefixLift 2776
  have htrace : WordTrace (prefixWord ++ tailWord_2776) baseStart_2776 baseEnd_2776 := by
    simpa [prefixWord, tailWord_2776, baseEnd_2776] using wordTrace_append hprefix tailTrace_2776
  have hstable : (prefixWord ++ tailWord_2776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776).length < 2 ^ (prefixWord ++ tailWord_2776).sum := by decide
  have hdescent : baseEnd_2776 < baseStart_2776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 6]
def baseStart_2879 : Nat := 118140960795 + 2879 * 2 ^ 59
def prefixEnd_2879 : Nat := 4983230072969 + 3 ^ 40 * 2879 * 2
def baseEnd_2879 : Nat := 328513512088771022059

theorem tailTrace_2879 : CollatzResearch.WordTrace tailWord_2879 prefixEnd_2879 328513512088771022059 := by
  unfold tailWord_2879
  simp only [CollatzResearch.WordTrace]
  refine ⟨105005756577349539163691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70003837718233026109127 105005756577349539163691)
  ·
    refine ⟨157508634866024308745537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105005756577349539163691 157508634866024308745537)
    ·
      refine ⟨118131476149518231559153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157508634866024308745537 118131476149518231559153)
      ·
        refine ⟨88598607112138673669365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118131476149518231559153 88598607112138673669365)
        ·
          refine ⟨8306119416763000656503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88598607112138673669365 8306119416763000656503)
          ·
            refine ⟨12459179125144500984755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8306119416763000656503 12459179125144500984755)
            ·
              refine ⟨18688768687716751477133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12459179125144500984755 18688768687716751477133)
              ·
                refine ⟨7008288257893781803925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18688768687716751477133 7008288257893781803925)
                ·
                  refine ⟨328513512088771022059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7008288257893781803925 328513512088771022059)
                  ·
                    rfl

theorem cell22_2879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 6].length) (baseStart_2879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879 prefixEnd_2879 := by exact prefixLift 2879
  have htrace : WordTrace (prefixWord ++ tailWord_2879) baseStart_2879 baseEnd_2879 := by
    simpa [prefixWord, tailWord_2879, baseEnd_2879] using wordTrace_append hprefix tailTrace_2879
  have hstable : (prefixWord ++ tailWord_2879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879).length < 2 ^ (prefixWord ++ tailWord_2879).sum := by decide
  have hdescent : baseEnd_2879 < baseStart_2879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_2956 : Nat := 118140960795 + 2956 * 2 ^ 59
def prefixEnd_2956 : Nat := 4983230072969 + 3 ^ 40 * 2956 * 2
def baseEnd_2956 : Nat := 1011899209863778890941

theorem tailTrace_2956 : CollatzResearch.WordTrace tailWord_2956 prefixEnd_2956 1011899209863778890941 := by
  unfold tailWord_2956
  simp only [CollatzResearch.WordTrace]
  refine ⟨53907088649195844858361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71876118198927793144481 53907088649195844858361)
  ·
    refine ⟨40430316486896883643771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53907088649195844858361 40430316486896883643771)
    ·
      refine ⟨60645474730345325465657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40430316486896883643771 60645474730345325465657)
      ·
        refine ⟨45484106047758994099243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60645474730345325465657 45484106047758994099243)
        ·
          refine ⟨68226159071638491148865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45484106047758994099243 68226159071638491148865)
          ·
            refine ⟨51169619303728868361649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68226159071638491148865 51169619303728868361649)
            ·
              refine ⟨38377214477796651271237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51169619303728868361649 38377214477796651271237)
              ·
                refine ⟨7195727714586872113357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38377214477796651271237 7195727714586872113357)
                ·
                  refine ⟨2698397892970077042509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7195727714586872113357 2698397892970077042509)
                  ·
                    refine ⟨1011899209863778890941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698397892970077042509 1011899209863778890941)
                    ·
                      rfl

theorem cell22_2956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_2956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956 prefixEnd_2956 := by exact prefixLift 2956
  have htrace : WordTrace (prefixWord ++ tailWord_2956) baseStart_2956 baseEnd_2956 := by
    simpa [prefixWord, tailWord_2956, baseEnd_2956] using wordTrace_append hprefix tailTrace_2956
  have hstable : (prefixWord ++ tailWord_2956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956).length < 2 ^ (prefixWord ++ tailWord_2956).sum := by decide
  have hdescent : baseEnd_2956 < baseStart_2956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_3001 : Nat := 118140960795 + 3001 * 2 ^ 59
def prefixEnd_3001 : Nat := 4983230072969 + 3 ^ 40 * 3001 * 2
def baseEnd_3001 : Nat := 1027303629498661515803

theorem tailTrace_3001 : CollatzResearch.WordTrace tailWord_3001 prefixEnd_3001 1027303629498661515803 := by
  unfold tailWord_3001
  simp only [CollatzResearch.WordTrace]
  refine ⟨109455462135364375104857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72970308090242916736571 109455462135364375104857)
  ·
    refine ⟨82091596601523281328643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109455462135364375104857 82091596601523281328643)
    ·
      refine ⟨123137394902284921992965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82091596601523281328643 123137394902284921992965)
      ·
        refine ⟨23088261544178422873681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123137394902284921992965 23088261544178422873681)
        ·
          refine ⟨17316196158133817155261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23088261544178422873681 17316196158133817155261)
          ·
            refine ⟨6493573559300181433223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17316196158133817155261 6493573559300181433223)
            ·
              refine ⟨9740360338950272149835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493573559300181433223 9740360338950272149835)
              ·
                refine ⟨14610540508425408224753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740360338950272149835 14610540508425408224753)
                ·
                  refine ⟨10957905381319056168565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14610540508425408224753 10957905381319056168565)
                  ·
                    refine ⟨1027303629498661515803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10957905381319056168565 1027303629498661515803)
                    ·
                      rfl

theorem cell22_3001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_3001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001 prefixEnd_3001 := by exact prefixLift 3001
  have htrace : WordTrace (prefixWord ++ tailWord_3001) baseStart_3001 baseEnd_3001 := by
    simpa [prefixWord, tailWord_3001, baseEnd_3001] using wordTrace_append hprefix tailTrace_3001
  have hstable : (prefixWord ++ tailWord_3001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001).length < 2 ^ (prefixWord ++ tailWord_3001).sum := by decide
  have hdescent : baseEnd_3001 < baseStart_3001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_3033 : Nat := 118140960795 + 3033 * 2 ^ 59
def prefixEnd_3033 : Nat := 4983230072969 + 3 ^ 40 * 3033 * 2
def baseEnd_3033 : Nat := 1038257883461244715705

theorem tailTrace_3033 : CollatzResearch.WordTrace tailWord_3033 prefixEnd_3033 1038257883461244715705 := by
  unfold tailWord_3033
  simp only [CollatzResearch.WordTrace]
  refine ⟨110622598019433840269753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73748398679622560179835 110622598019433840269753)
  ·
    refine ⟨82966948514575380202315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110622598019433840269753 82966948514575380202315)
    ·
      refine ⟨124450422771863070303473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82966948514575380202315 124450422771863070303473)
      ·
        refine ⟨93337817078897302727605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124450422771863070303473 93337817078897302727605)
        ·
          refine ⟨8750420351146622130713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93337817078897302727605 8750420351146622130713)
          ·
            refine ⟨6562815263359966598035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8750420351146622130713 6562815263359966598035)
            ·
              refine ⟨9844222895039949897053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562815263359966598035 9844222895039949897053)
              ·
                refine ⟨3691583585639981211395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9844222895039949897053 3691583585639981211395)
                ·
                  refine ⟨5537375378459971817093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691583585639981211395 5537375378459971817093)
                  ·
                    refine ⟨1038257883461244715705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537375378459971817093 1038257883461244715705)
                    ·
                      rfl

theorem cell22_3033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_3033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033 prefixEnd_3033 := by exact prefixLift 3033
  have htrace : WordTrace (prefixWord ++ tailWord_3033) baseStart_3033 baseEnd_3033 := by
    simpa [prefixWord, tailWord_3033, baseEnd_3033] using wordTrace_append hprefix tailTrace_3033
  have hstable : (prefixWord ++ tailWord_3033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033).length < 2 ^ (prefixWord ++ tailWord_3033).sum := by decide
  have hdescent : baseEnd_3033 < baseStart_3033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048 : List Nat := [2, 1, 4, 1, 1, 1, 4, 4, 4]
def baseStart_3048 : Nat := 118140960795 + 3048 * 2 ^ 59
def prefixEnd_3048 : Nat := 4983230072969 + 3 ^ 40 * 3048 * 2
def baseEnd_3048 : Nat := 347797563335401863553

theorem tailTrace_3048 : CollatzResearch.WordTrace tailWord_3048 prefixEnd_3048 347797563335401863553 := by
  unfold tailWord_3048
  simp only [CollatzResearch.WordTrace]
  refine ⟨55584846482545701032899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74113128643394268043865 55584846482545701032899)
  ·
    refine ⟨83377269723818551549349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55584846482545701032899 83377269723818551549349)
    ·
      refine ⟨15633238073215978415503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83377269723818551549349 15633238073215978415503)
      ·
        refine ⟨23449857109823967623255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15633238073215978415503 23449857109823967623255)
        ·
          refine ⟨35174785664735951434883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23449857109823967623255 35174785664735951434883)
          ·
            refine ⟨52762178497103927152325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35174785664735951434883 52762178497103927152325)
            ·
              refine ⟨9892908468206986341061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52762178497103927152325 9892908468206986341061)
              ·
                refine ⟨1854920337788809938949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9892908468206986341061 1854920337788809938949)
                ·
                  refine ⟨347797563335401863553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854920337788809938949 347797563335401863553)
                  ·
                    rfl

theorem cell22_3048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_3048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048 prefixEnd_3048 := by exact prefixLift 3048
  have htrace : WordTrace (prefixWord ++ tailWord_3048) baseStart_3048 baseEnd_3048 := by
    simpa [prefixWord, tailWord_3048, baseEnd_3048] using wordTrace_append hprefix tailTrace_3048
  have hstable : (prefixWord ++ tailWord_3048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048).length < 2 ^ (prefixWord ++ tailWord_3048).sum := by decide
  have hdescent : baseEnd_3048 < baseStart_3048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3114 : Nat := 118140960795 + 3114 * 2 ^ 59
def prefixEnd_3114 : Nat := 4983230072969 + 3 ^ 40 * 3114 * 2
def baseEnd_3114 : Nat := 1065985838804033440457

theorem tailTrace_3114 : CollatzResearch.WordTrace tailWord_3114 prefixEnd_3114 1065985838804033440457 := by
  unfold tailWord_3114
  simp only [CollatzResearch.WordTrace]
  refine ⟨28394227681496168492099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75717940483989782645597 28394227681496168492099)
  ·
    refine ⟨42591341522244252738149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28394227681496168492099 42591341522244252738149)
    ·
      refine ⟨7985876535420797388403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42591341522244252738149 7985876535420797388403)
      ·
        refine ⟨11978814803131196082605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985876535420797388403 11978814803131196082605)
        ·
          refine ⟨4492055551174198530977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11978814803131196082605 4492055551174198530977)
          ·
            refine ⟨3369041663380648898233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4492055551174198530977 3369041663380648898233)
            ·
              refine ⟨2526781247535486673675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3369041663380648898233 2526781247535486673675)
              ·
                refine ⟨3790171871303230010513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526781247535486673675 3790171871303230010513)
                ·
                  refine ⟨2842628903477422507885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3790171871303230010513 2842628903477422507885)
                  ·
                    refine ⟨1065985838804033440457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842628903477422507885 1065985838804033440457)
                    ·
                      rfl

theorem cell22_3114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114 prefixEnd_3114 := by exact prefixLift 3114
  have htrace : WordTrace (prefixWord ++ tailWord_3114) baseStart_3114 baseEnd_3114 := by
    simpa [prefixWord, tailWord_3114, baseEnd_3114] using wordTrace_append hprefix tailTrace_3114
  have hstable : (prefixWord ++ tailWord_3114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114).length < 2 ^ (prefixWord ++ tailWord_3114).sum := by decide
  have hdescent : baseEnd_3114 < baseStart_3114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 7, 4]
def baseStart_3151 : Nat := 118140960795 + 3151 * 2 ^ 59
def prefixEnd_3151 : Nat := 4983230072969 + 3 ^ 40 * 3151 * 2
def baseEnd_3151 : Nat := 1078651694948270265343

theorem tailTrace_3151 : CollatzResearch.WordTrace tailWord_3151 prefixEnd_3151 1078651694948270265343 := by
  unfold tailWord_3151
  simp only [CollatzResearch.WordTrace]
  refine ⟨114926411591939993065307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76617607727959995376871 114926411591939993065307)
  ·
    refine ⟨172389617387909989597961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114926411591939993065307 172389617387909989597961)
    ·
      refine ⟨129292213040932492198471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172389617387909989597961 129292213040932492198471)
      ·
        refine ⟨193938319561398738297707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129292213040932492198471 193938319561398738297707)
        ·
          refine ⟨290907479342098107446561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193938319561398738297707 290907479342098107446561)
          ·
            refine ⟨218180609506573580584921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290907479342098107446561 218180609506573580584921)
            ·
              refine ⟨163635457129930185438691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218180609506573580584921 163635457129930185438691)
              ·
                refine ⟨245453185694895278158037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163635457129930185438691 245453185694895278158037)
                ·
                  refine ⟨5752809039724108081829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 245453185694895278158037 5752809039724108081829)
                  ·
                    refine ⟨1078651694948270265343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752809039724108081829 1078651694948270265343)
                    ·
                      rfl

theorem cell22_3151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_3151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151 prefixEnd_3151 := by exact prefixLift 3151
  have htrace : WordTrace (prefixWord ++ tailWord_3151) baseStart_3151 baseEnd_3151 := by
    simpa [prefixWord, tailWord_3151, baseEnd_3151] using wordTrace_append hprefix tailTrace_3151
  have hstable : (prefixWord ++ tailWord_3151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151).length < 2 ^ (prefixWord ++ tailWord_3151).sum := by decide
  have hdescent : baseEnd_3151 < baseStart_3151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3170 : Nat := 118140960795 + 3170 * 2 ^ 59
def prefixEnd_3170 : Nat := 4983230072969 + 3 ^ 40 * 3170 * 2
def baseEnd_3170 : Nat := 1085155783238554040285

theorem tailTrace_3170 : CollatzResearch.WordTrace tailWord_3170 prefixEnd_3170 1085155783238554040285 := by
  unfold tailWord_3170
  simp only [CollatzResearch.WordTrace]
  refine ⟨28904849630776559501741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77079599015404158671309 28904849630776559501741)
  ·
    refine ⟨10839318611541209813153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28904849630776559501741 10839318611541209813153)
    ·
      refine ⟨8129488958655907359865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10839318611541209813153 8129488958655907359865)
      ·
        refine ⟨6097116718991930519899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8129488958655907359865 6097116718991930519899)
        ·
          refine ⟨9145675078487895779849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6097116718991930519899 9145675078487895779849)
          ·
            refine ⟨6859256308865921834887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9145675078487895779849 6859256308865921834887)
            ·
              refine ⟨10288884463298882752331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859256308865921834887 10288884463298882752331)
              ·
                refine ⟨15433326694948324128497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10288884463298882752331 15433326694948324128497)
                ·
                  refine ⟨11574995021211243096373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15433326694948324128497 11574995021211243096373)
                  ·
                    refine ⟨1085155783238554040285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11574995021211243096373 1085155783238554040285)
                    ·
                      rfl

theorem cell22_3170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3170 prefixEnd_3170 := by exact prefixLift 3170
  have htrace : WordTrace (prefixWord ++ tailWord_3170) baseStart_3170 baseEnd_3170 := by
    simpa [prefixWord, tailWord_3170, baseEnd_3170] using wordTrace_append hprefix tailTrace_3170
  have hstable : (prefixWord ++ tailWord_3170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170).length < 2 ^ (prefixWord ++ tailWord_3170).sum := by decide
  have hdescent : baseEnd_3170 < baseStart_3170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3230 : Nat := 118140960795 + 3230 * 2 ^ 59
def prefixEnd_3230 : Nat := 4983230072969 + 3 ^ 40 * 3230 * 2
def baseEnd_3230 : Nat := 1105695009418397540101

theorem tailTrace_3230 : CollatzResearch.WordTrace tailWord_3230 prefixEnd_3230 1105695009418397540101 := by
  unfold tailWord_3230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725972288217060648893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78538518870490990127429 14725972288217060648893)
  ·
    refine ⟨5522239608081397743335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14725972288217060648893 5522239608081397743335)
    ·
      refine ⟨8283359412122096615003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5522239608081397743335 8283359412122096615003)
      ·
        refine ⟨12425039118183144922505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8283359412122096615003 12425039118183144922505)
        ·
          refine ⟨9318779338637358691879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12425039118183144922505 9318779338637358691879)
          ·
            refine ⟨13978169007956038037819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318779338637358691879 13978169007956038037819)
            ·
              refine ⟨20967253511934057056729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13978169007956038037819 20967253511934057056729)
              ·
                refine ⟨15725440133950542792547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20967253511934057056729 15725440133950542792547)
                ·
                  refine ⟨23588160200925814188821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15725440133950542792547 23588160200925814188821)
                  ·
                    refine ⟨1105695009418397540101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23588160200925814188821 1105695009418397540101)
                    ·
                      rfl

theorem cell22_3230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230 prefixEnd_3230 := by exact prefixLift 3230
  have htrace : WordTrace (prefixWord ++ tailWord_3230) baseStart_3230 baseEnd_3230 := by
    simpa [prefixWord, tailWord_3230, baseEnd_3230] using wordTrace_append hprefix tailTrace_3230
  have hstable : (prefixWord ++ tailWord_3230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230).length < 2 ^ (prefixWord ++ tailWord_3230).sum := by decide
  have hdescent : baseEnd_3230 < baseStart_3230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 2, 3]
def baseStart_3232 : Nat := 118140960795 + 3232 * 2 ^ 59
def prefixEnd_3232 : Nat := 4983230072969 + 3 ^ 40 * 3232 * 2
def baseEnd_3232 : Nat := 1106379650291058990095

theorem tailTrace_3232 : CollatzResearch.WordTrace tailWord_3232 prefixEnd_3232 1106379650291058990095 := by
  unfold tailWord_3232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58940362149245413381975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78587149532327217842633 58940362149245413381975)
  ·
    refine ⟨88410543223868120072963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58940362149245413381975 88410543223868120072963)
    ·
      refine ⟨132615814835802180109445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88410543223868120072963 132615814835802180109445)
      ·
        refine ⟨24865465281712908770521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132615814835802180109445 24865465281712908770521)
        ·
          refine ⟨18649098961284681577891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24865465281712908770521 18649098961284681577891)
          ·
            refine ⟨27973648441927022366837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18649098961284681577891 27973648441927022366837)
            ·
              refine ⟨2622529541430658346891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27973648441927022366837 2622529541430658346891)
              ·
                refine ⟨3933794312145987520337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622529541430658346891 3933794312145987520337)
                ·
                  refine ⟨2950345734109490640253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933794312145987520337 2950345734109490640253)
                  ·
                    refine ⟨1106379650291058990095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950345734109490640253 1106379650291058990095)
                    ·
                      rfl

theorem cell22_3232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_3232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232 prefixEnd_3232 := by exact prefixLift 3232
  have htrace : WordTrace (prefixWord ++ tailWord_3232) baseStart_3232 baseEnd_3232 := by
    simpa [prefixWord, tailWord_3232, baseEnd_3232] using wordTrace_append hprefix tailTrace_3232
  have hstable : (prefixWord ++ tailWord_3232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232).length < 2 ^ (prefixWord ++ tailWord_3232).sum := by decide
  have hdescent : baseEnd_3232 < baseStart_3232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245 : List Nat := [1, 5, 2, 1, 3, 1, 1, 8]
def baseStart_3245 : Nat := 118140960795 + 3245 * 2 ^ 59
def prefixEnd_3245 : Nat := 4983230072969 + 3 ^ 40 * 3245 * 2
def baseEnd_3245 : Nat := 123425535107039823895

theorem tailTrace_3245 : CollatzResearch.WordTrace tailWord_3245 prefixEnd_3245 123425535107039823895 := by
  unfold tailWord_3245
  simp only [CollatzResearch.WordTrace]
  refine ⟨118354873251394046987189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78903248834262697991459 118354873251394046987189)
  ·
    refine ⟨11095769367318191905049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118354873251394046987189 11095769367318191905049)
    ·
      refine ⟨8321827025488643928787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11095769367318191905049 8321827025488643928787)
      ·
        refine ⟨12482740538232965893181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8321827025488643928787 12482740538232965893181)
        ·
          refine ⟨4681027701837362209943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12482740538232965893181 4681027701837362209943)
          ·
            refine ⟨7021541552756043314915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681027701837362209943 7021541552756043314915)
            ·
              refine ⟨10532312329134064972373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021541552756043314915 10532312329134064972373)
              ·
                refine ⟨123425535107039823895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10532312329134064972373 123425535107039823895)
                ·
                  rfl

theorem cell22_3245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 8].length) (baseStart_3245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245 prefixEnd_3245 := by exact prefixLift 3245
  have htrace : WordTrace (prefixWord ++ tailWord_3245) baseStart_3245 baseEnd_3245 := by
    simpa [prefixWord, tailWord_3245, baseEnd_3245] using wordTrace_append hprefix tailTrace_3245
  have hstable : (prefixWord ++ tailWord_3245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245).length < 2 ^ (prefixWord ++ tailWord_3245).sum := by decide
  have hdescent : baseEnd_3245 < baseStart_3245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_3333 : Nat := 118140960795 + 3333 * 2 ^ 59
def prefixEnd_3333 : Nat := 4983230072969 + 3 ^ 40 * 3333 * 2
def baseEnd_3333 : Nat := 1140954014360462214785

theorem tailTrace_3333 : CollatzResearch.WordTrace tailWord_3333 prefixEnd_3333 1140954014360462214785 := by
  unfold tailWord_3333
  simp only [CollatzResearch.WordTrace]
  refine ⟨121564496932585076190653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81042997955056717460435 121564496932585076190653)
  ·
    refine ⟨45586686349719403571495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121564496932585076190653 45586686349719403571495)
    ·
      refine ⟨68380029524579105357243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45586686349719403571495 68380029524579105357243)
      ·
        refine ⟨102570044286868658035865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68380029524579105357243 102570044286868658035865)
        ·
          refine ⟨76927533215151493526899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102570044286868658035865 76927533215151493526899)
          ·
            refine ⟨115391299822727240290349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76927533215151493526899 115391299822727240290349)
            ·
              refine ⟨43271737433522715108881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115391299822727240290349 43271737433522715108881)
              ·
                refine ⟨32453803075142036331661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43271737433522715108881 32453803075142036331661)
                ·
                  refine ⟨12170176153178263624373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32453803075142036331661 12170176153178263624373)
                  ·
                    refine ⟨1140954014360462214785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12170176153178263624373 1140954014360462214785)
                    ·
                      rfl

theorem cell22_3333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_3333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333 prefixEnd_3333 := by exact prefixLift 3333
  have htrace : WordTrace (prefixWord ++ tailWord_3333) baseStart_3333 baseEnd_3333 := by
    simpa [prefixWord, tailWord_3333, baseEnd_3333] using wordTrace_append hprefix tailTrace_3333
  have hstable : (prefixWord ++ tailWord_3333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333).length < 2 ^ (prefixWord ++ tailWord_3333).sum := by decide
  have hdescent : baseEnd_3333 < baseStart_3333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_3365 : Nat := 118140960795 + 3365 * 2 ^ 59
def prefixEnd_3365 : Nat := 4983230072969 + 3 ^ 40 * 3365 * 2
def baseEnd_3365 : Nat := 1151908268323045414687

theorem tailTrace_3365 : CollatzResearch.WordTrace tailWord_3365 prefixEnd_3365 1151908268323045414687 := by
  unfold tailWord_3365
  simp only [CollatzResearch.WordTrace]
  refine ⟨122731632816654541355549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81821088544436360903699 122731632816654541355549)
  ·
    refine ⟨46024362306245453008331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122731632816654541355549 46024362306245453008331)
    ·
      refine ⟨69036543459368179512497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46024362306245453008331 69036543459368179512497)
      ·
        refine ⟨51777407594526134634373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69036543459368179512497 51777407594526134634373)
        ·
          refine ⟨9708263923973650243945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51777407594526134634373 9708263923973650243945)
          ·
            refine ⟨7281197942980237682959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9708263923973650243945 7281197942980237682959)
            ·
              refine ⟨10921796914470356524439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281197942980237682959 10921796914470356524439)
              ·
                refine ⟨16382695371705534786659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10921796914470356524439 16382695371705534786659)
                ·
                  refine ⟨24574043057558302179989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16382695371705534786659 24574043057558302179989)
                  ·
                    refine ⟨1151908268323045414687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24574043057558302179989 1151908268323045414687)
                    ·
                      rfl

theorem cell22_3365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_3365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365 prefixEnd_3365 := by exact prefixLift 3365
  have htrace : WordTrace (prefixWord ++ tailWord_3365) baseStart_3365 baseEnd_3365 := by
    simpa [prefixWord, tailWord_3365, baseEnd_3365] using wordTrace_append hprefix tailTrace_3365
  have hstable : (prefixWord ++ tailWord_3365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365).length < 2 ^ (prefixWord ++ tailWord_3365).sum := by decide
  have hdescent : baseEnd_3365 < baseStart_3365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380 : List Nat := [2, 5, 1, 1, 1, 1, 11]
def baseStart_3380 : Nat := 118140960795 + 3380 * 2 ^ 59
def prefixEnd_3380 : Nat := 4983230072969 + 3 ^ 40 * 3380 * 2
def baseEnd_3380 : Nat := 42853447217333566283

theorem tailTrace_3380 : CollatzResearch.WordTrace tailWord_3380 prefixEnd_3380 42853447217333566283 := by
  unfold tailWord_3380
  simp only [CollatzResearch.WordTrace]
  refine ⟨61639363881156051575797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82185818508208068767729 61639363881156051575797)
  ·
    refine ⟨5778690363858379835231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61639363881156051575797 5778690363858379835231)
    ·
      refine ⟨8668035545787569752847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778690363858379835231 8668035545787569752847)
      ·
        refine ⟨13002053318681354629271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8668035545787569752847 13002053318681354629271)
        ·
          refine ⟨19503079978022031943907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13002053318681354629271 19503079978022031943907)
          ·
            refine ⟨29254619967033047915861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19503079978022031943907 29254619967033047915861)
            ·
              refine ⟨42853447217333566283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29254619967033047915861 42853447217333566283)
              ·
                rfl

theorem cell22_3380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 11].length) (baseStart_3380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380 prefixEnd_3380 := by exact prefixLift 3380
  have htrace : WordTrace (prefixWord ++ tailWord_3380) baseStart_3380 baseEnd_3380 := by
    simpa [prefixWord, tailWord_3380, baseEnd_3380] using wordTrace_append hprefix tailTrace_3380
  have hstable : (prefixWord ++ tailWord_3380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380).length < 2 ^ (prefixWord ++ tailWord_3380).sum := by decide
  have hdescent : baseEnd_3380 < baseStart_3380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3412 : Nat := 118140960795 + 3412 * 2 ^ 59
def prefixEnd_3412 : Nat := 4983230072969 + 3 ^ 40 * 3412 * 2
def baseEnd_3412 : Nat := 1167997328830589489543

theorem tailTrace_3412 : CollatzResearch.WordTrace tailWord_3412 prefixEnd_3412 1167997328830589489543 := by
  unfold tailWord_3412
  simp only [CollatzResearch.WordTrace]
  refine ⟨62222931823190784158245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82963909097587712210993 62222931823190784158245)
  ·
    refine ⟨11666799716848272029671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62222931823190784158245 11666799716848272029671)
    ·
      refine ⟨17500199575272408044507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11666799716848272029671 17500199575272408044507)
      ·
        refine ⟨26250299362908612066761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17500199575272408044507 26250299362908612066761)
        ·
          refine ⟨19687724522181459050071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26250299362908612066761 19687724522181459050071)
          ·
            refine ⟨29531586783272188575107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19687724522181459050071 29531586783272188575107)
            ·
              refine ⟨44297380174908282862661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29531586783272188575107 44297380174908282862661)
              ·
                refine ⟨8305758782795303036749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44297380174908282862661 8305758782795303036749)
                ·
                  refine ⟨3114659543548238638781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8305758782795303036749 3114659543548238638781)
                  ·
                    refine ⟨1167997328830589489543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114659543548238638781 1167997328830589489543)
                    ·
                      rfl

theorem cell22_3412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412 prefixEnd_3412 := by exact prefixLift 3412
  have htrace : WordTrace (prefixWord ++ tailWord_3412) baseStart_3412 baseEnd_3412 := by
    simpa [prefixWord, tailWord_3412, baseEnd_3412] using wordTrace_append hprefix tailTrace_3412
  have hstable : (prefixWord ++ tailWord_3412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412).length < 2 ^ (prefixWord ++ tailWord_3412).sum := by decide
  have hdescent : baseEnd_3412 < baseStart_3412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 5]
def baseStart_3459 : Nat := 118140960795 + 3459 * 2 ^ 59
def prefixEnd_3459 : Nat := 4983230072969 + 3 ^ 40 * 3459 * 2
def baseEnd_3459 : Nat := 394695463112711188133

theorem tailTrace_3459 : CollatzResearch.WordTrace tailWord_3459 prefixEnd_3459 394695463112711188133 := by
  unfold tailWord_3459
  simp only [CollatzResearch.WordTrace]
  refine ⟨126160094476108595277431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84106729650739063518287 126160094476108595277431)
  ·
    refine ⟨189240141714162892916147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126160094476108595277431 189240141714162892916147)
    ·
      refine ⟨283860212571244339374221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189240141714162892916147 283860212571244339374221)
      ·
        refine ⟨106447579714216627265333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283860212571244339374221 106447579714216627265333)
        ·
          refine ⟨9979460598207808806125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106447579714216627265333 9979460598207808806125)
          ·
            refine ⟨3742297724327928302297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9979460598207808806125 3742297724327928302297)
            ·
              refine ⟨2806723293245946226723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742297724327928302297 2806723293245946226723)
              ·
                refine ⟨4210084939868919340085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806723293245946226723 4210084939868919340085)
                ·
                  refine ⟨394695463112711188133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4210084939868919340085 394695463112711188133)
                  ·
                    rfl

theorem cell22_3459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 5].length) (baseStart_3459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459 prefixEnd_3459 := by exact prefixLift 3459
  have htrace : WordTrace (prefixWord ++ tailWord_3459) baseStart_3459 baseEnd_3459 := by
    simpa [prefixWord, tailWord_3459, baseEnd_3459] using wordTrace_append hprefix tailTrace_3459
  have hstable : (prefixWord ++ tailWord_3459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459).length < 2 ^ (prefixWord ++ tailWord_3459).sum := by decide
  have hdescent : baseEnd_3459 < baseStart_3459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 1, 7]
def baseStart_3575 : Nat := 118140960795 + 3575 * 2 ^ 59
def prefixEnd_3575 : Nat := 4983230072969 + 3 ^ 40 * 3575 * 2
def baseEnd_3575 : Nat := 1223795559952497664043

theorem tailTrace_3575 : CollatzResearch.WordTrace tailWord_3575 prefixEnd_3575 1223795559952497664043 := by
  unfold tailWord_3575
  simp only [CollatzResearch.WordTrace]
  refine ⟨130390962055860406500179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86927308037240271000119 130390962055860406500179)
  ·
    refine ⟨195586443083790609750269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130390962055860406500179 195586443083790609750269)
    ·
      refine ⟨73344916156421478656351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195586443083790609750269 73344916156421478656351)
      ·
        refine ⟨110017374234632217984527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73344916156421478656351 110017374234632217984527)
        ·
          refine ⟨165026061351948326976791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110017374234632217984527 165026061351948326976791)
          ·
            refine ⟨247539092027922490465187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165026061351948326976791 247539092027922490465187)
            ·
              refine ⟨371308638041883735697781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247539092027922490465187 371308638041883735697781)
              ·
                refine ⟨34810184816426600221667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 371308638041883735697781 34810184816426600221667)
                ·
                  refine ⟨52215277224639900332501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34810184816426600221667 52215277224639900332501)
                  ·
                    refine ⟨1223795559952497664043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52215277224639900332501 1223795559952497664043)
                    ·
                      rfl

theorem cell22_3575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_3575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575 prefixEnd_3575 := by exact prefixLift 3575
  have htrace : WordTrace (prefixWord ++ tailWord_3575) baseStart_3575 baseEnd_3575 := by
    simpa [prefixWord, tailWord_3575, baseEnd_3575] using wordTrace_append hprefix tailTrace_3575
  have hstable : (prefixWord ++ tailWord_3575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575).length < 2 ^ (prefixWord ++ tailWord_3575).sum := by decide
  have hdescent : baseEnd_3575 < baseStart_3575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 1, 4]
def baseStart_3641 : Nat := 118140960795 + 3641 * 2 ^ 59
def prefixEnd_3641 : Nat := 4983230072969 + 3 ^ 40 * 3641 * 2
def baseEnd_3641 : Nat := 1246388708750325513841

theorem tailTrace_3641 : CollatzResearch.WordTrace tailWord_3641 prefixEnd_3641 1246388708750325513841 := by
  unfold tailWord_3641
  simp only [CollatzResearch.WordTrace]
  refine ⟨132798179816753678402777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88532119877835785601851 132798179816753678402777)
  ·
    refine ⟨99598634862565258802083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132798179816753678402777 99598634862565258802083)
    ·
      refine ⟨149397952293847888203125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99598634862565258802083 149397952293847888203125)
      ·
        refine ⟨14006058027548239519043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149397952293847888203125 14006058027548239519043)
        ·
          refine ⟨21009087041322359278565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14006058027548239519043 21009087041322359278565)
          ·
            refine ⟨3939203820247942364731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21009087041322359278565 3939203820247942364731)
            ·
              refine ⟨5908805730371913547097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939203820247942364731 5908805730371913547097)
              ·
                refine ⟨4431604297778935160323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908805730371913547097 4431604297778935160323)
                ·
                  refine ⟨6647406446668402740485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431604297778935160323 6647406446668402740485)
                  ·
                    refine ⟨1246388708750325513841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647406446668402740485 1246388708750325513841)
                    ·
                      rfl

theorem cell22_3641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_3641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641 prefixEnd_3641 := by exact prefixLift 3641
  have htrace : WordTrace (prefixWord ++ tailWord_3641) baseStart_3641 baseEnd_3641 := by
    simpa [prefixWord, tailWord_3641, baseEnd_3641] using wordTrace_append hprefix tailTrace_3641
  have hstable : (prefixWord ++ tailWord_3641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641).length < 2 ^ (prefixWord ++ tailWord_3641).sum := by decide
  have hdescent : baseEnd_3641 < baseStart_3641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 2, 3]
def baseStart_3671 : Nat := 118140960795 + 3671 * 2 ^ 59
def prefixEnd_3671 : Nat := 4983230072969 + 3 ^ 40 * 3671 * 2
def baseEnd_3671 : Nat := 1256658321840247263749

theorem tailTrace_3671 : CollatzResearch.WordTrace tailWord_3671 prefixEnd_3671 1256658321840247263749 := by
  unfold tailWord_3671
  simp only [CollatzResearch.WordTrace]
  refine ⟨133892369708068801994867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89261579805379201329911 133892369708068801994867)
  ·
    refine ⟨200838554562103202992301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133892369708068801994867 200838554562103202992301)
    ·
      refine ⟨75314457960788701122113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200838554562103202992301 75314457960788701122113)
      ·
        refine ⟨56485843470591525841585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75314457960788701122113 56485843470591525841585)
        ·
          refine ⟨42364382602943644381189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56485843470591525841585 42364382602943644381189)
          ·
            refine ⟨7943321738051933321473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42364382602943644381189 7943321738051933321473)
            ·
              refine ⟨5957491303538949991105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7943321738051933321473 5957491303538949991105)
              ·
                refine ⟨4468118477654212493329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5957491303538949991105 4468118477654212493329)
                ·
                  refine ⟨3351088858240659369997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4468118477654212493329 3351088858240659369997)
                  ·
                    refine ⟨1256658321840247263749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3351088858240659369997 1256658321840247263749)
                    ·
                      rfl

theorem cell22_3671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_3671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671 prefixEnd_3671 := by exact prefixLift 3671
  have htrace : WordTrace (prefixWord ++ tailWord_3671) baseStart_3671 baseEnd_3671 := by
    simpa [prefixWord, tailWord_3671, baseEnd_3671] using wordTrace_append hprefix tailTrace_3671
  have hstable : (prefixWord ++ tailWord_3671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671).length < 2 ^ (prefixWord ++ tailWord_3671).sum := by decide
  have hdescent : baseEnd_3671 < baseStart_3671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684 : List Nat := [2, 3, 1, 1, 2, 5, 1, 7]
def baseStart_3684 : Nat := 118140960795 + 3684 * 2 ^ 59
def prefixEnd_3684 : Nat := 4983230072969 + 3 ^ 40 * 3684 * 2
def baseEnd_3684 : Nat := 140123165279171854301

theorem tailTrace_3684 : CollatzResearch.WordTrace tailWord_3684 prefixEnd_3684 140123165279171854301 := by
  unfold tailWord_3684
  simp only [CollatzResearch.WordTrace]
  refine ⟨67183259330486011109053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89577679107314681478737 67183259330486011109053)
  ·
    refine ⟨25193722248932254165895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67183259330486011109053 25193722248932254165895)
    ·
      refine ⟨37790583373398381248843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25193722248932254165895 37790583373398381248843)
      ·
        refine ⟨56685875060097571873265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37790583373398381248843 56685875060097571873265)
        ·
          refine ⟨42514406295073178904949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56685875060097571873265 42514406295073178904949)
          ·
            refine ⟨3985725590163110522339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42514406295073178904949 3985725590163110522339)
            ·
              refine ⟨5978588385244665783509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985725590163110522339 5978588385244665783509)
              ·
                refine ⟨140123165279171854301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5978588385244665783509 140123165279171854301)
                ·
                  rfl

theorem cell22_3684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 7].length) (baseStart_3684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684 prefixEnd_3684 := by exact prefixLift 3684
  have htrace : WordTrace (prefixWord ++ tailWord_3684) baseStart_3684 baseEnd_3684 := by
    simpa [prefixWord, tailWord_3684, baseEnd_3684] using wordTrace_append hprefix tailTrace_3684
  have hstable : (prefixWord ++ tailWord_3684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684).length < 2 ^ (prefixWord ++ tailWord_3684).sum := by decide
  have hdescent : baseEnd_3684 < baseStart_3684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701 : List Nat := [1, 3, 4, 2, 1, 2, 3, 6]
def baseStart_3701 : Nat := 118140960795 + 3701 * 2 ^ 59
def prefixEnd_3701 : Nat := 4983230072969 + 3 ^ 40 * 3701 * 2
def baseEnd_3701 : Nat := 140769770547796557073

theorem tailTrace_3701 : CollatzResearch.WordTrace tailWord_3701 prefixEnd_3701 140769770547796557073 := by
  unfold tailWord_3701
  simp only [CollatzResearch.WordTrace]
  refine ⟨134986559599383925586957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89991039732922617057971 134986559599383925586957)
  ·
    refine ⟨50619959849768972095109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134986559599383925586957 50619959849768972095109)
    ·
      refine ⟨9491242471831682267833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50619959849768972095109 9491242471831682267833)
      ·
        refine ⟨7118431853873761700875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9491242471831682267833 7118431853873761700875)
        ·
          refine ⟨10677647780810642551313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118431853873761700875 10677647780810642551313)
          ·
            refine ⟨8008235835607981913485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10677647780810642551313 8008235835607981913485)
            ·
              refine ⟨3003088438352993217557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8008235835607981913485 3003088438352993217557)
              ·
                refine ⟨140769770547796557073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3003088438352993217557 140769770547796557073)
                ·
                  rfl

theorem cell22_3701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 6].length) (baseStart_3701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701 prefixEnd_3701 := by exact prefixLift 3701
  have htrace : WordTrace (prefixWord ++ tailWord_3701) baseStart_3701 baseEnd_3701 := by
    simpa [prefixWord, tailWord_3701, baseEnd_3701] using wordTrace_append hprefix tailTrace_3701
  have hstable : (prefixWord ++ tailWord_3701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701).length < 2 ^ (prefixWord ++ tailWord_3701).sum := by decide
  have hdescent : baseEnd_3701 < baseStart_3701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 7]
def baseStart_3712 : Nat := 118140960795 + 3712 * 2 ^ 59
def prefixEnd_3712 : Nat := 4983230072969 + 3 ^ 40 * 3712 * 2
def baseEnd_3712 : Nat := 423564486576602329541

theorem tailTrace_3712 : CollatzResearch.WordTrace tailWord_3712 prefixEnd_3712 423564486576602329541 := by
  unfold tailWord_3712
  simp only [CollatzResearch.WordTrace]
  refine ⟨67693881279766402118695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90258508373021869491593 67693881279766402118695)
  ·
    refine ⟨101540821919649603178043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67693881279766402118695 101540821919649603178043)
    ·
      refine ⟨152311232879474404767065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101540821919649603178043 152311232879474404767065)
      ·
        refine ⟨114233424659605803575299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152311232879474404767065 114233424659605803575299)
        ·
          refine ⟨171350136989408705362949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114233424659605803575299 171350136989408705362949)
          ·
            refine ⟨32128150685514132255553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171350136989408705362949 32128150685514132255553)
            ·
              refine ⟨24096113014135599191665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32128150685514132255553 24096113014135599191665)
              ·
                refine ⟨18072084760601699393749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24096113014135599191665 18072084760601699393749)
                ·
                  refine ⟨423564486576602329541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18072084760601699393749 423564486576602329541)
                  ·
                    rfl

theorem cell22_3712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_3712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712 prefixEnd_3712 := by exact prefixLift 3712
  have htrace : WordTrace (prefixWord ++ tailWord_3712) baseStart_3712 baseEnd_3712 := by
    simpa [prefixWord, tailWord_3712, baseEnd_3712] using wordTrace_append hprefix tailTrace_3712
  have hstable : (prefixWord ++ tailWord_3712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712).length < 2 ^ (prefixWord ++ tailWord_3712).sum := by decide
  have hdescent : baseEnd_3712 < baseStart_3712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_3744 : Nat := 118140960795 + 3744 * 2 ^ 59
def prefixEnd_3744 : Nat := 4983230072969 + 3 ^ 40 * 3744 * 2
def baseEnd_3744 : Nat := 1281647713692390188525

theorem tailTrace_3744 : CollatzResearch.WordTrace tailWord_3744 prefixEnd_3744 1281647713692390188525 := by
  unfold tailWord_3744
  simp only [CollatzResearch.WordTrace]
  refine ⟨68277449221801134701143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91036598962401512934857 68277449221801134701143)
  ·
    refine ⟨102416173832701702051715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68277449221801134701143 102416173832701702051715)
    ·
      refine ⟨153624260749052553077573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102416173832701702051715 153624260749052553077573)
      ·
        refine ⟨28804548890447353702045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153624260749052553077573 28804548890447353702045)
        ·
          refine ⟨10801705833917757638267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28804548890447353702045 10801705833917757638267)
          ·
            refine ⟨16202558750876636457401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801705833917757638267 16202558750876636457401)
            ·
              refine ⟨12151919063157477343051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16202558750876636457401 12151919063157477343051)
              ·
                refine ⟨18227878594736216014577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12151919063157477343051 18227878594736216014577)
                ·
                  refine ⟨13670908946052162010933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18227878594736216014577 13670908946052162010933)
                  ·
                    refine ⟨1281647713692390188525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13670908946052162010933 1281647713692390188525)
                    ·
                      rfl

theorem cell22_3744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_3744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744 prefixEnd_3744 := by exact prefixLift 3744
  have htrace : WordTrace (prefixWord ++ tailWord_3744) baseStart_3744 baseEnd_3744 := by
    simpa [prefixWord, tailWord_3744, baseEnd_3744] using wordTrace_append hprefix tailTrace_3744
  have hstable : (prefixWord ++ tailWord_3744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744).length < 2 ^ (prefixWord ++ tailWord_3744).sum := by decide
  have hdescent : baseEnd_3744 < baseStart_3744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752 : List Nat := [2, 1, 7, 1, 2, 1, 2, 6]
def baseStart_3752 : Nat := 118140960795 + 3752 * 2 ^ 59
def prefixEnd_3752 : Nat := 4983230072969 + 3 ^ 40 * 3752 * 2
def baseEnd_3752 : Nat := 142709586353670665389

theorem tailTrace_3752 : CollatzResearch.WordTrace tailWord_3752 prefixEnd_3752 142709586353670665389 := by
  unfold tailWord_3752
  simp only [CollatzResearch.WordTrace]
  refine ⟨68423341207309817846755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91231121609746423795673 68423341207309817846755)
  ·
    refine ⟨102635011810964726770133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68423341207309817846755 102635011810964726770133)
    ·
      refine ⟨2405508089319485783675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102635011810964726770133 2405508089319485783675)
      ·
        refine ⟨3608262133979228675513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405508089319485783675 3608262133979228675513)
        ·
          refine ⟨2706196600484421506635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3608262133979228675513 2706196600484421506635)
          ·
            refine ⟨4059294900726632259953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706196600484421506635 4059294900726632259953)
            ·
              refine ⟨3044471175544974194965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4059294900726632259953 3044471175544974194965)
              ·
                refine ⟨142709586353670665389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3044471175544974194965 142709586353670665389)
                ·
                  rfl

theorem cell22_3752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 6].length) (baseStart_3752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3752 prefixEnd_3752 := by exact prefixLift 3752
  have htrace : WordTrace (prefixWord ++ tailWord_3752) baseStart_3752 baseEnd_3752 := by
    simpa [prefixWord, tailWord_3752, baseEnd_3752] using wordTrace_append hprefix tailTrace_3752
  have hstable : (prefixWord ++ tailWord_3752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752).length < 2 ^ (prefixWord ++ tailWord_3752).sum := by decide
  have hdescent : baseEnd_3752 < baseStart_3752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3821 : Nat := 118140960795 + 3821 * 2 ^ 59
def prefixEnd_3821 : Nat := 4983230072969 + 3 ^ 40 * 3821 * 2
def baseEnd_3821 : Nat := 1308006387289856013289

theorem tailTrace_3821 : CollatzResearch.WordTrace tailWord_3821 prefixEnd_3821 1308006387289856013289 := by
  unfold tailWord_3821
  simp only [CollatzResearch.WordTrace]
  refine ⟨139363319164644419955317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92908879443096279970211 139363319164644419955317)
  ·
    refine ⟨13065311171685414370811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139363319164644419955317 13065311171685414370811)
    ·
      refine ⟨19597966757528121556217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065311171685414370811 19597966757528121556217)
      ·
        refine ⟨14698475068146091167163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19597966757528121556217 14698475068146091167163)
        ·
          refine ⟨22047712602219136750745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14698475068146091167163 22047712602219136750745)
          ·
            refine ⟨16535784451664352563059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22047712602219136750745 16535784451664352563059)
            ·
              refine ⟨24803676677496528844589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16535784451664352563059 24803676677496528844589)
              ·
                refine ⟨9301378754061198316721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24803676677496528844589 9301378754061198316721)
                ·
                  refine ⟨6976034065545898737541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9301378754061198316721 6976034065545898737541)
                  ·
                    refine ⟨1308006387289856013289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976034065545898737541 1308006387289856013289)
                    ·
                      rfl

theorem cell22_3821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821 prefixEnd_3821 := by exact prefixLift 3821
  have htrace : WordTrace (prefixWord ++ tailWord_3821) baseStart_3821 baseEnd_3821 := by
    simpa [prefixWord, tailWord_3821, baseEnd_3821] using wordTrace_append hprefix tailTrace_3821
  have hstable : (prefixWord ++ tailWord_3821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821).length < 2 ^ (prefixWord ++ tailWord_3821).sum := by decide
  have hdescent : baseEnd_3821 < baseStart_3821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_3898 : Nat := 118140960795 + 3898 * 2 ^ 59
def prefixEnd_3898 : Nat := 4983230072969 + 3 ^ 40 * 3898 * 2
def baseEnd_3898 : Nat := 444788353629107279351

theorem tailTrace_3898 : CollatzResearch.WordTrace tailWord_3898 prefixEnd_3898 444788353629107279351 := by
  unfold tailWord_3898
  simp only [CollatzResearch.WordTrace]
  refine ⟨35542934971421642627087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94781159923791047005565 35542934971421642627087)
  ·
    refine ⟨53314402457132463940631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35542934971421642627087 53314402457132463940631)
    ·
      refine ⟨79971603685698695910947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53314402457132463940631 79971603685698695910947)
      ·
        refine ⟨119957405528548043866421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79971603685698695910947 119957405528548043866421)
        ·
          refine ⟨11246006768301379112477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119957405528548043866421 11246006768301379112477)
          ·
            refine ⟨4217252538113017167179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11246006768301379112477 4217252538113017167179)
            ·
              refine ⟨6325878807169525750769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217252538113017167179 6325878807169525750769)
              ·
                refine ⟨4744409105377144313077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6325878807169525750769 4744409105377144313077)
                ·
                  refine ⟨444788353629107279351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4744409105377144313077 444788353629107279351)
                  ·
                    rfl

theorem cell22_3898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_3898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3898 prefixEnd_3898 := by exact prefixLift 3898
  have htrace : WordTrace (prefixWord ++ tailWord_3898) baseStart_3898 baseEnd_3898 := by
    simpa [prefixWord, tailWord_3898, baseEnd_3898] using wordTrace_append hprefix tailTrace_3898
  have hstable : (prefixWord ++ tailWord_3898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898).length < 2 ^ (prefixWord ++ tailWord_3898).sum := by decide
  have hdescent : baseEnd_3898 < baseStart_3898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971 : List Nat := [1, 1, 1, 3, 4, 3, 2, 7]
def baseStart_3971 : Nat := 118140960795 + 3971 * 2 ^ 59
def prefixEnd_3971 : Nat := 4983230072969 + 3 ^ 40 * 3971 * 2
def baseEnd_3971 : Nat := 151039383637718306981

theorem tailTrace_3971 : CollatzResearch.WordTrace tailWord_3971 prefixEnd_3971 151039383637718306981 := by
  unfold tailWord_3971
  simp only [CollatzResearch.WordTrace]
  refine ⟨144834268621220037915767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96556179080813358610511 144834268621220037915767)
  ·
    refine ⟨217251402931830056873651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144834268621220037915767 217251402931830056873651)
    ·
      refine ⟨325877104397745085310477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217251402931830056873651 325877104397745085310477)
      ·
        refine ⟨122203914149154406991429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325877104397745085310477 122203914149154406991429)
        ·
          refine ⟨22913233902966451310893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122203914149154406991429 22913233902966451310893)
          ·
            refine ⟨8592462713612419241585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22913233902966451310893 8592462713612419241585)
            ·
              refine ⟨6444347035209314431189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8592462713612419241585 6444347035209314431189)
              ·
                refine ⟨151039383637718306981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6444347035209314431189 151039383637718306981)
                ·
                  rfl

theorem cell22_3971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 7].length) (baseStart_3971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971 prefixEnd_3971 := by exact prefixLift 3971
  have htrace : WordTrace (prefixWord ++ tailWord_3971) baseStart_3971 baseEnd_3971 := by
    simpa [prefixWord, tailWord_3971, baseEnd_3971] using wordTrace_append hprefix tailTrace_3971
  have hstable : (prefixWord ++ tailWord_3971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971).length < 2 ^ (prefixWord ++ tailWord_3971).sum := by decide
  have hdescent : baseEnd_3971 < baseStart_3971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 2, 3]
def baseStart_3975 : Nat := 118140960795 + 3975 * 2 ^ 59
def prefixEnd_3975 : Nat := 4983230072969 + 3 ^ 40 * 3975 * 2
def baseEnd_3975 : Nat := 1360723734484787662817

theorem tailTrace_3975 : CollatzResearch.WordTrace tailWord_3975 prefixEnd_3975 1360723734484787662817 := by
  unfold tailWord_3975
  simp only [CollatzResearch.WordTrace]
  refine ⟨144980160606728721061379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96653440404485814040919 144980160606728721061379)
  ·
    refine ⟨217470240910093081592069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144980160606728721061379 217470240910093081592069)
    ·
      refine ⟨40775670170642452798513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217470240910093081592069 40775670170642452798513)
      ·
        refine ⟨30581752627981839598885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40775670170642452798513 30581752627981839598885)
        ·
          refine ⟨5734078617746594924791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30581752627981839598885 5734078617746594924791)
          ·
            refine ⟨8601117926619892387187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734078617746594924791 8601117926619892387187)
            ·
              refine ⟨12901676889929838580781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601117926619892387187 12901676889929838580781)
              ·
                refine ⟨4838128833723689467793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12901676889929838580781 4838128833723689467793)
                ·
                  refine ⟨3628596625292767100845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4838128833723689467793 3628596625292767100845)
                  ·
                    refine ⟨1360723734484787662817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628596625292767100845 1360723734484787662817)
                    ·
                      rfl

theorem cell22_3975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_3975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975 prefixEnd_3975 := by exact prefixLift 3975
  have htrace : WordTrace (prefixWord ++ tailWord_3975) baseStart_3975 baseEnd_3975 := by
    simpa [prefixWord, tailWord_3975, baseEnd_3975] using wordTrace_append hprefix tailTrace_3975
  have hstable : (prefixWord ++ tailWord_3975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975).length < 2 ^ (prefixWord ++ tailWord_3975).sum := by decide
  have hdescent : baseEnd_3975 < baseStart_3975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 2, 5]
def baseStart_4031 : Nat := 118140960795 + 4031 * 2 ^ 59
def prefixEnd_4031 : Nat := 4983230072969 + 3 ^ 40 * 4031 * 2
def baseEnd_4031 : Nat := 1379893678919308262645

theorem tailTrace_4031 : CollatzResearch.WordTrace tailWord_4031 prefixEnd_4031 1379893678919308262645 := by
  unfold tailWord_4031
  simp only [CollatzResearch.WordTrace]
  refine ⟨147022648403850285099947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98015098935900190066631 147022648403850285099947)
  ·
    refine ⟨220533972605775427649921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147022648403850285099947 220533972605775427649921)
    ·
      refine ⟨165400479454331570737441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220533972605775427649921 165400479454331570737441)
      ·
        refine ⟨124050359590748678053081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165400479454331570737441 124050359590748678053081)
        ·
          refine ⟨93037769693061508539811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124050359590748678053081 93037769693061508539811)
          ·
            refine ⟨139556654539592262809717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93037769693061508539811 139556654539592262809717)
            ·
              refine ⟨13083436363086774638411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139556654539592262809717 13083436363086774638411)
              ·
                refine ⟨19625154544630161957617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13083436363086774638411 19625154544630161957617)
                ·
                  refine ⟨14718865908472621468213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19625154544630161957617 14718865908472621468213)
                  ·
                    refine ⟨1379893678919308262645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14718865908472621468213 1379893678919308262645)
                    ·
                      rfl

theorem cell22_4031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_4031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4031 prefixEnd_4031 := by exact prefixLift 4031
  have htrace : WordTrace (prefixWord ++ tailWord_4031) baseStart_4031 baseEnd_4031 := by
    simpa [prefixWord, tailWord_4031, baseEnd_4031] using wordTrace_append hprefix tailTrace_4031
  have hstable : (prefixWord ++ tailWord_4031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031).length < 2 ^ (prefixWord ++ tailWord_4031).sum := by decide
  have hdescent : baseEnd_4031 < baseStart_4031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_4076 : Nat := 118140960795 + 4076 * 2 ^ 59
def prefixEnd_4076 : Nat := 4983230072969 + 3 ^ 40 * 4076 * 2
def baseEnd_4076 : Nat := 1395298098554190887507

theorem tailTrace_4076 : CollatzResearch.WordTrace tailWord_4076 prefixEnd_4076 1395298098554190887507 := by
  unfold tailWord_4076
  simp only [CollatzResearch.WordTrace]
  refine ⟨74331966620411485244041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99109288827215313658721 74331966620411485244041)
  ·
    refine ⟨55748974965308613933031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74331966620411485244041 55748974965308613933031)
    ·
      refine ⟨83623462447962920899547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55748974965308613933031 83623462447962920899547)
      ·
        refine ⟨125435193671944381349321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83623462447962920899547 125435193671944381349321)
        ·
          refine ⟨94076395253958286011991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125435193671944381349321 94076395253958286011991)
          ·
            refine ⟨141114592880937429017987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94076395253958286011991 141114592880937429017987)
            ·
              refine ⟨211671889321406143526981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141114592880937429017987 211671889321406143526981)
              ·
                refine ⟨39688479247763651911309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211671889321406143526981 39688479247763651911309)
                ·
                  refine ⟨14883179717911369466741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39688479247763651911309 14883179717911369466741)
                  ·
                    refine ⟨1395298098554190887507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14883179717911369466741 1395298098554190887507)
                    ·
                      rfl

theorem cell22_4076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_4076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076 prefixEnd_4076 := by exact prefixLift 4076
  have htrace : WordTrace (prefixWord ++ tailWord_4076) baseStart_4076 baseEnd_4076 := by
    simpa [prefixWord, tailWord_4076, baseEnd_4076] using wordTrace_append hprefix tailTrace_4076
  have hstable : (prefixWord ++ tailWord_4076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076).length < 2 ^ (prefixWord ++ tailWord_4076).sum := by decide
  have hdescent : baseEnd_4076 < baseStart_4076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_4078 : Nat := 118140960795 + 4078 * 2 ^ 59
def prefixEnd_4078 : Nat := 4983230072969 + 3 ^ 40 * 4078 * 2
def baseEnd_4078 : Nat := 465327579808950779167

theorem tailTrace_4078 : CollatzResearch.WordTrace tailWord_4078 prefixEnd_4078 465327579808950779167 := by
  unfold tailWord_4078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592109904197164007611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99157919489051541373925 18592109904197164007611)
  ·
    refine ⟨27888164856295746011417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18592109904197164007611 27888164856295746011417)
    ·
      refine ⟨20916123642221809508563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27888164856295746011417 20916123642221809508563)
      ·
        refine ⟨31374185463332714262845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20916123642221809508563 31374185463332714262845)
        ·
          refine ⟨11765319548749767848567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31374185463332714262845 11765319548749767848567)
          ·
            refine ⟨17647979323124651772851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11765319548749767848567 17647979323124651772851)
            ·
              refine ⟨26471968984686977659277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17647979323124651772851 26471968984686977659277)
              ·
                refine ⟨9926988369257616622229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26471968984686977659277 9926988369257616622229)
                ·
                  refine ⟨465327579808950779167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9926988369257616622229 465327579808950779167)
                  ·
                    rfl

theorem cell22_4078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_4078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078 prefixEnd_4078 := by exact prefixLift 4078
  have htrace : WordTrace (prefixWord ++ tailWord_4078) baseStart_4078 baseEnd_4078 := by
    simpa [prefixWord, tailWord_4078, baseEnd_4078] using wordTrace_append hprefix tailTrace_4078
  have hstable : (prefixWord ++ tailWord_4078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078).length < 2 ^ (prefixWord ++ tailWord_4078).sum := by decide
  have hdescent : baseEnd_4078 < baseStart_4078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 1, 6]
def baseStart_4091 : Nat := 118140960795 + 4091 * 2 ^ 59
def prefixEnd_4091 : Nat := 4983230072969 + 3 ^ 40 * 4091 * 2
def baseEnd_4091 : Nat := 1400432905099151762461

theorem tailTrace_4091 : CollatzResearch.WordTrace tailWord_4091 prefixEnd_4091 1400432905099151762461 := by
  unfold tailWord_4091
  simp only [CollatzResearch.WordTrace]
  refine ⟨149211028186480532284127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99474018790987021522751 149211028186480532284127)
  ·
    refine ⟨223816542279720798426191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149211028186480532284127 223816542279720798426191)
    ·
      refine ⟨335724813419581197639287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223816542279720798426191 335724813419581197639287)
      ·
        refine ⟨503587220129371796458931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335724813419581197639287 503587220129371796458931)
        ·
          refine ⟨755380830194057694688397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503587220129371796458931 755380830194057694688397)
          ·
            refine ⟨283267811322771635508149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 755380830194057694688397 283267811322771635508149)
            ·
              refine ⟨26556357311509840828889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283267811322771635508149 26556357311509840828889)
              ·
                refine ⟨19917267983632380621667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26556357311509840828889 19917267983632380621667)
                ·
                  refine ⟨29875901975448570932501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19917267983632380621667 29875901975448570932501)
                  ·
                    refine ⟨1400432905099151762461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29875901975448570932501 1400432905099151762461)
                    ·
                      rfl

theorem cell22_4091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_4091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4091 prefixEnd_4091 := by exact prefixLift 4091
  have htrace : WordTrace (prefixWord ++ tailWord_4091) baseStart_4091 baseEnd_4091 := by
    simpa [prefixWord, tailWord_4091, baseEnd_4091] using wordTrace_append hprefix tailTrace_4091
  have hstable : (prefixWord ++ tailWord_4091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091).length < 2 ^ (prefixWord ++ tailWord_4091).sum := by decide
  have hdescent : baseEnd_4091 < baseStart_4091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_4093 : Nat := 118140960795 + 4093 * 2 ^ 59
def prefixEnd_4093 : Nat := 4983230072969 + 3 ^ 40 * 4093 * 2
def baseEnd_4093 : Nat := 1401117545971813212455

theorem tailTrace_4093 : CollatzResearch.WordTrace tailWord_4093 prefixEnd_4093 1401117545971813212455 := by
  unfold tailWord_4093
  simp only [CollatzResearch.WordTrace]
  refine ⟨149283974179234873856933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99522649452823249237955 149283974179234873856933)
  ·
    refine ⟨27990745158606538848175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149283974179234873856933 27990745158606538848175)
    ·
      refine ⟨41986117737909808272263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27990745158606538848175 41986117737909808272263)
      ·
        refine ⟨62979176606864712408395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41986117737909808272263 62979176606864712408395)
        ·
          refine ⟨94468764910297068612593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62979176606864712408395 94468764910297068612593)
          ·
            refine ⟨70851573682722801459445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94468764910297068612593 70851573682722801459445)
            ·
              refine ⟨6642335032755262636823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70851573682722801459445 6642335032755262636823)
              ·
                refine ⟨9963502549132893955235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642335032755262636823 9963502549132893955235)
                ·
                  refine ⟨14945253823699340932853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9963502549132893955235 14945253823699340932853)
                  ·
                    refine ⟨1401117545971813212455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14945253823699340932853 1401117545971813212455)
                    ·
                      rfl

theorem cell22_4093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_4093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4093 prefixEnd_4093 := by exact prefixLift 4093
  have htrace : WordTrace (prefixWord ++ tailWord_4093) baseStart_4093 baseEnd_4093 := by
    simpa [prefixWord, tailWord_4093, baseEnd_4093] using wordTrace_append hprefix tailTrace_4093
  have hstable : (prefixWord ++ tailWord_4093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093).length < 2 ^ (prefixWord ++ tailWord_4093).sum := by decide
  have hdescent : baseEnd_4093 < baseStart_4093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_4108 : Nat := 118140960795 + 4108 * 2 ^ 59
def prefixEnd_4108 : Nat := 4983230072969 + 3 ^ 40 * 4108 * 2
def baseEnd_4108 : Nat := 1406252352516774087409

theorem tailTrace_4108 : CollatzResearch.WordTrace tailWord_4108 prefixEnd_4108 1406252352516774087409 := by
  unfold tailWord_4108
  simp only [CollatzResearch.WordTrace]
  refine ⟨74915534562446217826489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99887379416594957101985 74915534562446217826489)
  ·
    refine ⟨56186650921834663369867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74915534562446217826489 56186650921834663369867)
    ·
      refine ⟨84279976382751995054801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56186650921834663369867 84279976382751995054801)
      ·
        refine ⟨63209982287063996291101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84279976382751995054801 63209982287063996291101)
        ·
          refine ⟨23703743357648998609163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63209982287063996291101 23703743357648998609163)
          ·
            refine ⟨35555615036473497913745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23703743357648998609163 35555615036473497913745)
            ·
              refine ⟨26666711277355123435309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35555615036473497913745 26666711277355123435309)
              ·
                refine ⟨10000016729008171288241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26666711277355123435309 10000016729008171288241)
                ·
                  refine ⟨7500012546756128466181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10000016729008171288241 7500012546756128466181)
                  ·
                    refine ⟨1406252352516774087409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7500012546756128466181 1406252352516774087409)
                    ·
                      rfl

theorem cell22_4108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_4108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4108 prefixEnd_4108 := by exact prefixLift 4108
  have htrace : WordTrace (prefixWord ++ tailWord_4108) baseStart_4108 baseEnd_4108 := by
    simpa [prefixWord, tailWord_4108, baseEnd_4108] using wordTrace_append hprefix tailTrace_4108
  have hstable : (prefixWord ++ tailWord_4108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108).length < 2 ^ (prefixWord ++ tailWord_4108).sum := by decide
  have hdescent : baseEnd_4108 < baseStart_4108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4125 : Nat := 118140960795 + 4125 * 2 ^ 59
def prefixEnd_4125 : Nat := 4983230072969 + 3 ^ 40 * 4125 * 2
def baseEnd_4125 : Nat := 1412071799934396412357

theorem tailTrace_4125 : CollatzResearch.WordTrace tailWord_4125 prefixEnd_4125 1412071799934396412357 := by
  unfold tailWord_4125
  simp only [CollatzResearch.WordTrace]
  refine ⟨150451110063304339021829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100300740042202892681219 150451110063304339021829)
  ·
    refine ⟨28209583136869563566593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150451110063304339021829 28209583136869563566593)
    ·
      refine ⟨21157187352652172674945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28209583136869563566593 21157187352652172674945)
      ·
        refine ⟨15867890514489129506209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21157187352652172674945 15867890514489129506209)
        ·
          refine ⟨11900917885866847129657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15867890514489129506209 11900917885866847129657)
          ·
            refine ⟨8925688414400135347243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11900917885866847129657 8925688414400135347243)
            ·
              refine ⟨13388532621600203020865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925688414400135347243 13388532621600203020865)
              ·
                refine ⟨10041399466200152265649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13388532621600203020865 10041399466200152265649)
                ·
                  refine ⟨7531049599650114199237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10041399466200152265649 7531049599650114199237)
                  ·
                    refine ⟨1412071799934396412357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7531049599650114199237 1412071799934396412357)
                    ·
                      rfl

theorem cell22_4125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125 prefixEnd_4125 := by exact prefixLift 4125
  have htrace : WordTrace (prefixWord ++ tailWord_4125) baseStart_4125 baseEnd_4125 := by
    simpa [prefixWord, tailWord_4125, baseEnd_4125] using wordTrace_append hprefix tailTrace_4125
  have hstable : (prefixWord ++ tailWord_4125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125).length < 2 ^ (prefixWord ++ tailWord_4125).sum := by decide
  have hdescent : baseEnd_4125 < baseStart_4125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_4232 : Nat := 118140960795 + 4232 * 2 ^ 59
def prefixEnd_4232 : Nat := 4983230072969 + 3 ^ 40 * 4232 * 2
def baseEnd_4232 : Nat := 1448700086621783987029

theorem tailTrace_4232 : CollatzResearch.WordTrace tailWord_4232 prefixEnd_4232 1448700086621783987029 := by
  unfold tailWord_4232
  simp only [CollatzResearch.WordTrace]
  refine ⟨77176860337830806583475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102902480450441075444633 77176860337830806583475)
  ·
    refine ⟨115765290506746209875213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77176860337830806583475 115765290506746209875213)
    ·
      refine ⟨43411983940029828703205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115765290506746209875213 43411983940029828703205)
      ·
        refine ⟨8139746988755592881851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43411983940029828703205 8139746988755592881851)
        ·
          refine ⟨12209620483133389322777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8139746988755592881851 12209620483133389322777)
          ·
            refine ⟨9157215362350041992083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12209620483133389322777 9157215362350041992083)
            ·
              refine ⟨13735823043525062988125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9157215362350041992083 13735823043525062988125)
              ·
                refine ⟨5150933641321898620547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13735823043525062988125 5150933641321898620547)
                ·
                  refine ⟨7726400461982847930821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150933641321898620547 7726400461982847930821)
                  ·
                    refine ⟨1448700086621783987029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7726400461982847930821 1448700086621783987029)
                    ·
                      rfl

theorem cell22_4232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_4232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4232 prefixEnd_4232 := by exact prefixLift 4232
  have htrace : WordTrace (prefixWord ++ tailWord_4232) baseStart_4232 baseEnd_4232 := by
    simpa [prefixWord, tailWord_4232, baseEnd_4232] using wordTrace_append hprefix tailTrace_4232
  have hstable : (prefixWord ++ tailWord_4232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232).length < 2 ^ (prefixWord ++ tailWord_4232).sum := by decide
  have hdescent : baseEnd_4232 < baseStart_4232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 4, 4]
def baseStart_4243 : Nat := 118140960795 + 4243 * 2 ^ 59
def prefixEnd_4243 : Nat := 4983230072969 + 3 ^ 40 * 4243 * 2
def baseEnd_4243 : Nat := 1452465611421421961995

theorem tailTrace_4243 : CollatzResearch.WordTrace tailWord_4243 prefixEnd_4243 1452465611421421961995 := by
  unfold tailWord_4243
  simp only [CollatzResearch.WordTrace]
  refine ⟨154754923635810491817383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103169949090540327878255 154754923635810491817383)
  ·
    refine ⟨232132385453715737726075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154754923635810491817383 232132385453715737726075)
    ·
      refine ⟨348198578180573606589113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232132385453715737726075 348198578180573606589113)
      ·
        refine ⟨261148933635430204941835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348198578180573606589113 261148933635430204941835)
        ·
          refine ⟨391723400453145307412753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261148933635430204941835 391723400453145307412753)
          ·
            refine ⟨293792550339858980559565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391723400453145307412753 293792550339858980559565)
            ·
              refine ⟨110172206377447117709837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293792550339858980559565 110172206377447117709837)
              ·
                refine ⟨41314577391542669141189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110172206377447117709837 41314577391542669141189)
                ·
                  refine ⟨7746483260914250463973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41314577391542669141189 7746483260914250463973)
                  ·
                    refine ⟨1452465611421421961995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7746483260914250463973 1452465611421421961995)
                    ·
                      rfl

theorem cell22_4243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_4243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4243 prefixEnd_4243 := by exact prefixLift 4243
  have htrace : WordTrace (prefixWord ++ tailWord_4243) baseStart_4243 baseEnd_4243 := by
    simpa [prefixWord, tailWord_4243, baseEnd_4243] using wordTrace_append hprefix tailTrace_4243
  have hstable : (prefixWord ++ tailWord_4243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243).length < 2 ^ (prefixWord ++ tailWord_4243).sum := by decide
  have hdescent : baseEnd_4243 < baseStart_4243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_4245 : Nat := 118140960795 + 4245 * 2 ^ 59
def prefixEnd_4245 : Nat := 4983230072969 + 3 ^ 40 * 4245 * 2
def baseEnd_4245 : Nat := 1453150252294083411989

theorem tailTrace_4245 : CollatzResearch.WordTrace tailWord_4245 prefixEnd_4245 1453150252294083411989 := by
  unfold tailWord_4245
  simp only [CollatzResearch.WordTrace]
  refine ⟨154827869628564833390189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103218579752376555593459 154827869628564833390189)
  ·
    refine ⟨58060451110711812521321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154827869628564833390189 58060451110711812521321)
    ·
      refine ⟨43545338333033859390991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58060451110711812521321 43545338333033859390991)
      ·
        refine ⟨65318007499550789086487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43545338333033859390991 65318007499550789086487)
        ·
          refine ⟨97977011249326183629731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65318007499550789086487 97977011249326183629731)
          ·
            refine ⟨146965516873989275444597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97977011249326183629731 146965516873989275444597)
            ·
              refine ⟨13778017206936494572931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146965516873989275444597 13778017206936494572931)
              ·
                refine ⟨20667025810404741859397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13778017206936494572931 20667025810404741859397)
                ·
                  refine ⟨3875067339450889098637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20667025810404741859397 3875067339450889098637)
                  ·
                    refine ⟨1453150252294083411989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3875067339450889098637 1453150252294083411989)
                    ·
                      rfl

theorem cell22_4245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_4245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4245 prefixEnd_4245 := by exact prefixLift 4245
  have htrace : WordTrace (prefixWord ++ tailWord_4245) baseStart_4245 baseEnd_4245 := by
    simpa [prefixWord, tailWord_4245, baseEnd_4245] using wordTrace_append hprefix tailTrace_4245
  have hstable : (prefixWord ++ tailWord_4245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245).length < 2 ^ (prefixWord ++ tailWord_4245).sum := by decide
  have hdescent : baseEnd_4245 < baseStart_4245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 7]
def baseStart_4303 : Nat := 118140960795 + 4303 * 2 ^ 59
def prefixEnd_4303 : Nat := 4983230072969 + 3 ^ 40 * 4303 * 2
def baseEnd_4303 : Nat := 491001612533755153937

theorem tailTrace_4303 : CollatzResearch.WordTrace tailWord_4303 prefixEnd_4303 491001612533755153937 := by
  unfold tailWord_4303
  simp only [CollatzResearch.WordTrace]
  refine ⟨156943303418440739001563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104628868945627159334375 156943303418440739001563)
  ·
    refine ⟨235414955127661108502345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156943303418440739001563 235414955127661108502345)
    ·
      refine ⟨176561216345745831376759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235414955127661108502345 176561216345745831376759)
      ·
        refine ⟨264841824518618747065139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176561216345745831376759 264841824518618747065139)
        ·
          refine ⟨397262736777928120597709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264841824518618747065139 397262736777928120597709)
          ·
            refine ⟨148973526291723045224141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 397262736777928120597709 148973526291723045224141)
            ·
              refine ⟨55865072359396141959053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148973526291723045224141 55865072359396141959053)
              ·
                refine ⟨20949402134773553234645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55865072359396141959053 20949402134773553234645)
                ·
                  refine ⟨491001612533755153937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20949402134773553234645 491001612533755153937)
                  ·
                    rfl

theorem cell22_4303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 7].length) (baseStart_4303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4303 prefixEnd_4303 := by exact prefixLift 4303
  have htrace : WordTrace (prefixWord ++ tailWord_4303) baseStart_4303 baseEnd_4303 := by
    simpa [prefixWord, tailWord_4303, baseEnd_4303] using wordTrace_append hprefix tailTrace_4303
  have hstable : (prefixWord ++ tailWord_4303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303).length < 2 ^ (prefixWord ++ tailWord_4303).sum := by decide
  have hdescent : baseEnd_4303 < baseStart_4303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4320 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 5]
def baseStart_4320 : Nat := 118140960795 + 4320 * 2 ^ 59
def prefixEnd_4320 : Nat := 4983230072969 + 3 ^ 40 * 4320 * 2
def baseEnd_4320 : Nat := 492941428339629262253

theorem tailTrace_4320 : CollatzResearch.WordTrace tailWord_4320 prefixEnd_4320 492941428339629262253 := by
  unfold tailWord_4320
  simp only [CollatzResearch.WordTrace]
  refine ⟨78781672178426321185207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105042229571235094913609 78781672178426321185207)
  ·
    refine ⟨118172508267639481777811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78781672178426321185207 118172508267639481777811)
    ·
      refine ⟨177258762401459222666717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118172508267639481777811 177258762401459222666717)
      ·
        refine ⟨66472035900547208500019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177258762401459222666717 66472035900547208500019)
        ·
          refine ⟨99708053850820812750029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66472035900547208500019 99708053850820812750029)
          ·
            refine ⟨37390520194057804781261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99708053850820812750029 37390520194057804781261)
            ·
              refine ⟨14021445072771676792973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37390520194057804781261 14021445072771676792973)
              ·
                refine ⟨5258041902289378797365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14021445072771676792973 5258041902289378797365)
                ·
                  refine ⟨492941428339629262253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5258041902289378797365 492941428339629262253)
                  ·
                    rfl

theorem cell22_4320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_4320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4320 prefixEnd_4320 := by exact prefixLift 4320
  have htrace : WordTrace (prefixWord ++ tailWord_4320) baseStart_4320 baseEnd_4320 := by
    simpa [prefixWord, tailWord_4320, baseEnd_4320] using wordTrace_append hprefix tailTrace_4320
  have hstable : (prefixWord ++ tailWord_4320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4320).length < 2 ^ (prefixWord ++ tailWord_4320).sum := by decide
  have hdescent : baseEnd_4320 < baseStart_4320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4354 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4354 : Nat := 118140960795 + 4354 * 2 ^ 59
def prefixEnd_4354 : Nat := 4983230072969 + 3 ^ 40 * 4354 * 2
def baseEnd_4354 : Nat := 496821059951377478885

theorem tailTrace_4354 : CollatzResearch.WordTrace tailWord_4354 prefixEnd_4354 496821059951377478885 := by
  unfold tailWord_4354
  simp only [CollatzResearch.WordTrace]
  refine ⟨39700856558419112277029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105868950822450966072077 39700856558419112277029)
  ·
    refine ⟨7443910604703583551943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39700856558419112277029 7443910604703583551943)
    ·
      refine ⟨11165865907055375327915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7443910604703583551943 11165865907055375327915)
      ·
        refine ⟨16748798860583062991873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11165865907055375327915 16748798860583062991873)
        ·
          refine ⟨12561599145437297243905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16748798860583062991873 12561599145437297243905)
          ·
            refine ⟨9421199359077972932929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12561599145437297243905 9421199359077972932929)
            ·
              refine ⟨7065899519308479699697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9421199359077972932929 7065899519308479699697)
              ·
                refine ⟨5299424639481359774773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7065899519308479699697 5299424639481359774773)
                ·
                  refine ⟨496821059951377478885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5299424639481359774773 496821059951377478885)
                  ·
                    rfl

theorem cell22_4354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4354 prefixEnd_4354 := by exact prefixLift 4354
  have htrace : WordTrace (prefixWord ++ tailWord_4354) baseStart_4354 baseEnd_4354 := by
    simpa [prefixWord, tailWord_4354, baseEnd_4354] using wordTrace_append hprefix tailTrace_4354
  have hstable : (prefixWord ++ tailWord_4354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4354).length < 2 ^ (prefixWord ++ tailWord_4354).sum := by decide
  have hdescent : baseEnd_4354 < baseStart_4354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4401 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 1, 4]
def baseStart_4401 : Nat := 118140960795 + 4401 * 2 ^ 59
def prefixEnd_4401 : Nat := 4983230072969 + 3 ^ 40 * 4401 * 2
def baseEnd_4401 : Nat := 1506552240361676511511

theorem tailTrace_4401 : CollatzResearch.WordTrace tailWord_4401 prefixEnd_4401 1506552240361676511511 := by
  unfold tailWord_4401
  simp only [CollatzResearch.WordTrace]
  refine ⟨160517657063403476069057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107011771375602317379371 160517657063403476069057)
  ·
    refine ⟨120388242797552607051793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160517657063403476069057 120388242797552607051793)
    ·
      refine ⟨90291182098164455288845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120388242797552607051793 90291182098164455288845)
      ·
        refine ⟨33859193286811670733317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90291182098164455288845 33859193286811670733317)
        ·
          refine ⟨6348598741277188262497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33859193286811670733317 6348598741277188262497)
          ·
            refine ⟨4761449055957891196873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6348598741277188262497 4761449055957891196873)
            ·
              refine ⟨3571086791968418397655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4761449055957891196873 3571086791968418397655)
              ·
                refine ⟨5356630187952627596483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571086791968418397655 5356630187952627596483)
                ·
                  refine ⟨8034945281928941394725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356630187952627596483 8034945281928941394725)
                  ·
                    refine ⟨1506552240361676511511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8034945281928941394725 1506552240361676511511)
                    ·
                      rfl

theorem cell22_4401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_4401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4401 prefixEnd_4401 := by exact prefixLift 4401
  have htrace : WordTrace (prefixWord ++ tailWord_4401) baseStart_4401 baseEnd_4401 := by
    simpa [prefixWord, tailWord_4401, baseEnd_4401] using wordTrace_append hprefix tailTrace_4401
  have hstable : (prefixWord ++ tailWord_4401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4401).length < 2 ^ (prefixWord ++ tailWord_4401).sum := by decide
  have hdescent : baseEnd_4401 < baseStart_4401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4410 : List Nat := [3, 1, 1, 1, 4, 3, 9]
def baseStart_4410 : Nat := 118140960795 + 4410 * 2 ^ 59
def prefixEnd_4410 : Nat := 4983230072969 + 3 ^ 40 * 4410 * 2
def baseEnd_4410 : Nat := 55912337936616779129

theorem tailTrace_4410 : CollatzResearch.WordTrace tailWord_4410 prefixEnd_4410 55912337936616779129 := by
  unfold tailWord_4410
  simp only [CollatzResearch.WordTrace]
  refine ⟨40211478507699503286671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107230609353865342097789 40211478507699503286671)
  ·
    refine ⟨60317217761549254930007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40211478507699503286671 60317217761549254930007)
    ·
      refine ⟨90475826642323882395011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60317217761549254930007 90475826642323882395011)
      ·
        refine ⟨135713739963485823592517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90475826642323882395011 135713739963485823592517)
        ·
          refine ⟨25446326243153591923597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135713739963485823592517 25446326243153591923597)
          ·
            refine ⟨9542372341182596971349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25446326243153591923597 9542372341182596971349)
            ·
              refine ⟨55912337936616779129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9542372341182596971349 55912337936616779129)
              ·
                rfl

theorem cell22_4410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 9].length) (baseStart_4410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4410 prefixEnd_4410 := by exact prefixLift 4410
  have htrace : WordTrace (prefixWord ++ tailWord_4410) baseStart_4410 baseEnd_4410 := by
    simpa [prefixWord, tailWord_4410, baseEnd_4410] using wordTrace_append hprefix tailTrace_4410
  have hstable : (prefixWord ++ tailWord_4410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410).length < 2 ^ (prefixWord ++ tailWord_4410).sum := by decide
  have hdescent : baseEnd_4410 < baseStart_4410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_4414 : Nat := 118140960795 + 4414 * 2 ^ 59
def prefixEnd_4414 : Nat := 4983230072969 + 3 ^ 40 * 4414 * 2
def baseEnd_4414 : Nat := 1511002406033975936471

theorem tailTrace_4414 : CollatzResearch.WordTrace tailWord_4414 prefixEnd_4414 1511002406033975936471 := by
  unfold tailWord_4414
  simp only [CollatzResearch.WordTrace]
  refine ⟨20123975752038337036537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107327870677537797528197 20123975752038337036537)
  ·
    refine ⟨15092981814028752777403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20123975752038337036537 15092981814028752777403)
    ·
      refine ⟨22639472721043129166105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15092981814028752777403 22639472721043129166105)
      ·
        refine ⟨16979604540782346874579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22639472721043129166105 16979604540782346874579)
        ·
          refine ⟨25469406811173520311869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16979604540782346874579 25469406811173520311869)
          ·
            refine ⟨9551027554190070116951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25469406811173520311869 9551027554190070116951)
            ·
              refine ⟨14326541331285105175427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9551027554190070116951 14326541331285105175427)
              ·
                refine ⟨21489811996927657763141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14326541331285105175427 21489811996927657763141)
                ·
                  refine ⟨4029339749423935830589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21489811996927657763141 4029339749423935830589)
                  ·
                    refine ⟨1511002406033975936471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4029339749423935830589 1511002406033975936471)
                    ·
                      rfl

theorem cell22_4414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_4414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4414 prefixEnd_4414 := by exact prefixLift 4414
  have htrace : WordTrace (prefixWord ++ tailWord_4414) baseStart_4414 baseEnd_4414 := by
    simpa [prefixWord, tailWord_4414, baseEnd_4414] using wordTrace_append hprefix tailTrace_4414
  have hstable : (prefixWord ++ tailWord_4414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414).length < 2 ^ (prefixWord ++ tailWord_4414).sum := by decide
  have hdescent : baseEnd_4414 < baseStart_4414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4444 : List Nat := [2, 2, 4, 3, 1, 1, 1, 8]
def baseStart_4444 : Nat := 118140960795 + 4444 * 2 ^ 59
def prefixEnd_4444 : Nat := 4983230072969 + 3 ^ 40 * 4444 * 2
def baseEnd_4444 : Nat := 169030224347099742931

theorem tailTrace_4444 : CollatzResearch.WordTrace tailWord_4444 prefixEnd_4444 169030224347099742931 := by
  unfold tailWord_4444
  simp only [CollatzResearch.WordTrace]
  refine ⟨81042997953810909942193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108057330605081213256257 81042997953810909942193)
  ·
    refine ⟨60782248465358182456645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81042997953810909942193 60782248465358182456645)
    ·
      refine ⟨11396671587254659210621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60782248465358182456645 11396671587254659210621)
      ·
        refine ⟨4273751845220497203983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11396671587254659210621 4273751845220497203983)
        ·
          refine ⟨6410627767830745805975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273751845220497203983 6410627767830745805975)
          ·
            refine ⟨9615941651746118708963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410627767830745805975 9615941651746118708963)
            ·
              refine ⟨14423912477619178063445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9615941651746118708963 14423912477619178063445)
              ·
                refine ⟨169030224347099742931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 14423912477619178063445 169030224347099742931)
                ·
                  rfl

theorem cell22_4444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 8].length) (baseStart_4444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4444 prefixEnd_4444 := by exact prefixLift 4444
  have htrace : WordTrace (prefixWord ++ tailWord_4444) baseStart_4444 baseEnd_4444 := by
    simpa [prefixWord, tailWord_4444, baseEnd_4444] using wordTrace_append hprefix tailTrace_4444
  have hstable : (prefixWord ++ tailWord_4444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4444).length < 2 ^ (prefixWord ++ tailWord_4444).sum := by decide
  have hdescent : baseEnd_4444 < baseStart_4444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4482 : Nat := 118140960795 + 4482 * 2 ^ 59
def prefixEnd_4482 : Nat := 4983230072969 + 3 ^ 40 * 4482 * 2
def baseEnd_4482 : Nat := 1534280195704465236263

theorem tailTrace_4482 : CollatzResearch.WordTrace tailWord_4482 prefixEnd_4482 1534280195704465236263 := by
  unfold tailWord_4482
  simp only [CollatzResearch.WordTrace]
  refine ⟨40867992442488577441925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108981313179969539845133 40867992442488577441925)
  ·
    refine ⟨7662748582966608270361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40867992442488577441925 7662748582966608270361)
    ·
      refine ⟨5747061437224956202771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7662748582966608270361 5747061437224956202771)
      ·
        refine ⟨8620592155837434304157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5747061437224956202771 8620592155837434304157)
        ·
          refine ⟨3232722058439037864059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8620592155837434304157 3232722058439037864059)
          ·
            refine ⟨4849083087658556796089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232722058439037864059 4849083087658556796089)
            ·
              refine ⟨3636812315743917597067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4849083087658556796089 3636812315743917597067)
              ·
                refine ⟨5455218473615876395601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636812315743917597067 5455218473615876395601)
                ·
                  refine ⟨4091413855211907296701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5455218473615876395601 4091413855211907296701)
                  ·
                    refine ⟨1534280195704465236263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4091413855211907296701 1534280195704465236263)
                    ·
                      rfl

theorem cell22_4482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4482 prefixEnd_4482 := by exact prefixLift 4482
  have htrace : WordTrace (prefixWord ++ tailWord_4482) baseStart_4482 baseEnd_4482 := by
    simpa [prefixWord, tailWord_4482, baseEnd_4482] using wordTrace_append hprefix tailTrace_4482
  have hstable : (prefixWord ++ tailWord_4482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482).length < 2 ^ (prefixWord ++ tailWord_4482).sum := by decide
  have hdescent : baseEnd_4482 < baseStart_4482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_4485 : Nat := 118140960795 + 4485 * 2 ^ 59
def prefixEnd_4485 : Nat := 4983230072969 + 3 ^ 40 * 4485 * 2
def baseEnd_4485 : Nat := 1535307157013457411253

theorem tailTrace_4485 : CollatzResearch.WordTrace tailWord_4485 prefixEnd_4485 1535307157013457411253 := by
  unfold tailWord_4485
  simp only [CollatzResearch.WordTrace]
  refine ⟨163581388759085822126909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109054259172723881417939 163581388759085822126909)
  ·
    refine ⟨61343020784657183297591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163581388759085822126909 61343020784657183297591)
    ·
      refine ⟨92014531176985774946387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61343020784657183297591 92014531176985774946387)
      ·
        refine ⟨138021796765478662419581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92014531176985774946387 138021796765478662419581)
        ·
          refine ⟨51758173787054498407343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138021796765478662419581 51758173787054498407343)
          ·
            refine ⟨77637260680581747611015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51758173787054498407343 77637260680581747611015)
            ·
              refine ⟨116455891020872621416523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77637260680581747611015 116455891020872621416523)
              ·
                refine ⟨174683836531308932124785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116455891020872621416523 174683836531308932124785)
                ·
                  refine ⟨131012877398481699093589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174683836531308932124785 131012877398481699093589)
                  ·
                    refine ⟨1535307157013457411253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 131012877398481699093589 1535307157013457411253)
                    ·
                      rfl

theorem cell22_4485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_4485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4485 prefixEnd_4485 := by exact prefixLift 4485
  have htrace : WordTrace (prefixWord ++ tailWord_4485) baseStart_4485 baseEnd_4485 := by
    simpa [prefixWord, tailWord_4485, baseEnd_4485] using wordTrace_append hprefix tailTrace_4485
  have hstable : (prefixWord ++ tailWord_4485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485).length < 2 ^ (prefixWord ++ tailWord_4485).sum := by decide
  have hdescent : baseEnd_4485 < baseStart_4485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 5]
def baseStart_4489 : Nat := 118140960795 + 4489 * 2 ^ 59
def prefixEnd_4489 : Nat := 4983230072969 + 3 ^ 40 * 4489 * 2
def baseEnd_4489 : Nat := 512225479586260103747

theorem tailTrace_4489 : CollatzResearch.WordTrace tailWord_4489 prefixEnd_4489 512225479586260103747 := by
  unfold tailWord_4489
  simp only [CollatzResearch.WordTrace]
  refine ⟨163727280744594505272521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109151520496396336848347 163727280744594505272521)
  ·
    refine ⟨122795460558445878954391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163727280744594505272521 122795460558445878954391)
    ·
      refine ⟨184193190837668818431587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122795460558445878954391 184193190837668818431587)
      ·
        refine ⟨276289786256503227647381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184193190837668818431587 276289786256503227647381)
        ·
          refine ⟨12951083730773588795971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 276289786256503227647381 12951083730773588795971)
          ·
            refine ⟨19426625596160383193957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12951083730773588795971 19426625596160383193957)
            ·
              refine ⟨3642492299280071848867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19426625596160383193957 3642492299280071848867)
              ·
                refine ⟨5463738448920107773301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3642492299280071848867 5463738448920107773301)
                ·
                  refine ⟨512225479586260103747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5463738448920107773301 512225479586260103747)
                  ·
                    rfl

theorem cell22_4489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_4489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4489 prefixEnd_4489 := by exact prefixLift 4489
  have htrace : WordTrace (prefixWord ++ tailWord_4489) baseStart_4489 baseEnd_4489 := by
    simpa [prefixWord, tailWord_4489, baseEnd_4489] using wordTrace_append hprefix tailTrace_4489
  have hstable : (prefixWord ++ tailWord_4489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489).length < 2 ^ (prefixWord ++ tailWord_4489).sum := by decide
  have hdescent : baseEnd_4489 < baseStart_4489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4564 : Nat := 118140960795 + 4564 * 2 ^ 59
def prefixEnd_4564 : Nat := 4983230072969 + 3 ^ 40 * 4564 * 2
def baseEnd_4564 : Nat := 1562350471483584686011

theorem tailTrace_4564 : CollatzResearch.WordTrace tailWord_4564 prefixEnd_4564 1562350471483584686011 := by
  unfold tailWord_4564
  simp only [CollatzResearch.WordTrace]
  refine ⟨83231377736441157126373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110975170315254876168497 83231377736441157126373)
  ·
    refine ⟨15605883325582716961195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83231377736441157126373 15605883325582716961195)
    ·
      refine ⟨23408824988374075441793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15605883325582716961195 23408824988374075441793)
      ·
        refine ⟨17556618741280556581345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23408824988374075441793 17556618741280556581345)
        ·
          refine ⟨13167464055960417436009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17556618741280556581345 13167464055960417436009)
          ·
            refine ⟨9875598041970313077007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13167464055960417436009 9875598041970313077007)
            ·
              refine ⟨14813397062955469615511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9875598041970313077007 14813397062955469615511)
              ·
                refine ⟨22220095594433204423267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14813397062955469615511 22220095594433204423267)
                ·
                  refine ⟨33330143391649806634901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22220095594433204423267 33330143391649806634901)
                  ·
                    refine ⟨1562350471483584686011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33330143391649806634901 1562350471483584686011)
                    ·
                      rfl

theorem cell22_4564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4564 prefixEnd_4564 := by exact prefixLift 4564
  have htrace : WordTrace (prefixWord ++ tailWord_4564) baseStart_4564 baseEnd_4564 := by
    simpa [prefixWord, tailWord_4564, baseEnd_4564] using wordTrace_append hprefix tailTrace_4564
  have hstable : (prefixWord ++ tailWord_4564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564).length < 2 ^ (prefixWord ++ tailWord_4564).sum := by decide
  have hdescent : baseEnd_4564 < baseStart_4564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_4566 : Nat := 118140960795 + 4566 * 2 ^ 59
def prefixEnd_4566 : Nat := 4983230072969 + 3 ^ 40 * 4566 * 2
def baseEnd_4566 : Nat := 1563035112356246136005

theorem tailTrace_4566 : CollatzResearch.WordTrace tailWord_4566 prefixEnd_4566 1563035112356246136005 := by
  unfold tailWord_4566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10408481341602290989097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111023800977091103883701 10408481341602290989097)
  ·
    refine ⟨7806361006201718241823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10408481341602290989097 7806361006201718241823)
    ·
      refine ⟨11709541509302577362735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7806361006201718241823 11709541509302577362735)
      ·
        refine ⟨17564312263953866044103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11709541509302577362735 17564312263953866044103)
        ·
          refine ⟨26346468395930799066155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17564312263953866044103 26346468395930799066155)
          ·
            refine ⟨39519702593896198599233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26346468395930799066155 39519702593896198599233)
            ·
              refine ⟨29639776945422148949425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39519702593896198599233 29639776945422148949425)
              ·
                refine ⟨22229832709066611712069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29639776945422148949425 22229832709066611712069)
                ·
                  refine ⟨4168093632949989696013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22229832709066611712069 4168093632949989696013)
                  ·
                    refine ⟨1563035112356246136005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4168093632949989696013 1563035112356246136005)
                    ·
                      rfl

theorem cell22_4566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_4566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4566 prefixEnd_4566 := by exact prefixLift 4566
  have htrace : WordTrace (prefixWord ++ tailWord_4566) baseStart_4566 baseEnd_4566 := by
    simpa [prefixWord, tailWord_4566, baseEnd_4566] using wordTrace_append hprefix tailTrace_4566
  have hstable : (prefixWord ++ tailWord_4566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566).length < 2 ^ (prefixWord ++ tailWord_4566).sum := by decide
  have hdescent : baseEnd_4566 < baseStart_4566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_4684 : Nat := 118140960795 + 4684 * 2 ^ 59
def prefixEnd_4684 : Nat := 4983230072969 + 3 ^ 40 * 4684 * 2
def baseEnd_4684 : Nat := 1603428923843271685643

theorem tailTrace_4684 : CollatzResearch.WordTrace tailWord_4684 prefixEnd_4684 1603428923843271685643 := by
  unfold tailWord_4684
  simp only [CollatzResearch.WordTrace]
  refine ⟨85419757519071404310553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113893010025428539080737 85419757519071404310553)
  ·
    refine ⟨64064818139303553232915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85419757519071404310553 64064818139303553232915)
    ·
      refine ⟨96097227208955329849373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64064818139303553232915 96097227208955329849373)
      ·
        refine ⟨36036460203358248693515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96097227208955329849373 36036460203358248693515)
        ·
          refine ⟨54054690305037373040273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36036460203358248693515 54054690305037373040273)
          ·
            refine ⟨40541017728778029780205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54054690305037373040273 40541017728778029780205)
            ·
              refine ⟨15202881648291761167577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40541017728778029780205 15202881648291761167577)
              ·
                refine ⟨11402161236218820875683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15202881648291761167577 11402161236218820875683)
                ·
                  refine ⟨17103241854328231313525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11402161236218820875683 17103241854328231313525)
                  ·
                    refine ⟨1603428923843271685643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17103241854328231313525 1603428923843271685643)
                    ·
                      rfl

theorem cell22_4684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_4684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4684 prefixEnd_4684 := by exact prefixLift 4684
  have htrace : WordTrace (prefixWord ++ tailWord_4684) baseStart_4684 baseEnd_4684 := by
    simpa [prefixWord, tailWord_4684, baseEnd_4684] using wordTrace_append hprefix tailTrace_4684
  have hstable : (prefixWord ++ tailWord_4684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684).length < 2 ^ (prefixWord ++ tailWord_4684).sum := by decide
  have hdescent : baseEnd_4684 < baseStart_4684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_4718 : Nat := 118140960795 + 4718 * 2 ^ 59
def prefixEnd_4718 : Nat := 4983230072969 + 3 ^ 40 * 4718 * 2
def baseEnd_4718 : Nat := 1615067818678516335539

theorem tailTrace_4718 : CollatzResearch.WordTrace tailWord_4718 prefixEnd_4718 1615067818678516335539 := by
  unfold tailWord_4718
  simp only [CollatzResearch.WordTrace]
  refine ⟨21509949614370826919851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114719731276644410239205 21509949614370826919851)
  ·
    refine ⟨32264924421556240379777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21509949614370826919851 32264924421556240379777)
    ·
      refine ⟨24198693316167180284833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32264924421556240379777 24198693316167180284833)
      ·
        refine ⟨18149019987125385213625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24198693316167180284833 18149019987125385213625)
        ·
          refine ⟨13611764990344038910219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18149019987125385213625 13611764990344038910219)
          ·
            refine ⟨20417647485516058365329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13611764990344038910219 20417647485516058365329)
            ·
              refine ⟨15313235614137043773997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20417647485516058365329 15313235614137043773997)
              ·
                refine ⟨5742463355301391415249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15313235614137043773997 5742463355301391415249)
                ·
                  refine ⟨4306847516476043561437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5742463355301391415249 4306847516476043561437)
                  ·
                    refine ⟨1615067818678516335539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4306847516476043561437 1615067818678516335539)
                    ·
                      rfl

theorem cell22_4718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_4718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4718 prefixEnd_4718 := by exact prefixLift 4718
  have htrace : WordTrace (prefixWord ++ tailWord_4718) baseStart_4718 baseEnd_4718 := by
    simpa [prefixWord, tailWord_4718, baseEnd_4718] using wordTrace_append hprefix tailTrace_4718
  have hstable : (prefixWord ++ tailWord_4718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718).length < 2 ^ (prefixWord ++ tailWord_4718).sum := by decide
  have hdescent : baseEnd_4718 < baseStart_4718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4733 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_4733 : Nat := 118140960795 + 4733 * 2 ^ 59
def prefixEnd_4733 : Nat := 4983230072969 + 3 ^ 40 * 4733 * 2
def baseEnd_4733 : Nat := 1620202625223477210493

theorem tailTrace_4733 : CollatzResearch.WordTrace tailWord_4733 prefixEnd_4733 1620202625223477210493 := by
  unfold tailWord_4733
  simp only [CollatzResearch.WordTrace]
  refine ⟨172626691860624177154853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115084461240416118103235 172626691860624177154853)
  ·
    refine ⟨32367504723867033216535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172626691860624177154853 32367504723867033216535)
    ·
      refine ⟨48551257085800549824803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32367504723867033216535 48551257085800549824803)
      ·
        refine ⟨72826885628700824737205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48551257085800549824803 72826885628700824737205)
        ·
          refine ⟨6827520527690702319113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72826885628700824737205 6827520527690702319113)
          ·
            refine ⟨5120640395768026739335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6827520527690702319113 5120640395768026739335)
            ·
              refine ⟨7680960593652040109003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5120640395768026739335 7680960593652040109003)
              ·
                refine ⟨11521440890478060163505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7680960593652040109003 11521440890478060163505)
                ·
                  refine ⟨8641080667858545122629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11521440890478060163505 8641080667858545122629)
                  ·
                    refine ⟨1620202625223477210493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8641080667858545122629 1620202625223477210493)
                    ·
                      rfl

theorem cell22_4733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_4733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4733 prefixEnd_4733 := by exact prefixLift 4733
  have htrace : WordTrace (prefixWord ++ tailWord_4733) baseStart_4733 baseEnd_4733 := by
    simpa [prefixWord, tailWord_4733, baseEnd_4733] using wordTrace_append hprefix tailTrace_4733
  have hstable : (prefixWord ++ tailWord_4733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4733).length < 2 ^ (prefixWord ++ tailWord_4733).sum := by decide
  have hdescent : baseEnd_4733 < baseStart_4733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4759 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 7]
def baseStart_4759 : Nat := 118140960795 + 4759 * 2 ^ 59
def prefixEnd_4759 : Nat := 4983230072969 + 3 ^ 40 * 4759 * 2
def baseEnd_4759 : Nat := 543034318856025353471

theorem tailTrace_4759 : CollatzResearch.WordTrace tailWord_4759 prefixEnd_4759 543034318856025353471 := by
  unfold tailWord_4759
  simp only [CollatzResearch.WordTrace]
  refine ⟨173574989766430617601331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115716659844287078400887 173574989766430617601331)
  ·
    refine ⟨260362484649645926401997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173574989766430617601331 260362484649645926401997)
    ·
      refine ⟨97635931743617222400749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260362484649645926401997 97635931743617222400749)
      ·
        refine ⟨36613474403856458400281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97635931743617222400749 36613474403856458400281)
        ·
          refine ⟨27460105802892343800211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36613474403856458400281 27460105802892343800211)
          ·
            refine ⟨41190158704338515700317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27460105802892343800211 41190158704338515700317)
            ·
              refine ⟨15446309514126943387619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41190158704338515700317 15446309514126943387619)
              ·
                refine ⟨23169464271190415081429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15446309514126943387619 23169464271190415081429)
                ·
                  refine ⟨543034318856025353471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 23169464271190415081429 543034318856025353471)
                  ·
                    rfl

theorem cell22_4759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 7].length) (baseStart_4759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4759 prefixEnd_4759 := by exact prefixLift 4759
  have htrace : WordTrace (prefixWord ++ tailWord_4759) baseStart_4759 baseEnd_4759 := by
    simpa [prefixWord, tailWord_4759, baseEnd_4759] using wordTrace_append hprefix tailTrace_4759
  have hstable : (prefixWord ++ tailWord_4759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4759).length < 2 ^ (prefixWord ++ tailWord_4759).sum := by decide
  have hdescent : baseEnd_4759 < baseStart_4759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 1, 4]
def baseStart_4840 : Nat := 118140960795 + 4840 * 2 ^ 59
def prefixEnd_4840 : Nat := 4983230072969 + 3 ^ 40 * 4840 * 2
def baseEnd_4840 : Nat := 1656830911910864785165

theorem tailTrace_4840 : CollatzResearch.WordTrace tailWord_4840 prefixEnd_4840 1656830911910864785165 := by
  unfold tailWord_4840
  simp only [CollatzResearch.WordTrace]
  refine ⟨88264651236490725649987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117686201648654300866649 88264651236490725649987)
  ·
    refine ⟨132396976854736088474981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88264651236490725649987 132396976854736088474981)
    ·
      refine ⟨24824433160263016589059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132396976854736088474981 24824433160263016589059)
      ·
        refine ⟨37236649740394524883589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24824433160263016589059 37236649740394524883589)
        ·
          refine ⟨6981871826323973415673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37236649740394524883589 6981871826323973415673)
          ·
            refine ⟨5236403869742980061755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6981871826323973415673 5236403869742980061755)
            ·
              refine ⟨7854605804614470092633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236403869742980061755 7854605804614470092633)
              ·
                refine ⟨5890954353460852569475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7854605804614470092633 5890954353460852569475)
                ·
                  refine ⟨8836431530191278854213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5890954353460852569475 8836431530191278854213)
                  ·
                    refine ⟨1656830911910864785165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8836431530191278854213 1656830911910864785165)
                    ·
                      rfl

theorem cell22_4840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_4840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4840 prefixEnd_4840 := by exact prefixLift 4840
  have htrace : WordTrace (prefixWord ++ tailWord_4840) baseStart_4840 baseEnd_4840 := by
    simpa [prefixWord, tailWord_4840, baseEnd_4840] using wordTrace_append hprefix tailTrace_4840
  have hstable : (prefixWord ++ tailWord_4840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840).length < 2 ^ (prefixWord ++ tailWord_4840).sum := by decide
  have hdescent : baseEnd_4840 < baseStart_4840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849 : List Nat := [1, 2, 2, 2, 2, 2, 1, 10]
def baseStart_4849 : Nat := 118140960795 + 4849 * 2 ^ 59
def prefixEnd_4849 : Nat := 4983230072969 + 3 ^ 40 * 4849 * 2
def baseEnd_4849 : Nat := 184434643981982367793

theorem tailTrace_4849 : CollatzResearch.WordTrace tailWord_4849 prefixEnd_4849 184434643981982367793 := by
  unfold tailWord_4849
  simp only [CollatzResearch.WordTrace]
  refine ⟨176857559440375988377601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117905039626917325585067 176857559440375988377601)
  ·
    refine ⟨132643169580281991283201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176857559440375988377601 132643169580281991283201)
    ·
      refine ⟨99482377185211493462401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132643169580281991283201 99482377185211493462401)
      ·
        refine ⟨74611782888908620096801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99482377185211493462401 74611782888908620096801)
        ·
          refine ⟨55958837166681465072601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74611782888908620096801 55958837166681465072601)
          ·
            refine ⟨41969127875011098804451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55958837166681465072601 41969127875011098804451)
            ·
              refine ⟨62953691812516648206677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41969127875011098804451 62953691812516648206677)
              ·
                refine ⟨184434643981982367793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 62953691812516648206677 184434643981982367793)
                ·
                  rfl

theorem cell22_4849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 10].length) (baseStart_4849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4849 prefixEnd_4849 := by exact prefixLift 4849
  have htrace : WordTrace (prefixWord ++ tailWord_4849) baseStart_4849 baseEnd_4849 := by
    simpa [prefixWord, tailWord_4849, baseEnd_4849] using wordTrace_append hprefix tailTrace_4849
  have hstable : (prefixWord ++ tailWord_4849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849).length < 2 ^ (prefixWord ++ tailWord_4849).sum := by decide
  have hdescent : baseEnd_4849 < baseStart_4849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866 : List Nat := [3, 4, 1, 1, 1, 12]
def baseStart_4866 : Nat := 118140960795 + 4866 * 2 ^ 59
def prefixEnd_4866 : Nat := 4983230072969 + 3 ^ 40 * 4866 * 2
def baseEnd_4866 : Nat := 20564583250067452285

theorem tailTrace_4866 : CollatzResearch.WordTrace tailWord_4866 prefixEnd_4866 20564583250067452285 := by
  unfold tailWord_4866
  simp only [CollatzResearch.WordTrace]
  refine ⟨44369400094696972936613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118318400252525261164301 44369400094696972936613)
  ·
    refine ⟨8319262517755682425615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44369400094696972936613 8319262517755682425615)
    ·
      refine ⟨12478893776633523638423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8319262517755682425615 12478893776633523638423)
      ·
        refine ⟨18718340664950285457635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12478893776633523638423 18718340664950285457635)
        ·
          refine ⟨28077510997425428186453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18718340664950285457635 28077510997425428186453)
          ·
            refine ⟨20564583250067452285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 28077510997425428186453 20564583250067452285)
            ·
              rfl

theorem cell22_4866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 12].length) (baseStart_4866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4866 prefixEnd_4866 := by exact prefixLift 4866
  have htrace : WordTrace (prefixWord ++ tailWord_4866) baseStart_4866 baseEnd_4866 := by
    simpa [prefixWord, tailWord_4866, baseEnd_4866] using wordTrace_append hprefix tailTrace_4866
  have hstable : (prefixWord ++ tailWord_4866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866).length < 2 ^ (prefixWord ++ tailWord_4866).sum := by decide
  have hdescent : baseEnd_4866 < baseStart_4866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 8]
def baseStart_4879 : Nat := 118140960795 + 4879 * 2 ^ 59
def prefixEnd_4879 : Nat := 4983230072969 + 3 ^ 40 * 4879 * 2
def baseEnd_4879 : Nat := 1670181408927763060045

theorem tailTrace_4879 : CollatzResearch.WordTrace tailWord_4879 prefixEnd_4879 1670181408927763060045 := by
  unfold tailWord_4879
  simp only [CollatzResearch.WordTrace]
  refine ⟨177951749331691111969691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118634499554460741313127 177951749331691111969691)
  ·
    refine ⟨266927623997536667954537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177951749331691111969691 266927623997536667954537)
    ·
      refine ⟨200195717998152500965903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266927623997536667954537 200195717998152500965903)
      ·
        refine ⟨300293576997228751448855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200195717998152500965903 300293576997228751448855)
        ·
          refine ⟨450440365495843127173283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300293576997228751448855 450440365495843127173283)
          ·
            refine ⟨675660548243764690759925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450440365495843127173283 675660548243764690759925)
            ·
              refine ⟨63343176397852939758743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 675660548243764690759925 63343176397852939758743)
              ·
                refine ⟨95014764596779409638115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63343176397852939758743 95014764596779409638115)
                ·
                  refine ⟨142522146895169114457173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95014764596779409638115 142522146895169114457173)
                  ·
                    refine ⟨1670181408927763060045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 142522146895169114457173 1670181408927763060045)
                    ·
                      rfl

theorem cell22_4879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_4879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4879 prefixEnd_4879 := by exact prefixLift 4879
  have htrace : WordTrace (prefixWord ++ tailWord_4879) baseStart_4879 baseEnd_4879 := by
    simpa [prefixWord, tailWord_4879, baseEnd_4879] using wordTrace_append hprefix tailTrace_4879
  have hstable : (prefixWord ++ tailWord_4879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879).length < 2 ^ (prefixWord ++ tailWord_4879).sum := by decide
  have hdescent : baseEnd_4879 < baseStart_4879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_4898 : Nat := 118140960795 + 4898 * 2 ^ 59
def prefixEnd_4898 : Nat := 4983230072969 + 3 ^ 40 * 4898 * 2
def baseEnd_4898 : Nat := 1676685497218046834987

theorem tailTrace_4898 : CollatzResearch.WordTrace tailWord_4898 prefixEnd_4898 1676685497218046834987 := by
  unfold tailWord_4898
  simp only [CollatzResearch.WordTrace]
  refine ⟨44661184065714339227837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119096490841904904607565 44661184065714339227837)
  ·
    refine ⟨16747944024642877210439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44661184065714339227837 16747944024642877210439)
    ·
      refine ⟨25121916036964315815659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16747944024642877210439 25121916036964315815659)
      ·
        refine ⟨37682874055446473723489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25121916036964315815659 37682874055446473723489)
        ·
          refine ⟨28262155541584855292617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37682874055446473723489 28262155541584855292617)
          ·
            refine ⟨21196616656188641469463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28262155541584855292617 21196616656188641469463)
            ·
              refine ⟨31794924984282962204195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21196616656188641469463 31794924984282962204195)
              ·
                refine ⟨47692387476424443306293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31794924984282962204195 47692387476424443306293)
                ·
                  refine ⟨4471161325914791559965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47692387476424443306293 4471161325914791559965)
                  ·
                    refine ⟨1676685497218046834987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4471161325914791559965 1676685497218046834987)
                    ·
                      rfl

theorem cell22_4898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_4898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4898 prefixEnd_4898 := by exact prefixLift 4898
  have htrace : WordTrace (prefixWord ++ tailWord_4898) baseStart_4898 baseEnd_4898 := by
    simpa [prefixWord, tailWord_4898, baseEnd_4898] using wordTrace_append hprefix tailTrace_4898
  have hstable : (prefixWord ++ tailWord_4898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898).length < 2 ^ (prefixWord ++ tailWord_4898).sum := by decide
  have hdescent : baseEnd_4898 < baseStart_4898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4915 : List Nat := [1, 1, 1, 2, 6, 1, 1, 5, 1, 3]
def baseStart_4915 : Nat := 118140960795 + 4915 * 2 ^ 59
def prefixEnd_4915 : Nat := 4983230072969 + 3 ^ 40 * 4915 * 2
def baseEnd_4915 : Nat := 1682504944635669159935

theorem tailTrace_4915 : CollatzResearch.WordTrace tailWord_4915 prefixEnd_4915 1682504944635669159935 := by
  unfold tailWord_4915
  simp only [CollatzResearch.WordTrace]
  refine ⟨179264777201269260280199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119509851467512840186799 179264777201269260280199)
  ·
    refine ⟨268897165801903890420299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179264777201269260280199 268897165801903890420299)
    ·
      refine ⟨403345748702855835630449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268897165801903890420299 403345748702855835630449)
      ·
        refine ⟨302509311527141876722837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403345748702855835630449 302509311527141876722837)
        ·
          refine ⟨14180123977834775471383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 302509311527141876722837 14180123977834775471383)
          ·
            refine ⟨21270185966752163207075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14180123977834775471383 21270185966752163207075)
            ·
              refine ⟨31905278950128244810613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21270185966752163207075 31905278950128244810613)
              ·
                refine ⟨2991119901574522950995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31905278950128244810613 2991119901574522950995)
                ·
                  refine ⟨4486679852361784426493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991119901574522950995 4486679852361784426493)
                  ·
                    refine ⟨1682504944635669159935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4486679852361784426493 1682504944635669159935)
                    ·
                      rfl

theorem cell22_4915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 3].length) (baseStart_4915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4915 prefixEnd_4915 := by exact prefixLift 4915
  have htrace : WordTrace (prefixWord ++ tailWord_4915) baseStart_4915 baseEnd_4915 := by
    simpa [prefixWord, tailWord_4915, baseEnd_4915] using wordTrace_append hprefix tailTrace_4915
  have hstable : (prefixWord ++ tailWord_4915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4915).length < 2 ^ (prefixWord ++ tailWord_4915).sum := by decide
  have hdescent : baseEnd_4915 < baseStart_4915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4945 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 5]
def baseStart_4945 : Nat := 118140960795 + 4945 * 2 ^ 59
def prefixEnd_4945 : Nat := 4983230072969 + 3 ^ 40 * 4945 * 2
def baseEnd_4945 : Nat := 564258185908530303281

theorem tailTrace_4945 : CollatzResearch.WordTrace tailWord_4945 prefixEnd_4945 564258185908530303281 := by
  unfold tailWord_4945
  simp only [CollatzResearch.WordTrace]
  refine ⟨180358967092584383872289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120239311395056255914859 180358967092584383872289)
  ·
    refine ⟨135269225319438287904217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180358967092584383872289 135269225319438287904217)
    ·
      refine ⟨101451918989578715928163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135269225319438287904217 101451918989578715928163)
      ·
        refine ⟨152177878484368073892245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101451918989578715928163 152177878484368073892245)
        ·
          refine ⟨7133338053954753463699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152177878484368073892245 7133338053954753463699)
          ·
            refine ⟨10700007080932130195549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7133338053954753463699 10700007080932130195549)
            ·
              refine ⟨4012502655349548823331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10700007080932130195549 4012502655349548823331)
              ·
                refine ⟨6018753983024323234997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4012502655349548823331 6018753983024323234997)
                ·
                  refine ⟨564258185908530303281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6018753983024323234997 564258185908530303281)
                  ·
                    rfl

theorem cell22_4945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_4945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4945 prefixEnd_4945 := by exact prefixLift 4945
  have htrace : WordTrace (prefixWord ++ tailWord_4945) baseStart_4945 baseEnd_4945 := by
    simpa [prefixWord, tailWord_4945, baseEnd_4945] using wordTrace_append hprefix tailTrace_4945
  have hstable : (prefixWord ++ tailWord_4945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4945).length < 2 ^ (prefixWord ++ tailWord_4945).sum := by decide
  have hdescent : baseEnd_4945 < baseStart_4945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 1, 5]
def baseStart_4971 : Nat := 118140960795 + 4971 * 2 ^ 59
def prefixEnd_4971 : Nat := 4983230072969 + 3 ^ 40 * 4971 * 2
def baseEnd_4971 : Nat := 1701674889070189759763

theorem tailTrace_4971 : CollatzResearch.WordTrace tailWord_4971 prefixEnd_4971 1701674889070189759763 := by
  unfold tailWord_4971
  simp only [CollatzResearch.WordTrace]
  refine ⟨181307264998390824318767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120871509998927216212511 181307264998390824318767)
  ·
    refine ⟨271960897497586236478151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181307264998390824318767 271960897497586236478151)
    ·
      refine ⟨407941346246379354717227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271960897497586236478151 407941346246379354717227)
      ·
        refine ⟨611912019369569032075841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407941346246379354717227 611912019369569032075841)
        ·
          refine ⟨458934014527176774056881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611912019369569032075841 458934014527176774056881)
          ·
            refine ⟨344200510895382580542661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458934014527176774056881 344200510895382580542661)
            ·
              refine ⟨64537595792884233851749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344200510895382580542661 64537595792884233851749)
              ·
                refine ⟨12100799211165793847203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64537595792884233851749 12100799211165793847203)
                ·
                  refine ⟨18151198816748690770805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12100799211165793847203 18151198816748690770805)
                  ·
                    refine ⟨1701674889070189759763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18151198816748690770805 1701674889070189759763)
                    ·
                      rfl

theorem cell22_4971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_4971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4971 prefixEnd_4971 := by exact prefixLift 4971
  have htrace : WordTrace (prefixWord ++ tailWord_4971) baseStart_4971 baseEnd_4971 := by
    simpa [prefixWord, tailWord_4971, baseEnd_4971] using wordTrace_append hprefix tailTrace_4971
  have hstable : (prefixWord ++ tailWord_4971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971).length < 2 ^ (prefixWord ++ tailWord_4971).sum := by decide
  have hdescent : baseEnd_4971 < baseStart_4971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001 : List Nat := [1, 2, 1, 1, 5, 2, 1, 9]
def baseStart_5001 : Nat := 118140960795 + 5001 * 2 ^ 59
def prefixEnd_5001 : Nat := 4983230072969 + 3 ^ 40 * 5001 * 2
def baseEnd_5001 : Nat := 190216055795567945519

theorem tailTrace_5001 : CollatzResearch.WordTrace tailWord_5001 prefixEnd_5001 190216055795567945519 := by
  unfold tailWord_5001
  simp only [CollatzResearch.WordTrace]
  refine ⟨182401454889705947910857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121600969926470631940571 182401454889705947910857)
  ·
    refine ⟨136801091167279460933143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182401454889705947910857 136801091167279460933143)
    ·
      refine ⟨205201636750919191399715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136801091167279460933143 205201636750919191399715)
      ·
        refine ⟨307802455126378787099573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205201636750919191399715 307802455126378787099573)
        ·
          refine ⟨28856480168098011290585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307802455126378787099573 28856480168098011290585)
          ·
            refine ⟨21642360126073508467939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28856480168098011290585 21642360126073508467939)
            ·
              refine ⟨32463540189110262701909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21642360126073508467939 32463540189110262701909)
              ·
                refine ⟨190216055795567945519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 32463540189110262701909 190216055795567945519)
                ·
                  rfl

theorem cell22_5001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 9].length) (baseStart_5001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5001 prefixEnd_5001 := by exact prefixLift 5001
  have htrace : WordTrace (prefixWord ++ tailWord_5001) baseStart_5001 baseEnd_5001 := by
    simpa [prefixWord, tailWord_5001, baseEnd_5001] using wordTrace_append hprefix tailTrace_5001
  have hstable : (prefixWord ++ tailWord_5001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001).length < 2 ^ (prefixWord ++ tailWord_5001).sum := by decide
  have hdescent : baseEnd_5001 < baseStart_5001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 5]
def baseStart_5063 : Nat := 118140960795 + 5063 * 2 ^ 59
def prefixEnd_5063 : Nat := 4983230072969 + 3 ^ 40 * 5063 * 2
def baseEnd_5063 : Nat := 577722789737538819827

theorem tailTrace_5063 : CollatzResearch.WordTrace tailWord_5063 prefixEnd_5063 577722789737538819827 := by
  unfold tailWord_5063
  simp only [CollatzResearch.WordTrace]
  refine ⟨184662780665090536667843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123108520443393691111895 184662780665090536667843)
  ·
    refine ⟨276994170997635805001765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184662780665090536667843 276994170997635805001765)
    ·
      refine ⟨51936407062056713437831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276994170997635805001765 51936407062056713437831)
      ·
        refine ⟨77904610593085070156747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51936407062056713437831 77904610593085070156747)
        ·
          refine ⟨116856915889627605235121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77904610593085070156747 116856915889627605235121)
          ·
            refine ⟨87642686917220703926341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116856915889627605235121 87642686917220703926341)
            ·
              refine ⟨16433003796978881986189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87642686917220703926341 16433003796978881986189)
              ·
                refine ⟨6162376423867080744821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16433003796978881986189 6162376423867080744821)
                ·
                  refine ⟨577722789737538819827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6162376423867080744821 577722789737538819827)
                  ·
                    rfl

theorem cell22_5063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 5].length) (baseStart_5063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5063 prefixEnd_5063 := by exact prefixLift 5063
  have htrace : WordTrace (prefixWord ++ tailWord_5063) baseStart_5063 baseEnd_5063 := by
    simpa [prefixWord, tailWord_5063, baseEnd_5063] using wordTrace_append hprefix tailTrace_5063
  have hstable : (prefixWord ++ tailWord_5063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063).length < 2 ^ (prefixWord ++ tailWord_5063).sum := by decide
  have hdescent : baseEnd_5063 < baseStart_5063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5153 : List Nat := [1, 2, 3, 2, 3, 1, 10]
def baseStart_5153 : Nat := 118140960795 + 5153 * 2 ^ 59
def prefixEnd_5153 : Nat := 4983230072969 + 3 ^ 40 * 5153 * 2
def baseEnd_5153 : Nat := 65332489203051174415

theorem tailTrace_5153 : CollatzResearch.WordTrace tailWord_5153 prefixEnd_5153 65332489203051174415 := by
  unfold tailWord_5153
  simp only [CollatzResearch.WordTrace]
  refine ⟨187945350339035907444113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125296900226023938296075 187945350339035907444113)
  ·
    refine ⟨140959012754276930583085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187945350339035907444113 140959012754276930583085)
    ·
      refine ⟨52859629782853848968657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140959012754276930583085 52859629782853848968657)
      ·
        refine ⟨39644722337140386726493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52859629782853848968657 39644722337140386726493)
        ·
          refine ⟨14866770876427645022435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39644722337140386726493 14866770876427645022435)
          ·
            refine ⟨22300156314641467533653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14866770876427645022435 22300156314641467533653)
            ·
              refine ⟨65332489203051174415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 22300156314641467533653 65332489203051174415)
              ·
                rfl

theorem cell22_5153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 10].length) (baseStart_5153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5153 prefixEnd_5153 := by exact prefixLift 5153
  have htrace : WordTrace (prefixWord ++ tailWord_5153) baseStart_5153 baseEnd_5153 := by
    simpa [prefixWord, tailWord_5153, baseEnd_5153] using wordTrace_append hprefix tailTrace_5153
  have hstable : (prefixWord ++ tailWord_5153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5153).length < 2 ^ (prefixWord ++ tailWord_5153).sum := by decide
  have hdescent : baseEnd_5153 < baseStart_5153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5155 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 2, 4]
def baseStart_5155 : Nat := 118140960795 + 5155 * 2 ^ 59
def prefixEnd_5155 : Nat := 4983230072969 + 3 ^ 40 * 5155 * 2
def baseEnd_5155 : Nat := 1764661849355043159199

theorem tailTrace_5155 : CollatzResearch.WordTrace tailWord_5155 prefixEnd_5155 1764661849355043159199 := by
  unfold tailWord_5155
  simp only [CollatzResearch.WordTrace]
  refine ⟨188018296331790249016919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125345530887860166011279 188018296331790249016919)
  ·
    refine ⟨282027444497685373525379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188018296331790249016919 282027444497685373525379)
    ·
      refine ⟨423041166746528060288069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282027444497685373525379 423041166746528060288069)
      ·
        refine ⟨79320218764974011304013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423041166746528060288069 79320218764974011304013)
        ·
          refine ⟨29745082036865254239005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79320218764974011304013 29745082036865254239005)
          ·
            refine ⟨11154405763824470339627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29745082036865254239005 11154405763824470339627)
            ·
              refine ⟨16731608645736705509441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11154405763824470339627 16731608645736705509441)
              ·
                refine ⟨12548706484302529132081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16731608645736705509441 12548706484302529132081)
                ·
                  refine ⟨9411529863226896849061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12548706484302529132081 9411529863226896849061)
                  ·
                    refine ⟨1764661849355043159199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9411529863226896849061 1764661849355043159199)
                    ·
                      rfl

theorem cell22_5155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_5155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5155 prefixEnd_5155 := by exact prefixLift 5155
  have htrace : WordTrace (prefixWord ++ tailWord_5155) baseStart_5155 baseEnd_5155 := by
    simpa [prefixWord, tailWord_5155, baseEnd_5155] using wordTrace_append hprefix tailTrace_5155
  have hstable : (prefixWord ++ tailWord_5155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5155).length < 2 ^ (prefixWord ++ tailWord_5155).sum := by decide
  have hdescent : baseEnd_5155 < baseStart_5155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_5174 : Nat := 118140960795 + 5174 * 2 ^ 59
def prefixEnd_5174 : Nat := 4983230072969 + 3 ^ 40 * 5174 * 2
def baseEnd_5174 : Nat := 1771165937645326934141

theorem tailTrace_5174 : CollatzResearch.WordTrace tailWord_5174 prefixEnd_5174 1771165937645326934141 := by
  unfold tailWord_5174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11794455203934780872411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125807522175304329305717 11794455203934780872411)
  ·
    refine ⟨17691682805902171308617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11794455203934780872411 17691682805902171308617)
    ·
      refine ⟨13268762104426628481463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17691682805902171308617 13268762104426628481463)
      ·
        refine ⟨19903143156639942722195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13268762104426628481463 19903143156639942722195)
        ·
          refine ⟨29854714734959914083293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19903143156639942722195 29854714734959914083293)
          ·
            refine ⟨11195518025609967781235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29854714734959914083293 11195518025609967781235)
            ·
              refine ⟨16793277038414951671853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11195518025609967781235 16793277038414951671853)
              ·
                refine ⟨6297478889405606876945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16793277038414951671853 6297478889405606876945)
                ·
                  refine ⟨4723109167054205157709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6297478889405606876945 4723109167054205157709)
                  ·
                    refine ⟨1771165937645326934141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4723109167054205157709 1771165937645326934141)
                    ·
                      rfl

theorem cell22_5174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_5174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5174 prefixEnd_5174 := by exact prefixLift 5174
  have htrace : WordTrace (prefixWord ++ tailWord_5174) baseStart_5174 baseEnd_5174 := by
    simpa [prefixWord, tailWord_5174, baseEnd_5174] using wordTrace_append hprefix tailTrace_5174
  have hstable : (prefixWord ++ tailWord_5174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174).length < 2 ^ (prefixWord ++ tailWord_5174).sum := by decide
  have hdescent : baseEnd_5174 < baseStart_5174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5215 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 5]
def baseStart_5215 : Nat := 118140960795 + 5215 * 2 ^ 59
def prefixEnd_5215 : Nat := 4983230072969 + 3 ^ 40 * 5215 * 2
def baseEnd_5215 : Nat := 595067025178295553005

theorem tailTrace_5215 : CollatzResearch.WordTrace tailWord_5215 prefixEnd_5215 595067025178295553005 := by
  unfold tailWord_5215
  simp only [CollatzResearch.WordTrace]
  refine ⟨190206676114420496201099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126804450742946997467399 190206676114420496201099)
  ·
    refine ⟨285310014171630744301649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190206676114420496201099 285310014171630744301649)
    ·
      refine ⟨213982510628723058226237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285310014171630744301649 213982510628723058226237)
      ·
        refine ⟨80243441485771146834839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213982510628723058226237 80243441485771146834839)
        ·
          refine ⟨120365162228656720252259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80243441485771146834839 120365162228656720252259)
          ·
            refine ⟨180547743342985080378389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120365162228656720252259 180547743342985080378389)
            ·
              refine ⟨8463175469202425642737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 180547743342985080378389 8463175469202425642737)
              ·
                refine ⟨6347381601901819232053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8463175469202425642737 6347381601901819232053)
                ·
                  refine ⟨595067025178295553005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6347381601901819232053 595067025178295553005)
                  ·
                    rfl

theorem cell22_5215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 5].length) (baseStart_5215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5215 prefixEnd_5215 := by exact prefixLift 5215
  have htrace : WordTrace (prefixWord ++ tailWord_5215) baseStart_5215 baseEnd_5215 := by
    simpa [prefixWord, tailWord_5215, baseEnd_5215] using wordTrace_append hprefix tailTrace_5215
  have hstable : (prefixWord ++ tailWord_5215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5215).length < 2 ^ (prefixWord ++ tailWord_5215).sum := by decide
  have hdescent : baseEnd_5215 < baseStart_5215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_5230 : Nat := 118140960795 + 5230 * 2 ^ 59
def prefixEnd_5230 : Nat := 4983230072969 + 3 ^ 40 * 5230 * 2
def baseEnd_5230 : Nat := 1790335882079847533969

theorem tailTrace_5230 : CollatzResearch.WordTrace tailWord_5230 prefixEnd_5230 1790335882079847533969 := by
  unfold tailWord_5230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23844221382509757249643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127169180706718705331429 23844221382509757249643)
  ·
    refine ⟨35766332073764635874465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23844221382509757249643 35766332073764635874465)
    ·
      refine ⟨26824749055323476905849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35766332073764635874465 26824749055323476905849)
      ·
        refine ⟨20118561791492607679387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26824749055323476905849 20118561791492607679387)
        ·
          refine ⟨30177842687238911519081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20118561791492607679387 30177842687238911519081)
          ·
            refine ⟨22633382015429183639311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30177842687238911519081 22633382015429183639311)
            ·
              refine ⟨33950073023143775458967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22633382015429183639311 33950073023143775458967)
              ·
                refine ⟨50925109534715663188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33950073023143775458967 50925109534715663188451)
                ·
                  refine ⟨76387664302073494782677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50925109534715663188451 76387664302073494782677)
                  ·
                    refine ⟨1790335882079847533969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 76387664302073494782677 1790335882079847533969)
                    ·
                      rfl

theorem cell22_5230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_5230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5230 prefixEnd_5230 := by exact prefixLift 5230
  have htrace : WordTrace (prefixWord ++ tailWord_5230) baseStart_5230 baseEnd_5230 := by
    simpa [prefixWord, tailWord_5230, baseEnd_5230] using wordTrace_append hprefix tailTrace_5230
  have hstable : (prefixWord ++ tailWord_5230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230).length < 2 ^ (prefixWord ++ tailWord_5230).sum := by decide
  have hdescent : baseEnd_5230 < baseStart_5230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_5245 : Nat := 118140960795 + 5245 * 2 ^ 59
def prefixEnd_5245 : Nat := 4983230072969 + 3 ^ 40 * 5245 * 2
def baseEnd_5245 : Nat := 1795470688624808408923

theorem tailTrace_5245 : CollatzResearch.WordTrace tailWord_5245 prefixEnd_5245 1795470688624808408923 := by
  unfold tailWord_5245
  simp only [CollatzResearch.WordTrace]
  refine ⟨191300866005735619793189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127533910670490413195459 191300866005735619793189)
  ·
    refine ⟨35868912376075428711223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191300866005735619793189 35868912376075428711223)
    ·
      refine ⟨53803368564113143066835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35868912376075428711223 53803368564113143066835)
      ·
        refine ⟨80705052846169714600253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53803368564113143066835 80705052846169714600253)
        ·
          refine ⟨30264394817313642975095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80705052846169714600253 30264394817313642975095)
          ·
            refine ⟨45396592225970464462643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30264394817313642975095 45396592225970464462643)
            ·
              refine ⟨68094888338955696693965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45396592225970464462643 68094888338955696693965)
              ·
                refine ⟨25535583127108386260237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68094888338955696693965 25535583127108386260237)
                ·
                  refine ⟨9575843672665644847589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25535583127108386260237 9575843672665644847589)
                  ·
                    refine ⟨1795470688624808408923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9575843672665644847589 1795470688624808408923)
                    ·
                      rfl

theorem cell22_5245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_5245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5245 prefixEnd_5245 := by exact prefixLift 5245
  have htrace : WordTrace (prefixWord ++ tailWord_5245) baseStart_5245 baseEnd_5245 := by
    simpa [prefixWord, tailWord_5245, baseEnd_5245] using wordTrace_append hprefix tailTrace_5245
  have hstable : (prefixWord ++ tailWord_5245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245).length < 2 ^ (prefixWord ++ tailWord_5245).sum := by decide
  have hdescent : baseEnd_5245 < baseStart_5245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5277 : List Nat := [1, 4, 2, 1, 1, 2, 1, 6, 4]
def baseStart_5277 : Nat := 118140960795 + 5277 * 2 ^ 59
def prefixEnd_5277 : Nat := 4983230072969 + 3 ^ 40 * 5277 * 2
def baseEnd_5277 : Nat := 602141647529130536275

theorem tailTrace_5277 : CollatzResearch.WordTrace tailWord_5277 prefixEnd_5277 602141647529130536275 := by
  unfold tailWord_5277
  simp only [CollatzResearch.WordTrace]
  refine ⟨192468001889805084958085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128312001259870056638723 192468001889805084958085)
  ·
    refine ⟨36087750354338453429641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192468001889805084958085 36087750354338453429641)
    ·
      refine ⟨27065812765753840072231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36087750354338453429641 27065812765753840072231)
      ·
        refine ⟨40598719148630760108347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27065812765753840072231 40598719148630760108347)
        ·
          refine ⟨60898078722946140162521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40598719148630760108347 60898078722946140162521)
          ·
            refine ⟨45673559042209605121891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60898078722946140162521 45673559042209605121891)
            ·
              refine ⟨68510338563314407682837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45673559042209605121891 68510338563314407682837)
              ·
                refine ⟨3211422120155362860133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68510338563314407682837 3211422120155362860133)
                ·
                  refine ⟨602141647529130536275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3211422120155362860133 602141647529130536275)
                  ·
                    rfl

theorem cell22_5277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_5277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5277 prefixEnd_5277 := by exact prefixLift 5277
  have htrace : WordTrace (prefixWord ++ tailWord_5277) baseStart_5277 baseEnd_5277 := by
    simpa [prefixWord, tailWord_5277, baseEnd_5277] using wordTrace_append hprefix tailTrace_5277
  have hstable : (prefixWord ++ tailWord_5277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5277).length < 2 ^ (prefixWord ++ tailWord_5277).sum := by decide
  have hdescent : baseEnd_5277 < baseStart_5277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305 : List Nat := [1, 2, 1, 4, 1, 4, 1, 8]
def baseStart_5305 : Nat := 118140960795 + 5305 * 2 ^ 59
def prefixEnd_5305 : Nat := 4983230072969 + 3 ^ 40 * 5305 * 2
def baseEnd_5305 : Nat := 201778879422739100971

theorem tailTrace_5305 : CollatzResearch.WordTrace tailWord_5305 prefixEnd_5305 201778879422739100971 := by
  unfold tailWord_5305
  simp only [CollatzResearch.WordTrace]
  refine ⟨193489245788365866977369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128992830525577244651579 193489245788365866977369)
  ·
    refine ⟨145116934341274400233027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193489245788365866977369 145116934341274400233027)
    ·
      refine ⟨217675401511911600349541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145116934341274400233027 217675401511911600349541)
      ·
        refine ⟨40814137783483425065539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217675401511911600349541 40814137783483425065539)
        ·
          refine ⟨61221206675225137598309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40814137783483425065539 61221206675225137598309)
          ·
            refine ⟨11478976251604713299683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61221206675225137598309 11478976251604713299683)
            ·
              refine ⟨17218464377407069949525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11478976251604713299683 17218464377407069949525)
              ·
                refine ⟨201778879422739100971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 17218464377407069949525 201778879422739100971)
                ·
                  rfl

theorem cell22_5305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 8].length) (baseStart_5305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5305 prefixEnd_5305 := by exact prefixLift 5305
  have htrace : WordTrace (prefixWord ++ tailWord_5305) baseStart_5305 baseEnd_5305 := by
    simpa [prefixWord, tailWord_5305, baseEnd_5305] using wordTrace_append hprefix tailTrace_5305
  have hstable : (prefixWord ++ tailWord_5305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305).length < 2 ^ (prefixWord ++ tailWord_5305).sum := by decide
  have hdescent : baseEnd_5305 < baseStart_5305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 5]
def baseStart_5384 : Nat := 118140960795 + 5384 * 2 ^ 59
def prefixEnd_5384 : Nat := 4983230072969 + 3 ^ 40 * 5384 * 2
def baseEnd_5384 : Nat := 614351076424926394499

theorem tailTrace_5384 : CollatzResearch.WordTrace tailWord_5384 prefixEnd_5384 614351076424926394499 := by
  unfold tailWord_5384
  simp only [CollatzResearch.WordTrace]
  refine ⟨98185306251081179551603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130913741668108239402137 98185306251081179551603)
  ·
    refine ⟨147277959376621769327405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98185306251081179551603 147277959376621769327405)
    ·
      refine ⟨55229234766233163497777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147277959376621769327405 55229234766233163497777)
      ·
        refine ⟨41421926074674872623333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55229234766233163497777 41421926074674872623333)
        ·
          refine ⟨7766611139001538616875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41421926074674872623333 7766611139001538616875)
          ·
            refine ⟨11649916708502307925313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766611139001538616875 11649916708502307925313)
            ·
              refine ⟨8737437531376730943985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11649916708502307925313 8737437531376730943985)
              ·
                refine ⟨6553078148532548207989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8737437531376730943985 6553078148532548207989)
                ·
                  refine ⟨614351076424926394499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6553078148532548207989 614351076424926394499)
                  ·
                    rfl

theorem cell22_5384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_5384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5384 prefixEnd_5384 := by exact prefixLift 5384
  have htrace : WordTrace (prefixWord ++ tailWord_5384) baseStart_5384 baseEnd_5384 := by
    simpa [prefixWord, tailWord_5384, baseEnd_5384] using wordTrace_append hprefix tailTrace_5384
  have hstable : (prefixWord ++ tailWord_5384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384).length < 2 ^ (prefixWord ++ tailWord_5384).sum := by decide
  have hdescent : baseEnd_5384 < baseStart_5384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388 : List Nat := [2, 2, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_5388 : Nat := 118140960795 + 5388 * 2 ^ 59
def prefixEnd_5388 : Nat := 4983230072969 + 3 ^ 40 * 5388 * 2
def baseEnd_5388 : Nat := 1844422511020102083485

theorem tailTrace_5388 : CollatzResearch.WordTrace tailWord_5388 prefixEnd_5388 1844422511020102083485 := by
  unfold tailWord_5388
  simp only [CollatzResearch.WordTrace]
  refine ⟨98258252243835521124409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131011002991780694832545 98258252243835521124409)
  ·
    refine ⟨73693689182876640843307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98258252243835521124409 73693689182876640843307)
    ·
      refine ⟨110540533774314961264961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73693689182876640843307 110540533774314961264961)
      ·
        refine ⟨82905400330736220948721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110540533774314961264961 82905400330736220948721)
        ·
          refine ⟨62179050248052165711541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82905400330736220948721 62179050248052165711541)
          ·
            refine ⟨5829285960754890535457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62179050248052165711541 5829285960754890535457)
            ·
              refine ⟨4371964470566167901593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5829285960754890535457 4371964470566167901593)
              ·
                refine ⟨3278973352924625926195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371964470566167901593 3278973352924625926195)
                ·
                  refine ⟨4918460029386938889293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278973352924625926195 4918460029386938889293)
                  ·
                    refine ⟨1844422511020102083485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4918460029386938889293 1844422511020102083485)
                    ·
                      rfl

theorem cell22_5388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_5388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5388 prefixEnd_5388 := by exact prefixLift 5388
  have htrace : WordTrace (prefixWord ++ tailWord_5388) baseStart_5388 baseEnd_5388 := by
    simpa [prefixWord, tailWord_5388, baseEnd_5388] using wordTrace_append hprefix tailTrace_5388
  have hstable : (prefixWord ++ tailWord_5388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388).length < 2 ^ (prefixWord ++ tailWord_5388).sum := by decide
  have hdescent : baseEnd_5388 < baseStart_5388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5412 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 6]
def baseStart_5412 : Nat := 118140960795 + 5412 * 2 ^ 59
def prefixEnd_5412 : Nat := 4983230072969 + 3 ^ 40 * 5412 * 2
def baseEnd_5412 : Nat := 617546067164013161137

theorem tailTrace_5412 : CollatzResearch.WordTrace tailWord_5412 prefixEnd_5412 617546067164013161137 := by
  unfold tailWord_5412
  simp only [CollatzResearch.WordTrace]
  refine ⟨98695928200361570561245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131594570933815427414993 98695928200361570561245)
  ·
    refine ⟨37010973075135588960467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98695928200361570561245 37010973075135588960467)
    ·
      refine ⟨55516459612703383440701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37010973075135588960467 55516459612703383440701)
      ·
        refine ⟨20818672354763768790263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55516459612703383440701 20818672354763768790263)
        ·
          refine ⟨31228008532145653185395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20818672354763768790263 31228008532145653185395)
          ·
            refine ⟨46842012798218479778093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31228008532145653185395 46842012798218479778093)
            ·
              refine ⟨17565754799331929916785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46842012798218479778093 17565754799331929916785)
              ·
                refine ⟨13174316099498947437589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17565754799331929916785 13174316099498947437589)
                ·
                  refine ⟨617546067164013161137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13174316099498947437589 617546067164013161137)
                  ·
                    rfl

theorem cell22_5412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_5412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5412 prefixEnd_5412 := by exact prefixLift 5412
  have htrace : WordTrace (prefixWord ++ tailWord_5412) baseStart_5412 baseEnd_5412 := by
    simpa [prefixWord, tailWord_5412, baseEnd_5412] using wordTrace_append hprefix tailTrace_5412
  have hstable : (prefixWord ++ tailWord_5412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5412).length < 2 ^ (prefixWord ++ tailWord_5412).sum := by decide
  have hdescent : baseEnd_5412 < baseStart_5412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 1, 5]
def baseStart_5427 : Nat := 118140960795 + 5427 * 2 ^ 59
def prefixEnd_5427 : Nat := 4983230072969 + 3 ^ 40 * 5427 * 2
def baseEnd_5427 : Nat := 1857773008037000358365

theorem tailTrace_5427 : CollatzResearch.WordTrace tailWord_5427 prefixEnd_5427 1857773008037000358365 := by
  unfold tailWord_5427
  simp only [CollatzResearch.WordTrace]
  refine ⟨197938951346380702918535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131959300897587135279023 197938951346380702918535)
  ·
    refine ⟨296908427019571054377803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197938951346380702918535 296908427019571054377803)
    ·
      refine ⟨445362640529356581566705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296908427019571054377803 445362640529356581566705)
      ·
        refine ⟨334021980397017436175029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445362640529356581566705 334021980397017436175029)
        ·
          refine ⟨31314560662220384641409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334021980397017436175029 31314560662220384641409)
          ·
            refine ⟨23485920496665288481057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31314560662220384641409 23485920496665288481057)
            ·
              refine ⟨17614440372498966360793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23485920496665288481057 17614440372498966360793)
              ·
                refine ⟨13210830279374224770595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17614440372498966360793 13210830279374224770595)
                ·
                  refine ⟨19816245419061337155893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13210830279374224770595 19816245419061337155893)
                  ·
                    refine ⟨1857773008037000358365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19816245419061337155893 1857773008037000358365)
                    ·
                      rfl

theorem cell22_5427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_5427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5427 prefixEnd_5427 := by exact prefixLift 5427
  have htrace : WordTrace (prefixWord ++ tailWord_5427) baseStart_5427 baseEnd_5427 := by
    simpa [prefixWord, tailWord_5427, baseEnd_5427] using wordTrace_append hprefix tailTrace_5427
  have hstable : (prefixWord ++ tailWord_5427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427).length < 2 ^ (prefixWord ++ tailWord_5427).sum := by decide
  have hdescent : baseEnd_5427 < baseStart_5427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429 : List Nat := [1, 3, 3, 1, 2, 2, 1, 5, 4]
def baseStart_5429 : Nat := 118140960795 + 5429 * 2 ^ 59
def prefixEnd_5429 : Nat := 4983230072969 + 3 ^ 40 * 5429 * 2
def baseEnd_5429 : Nat := 619485882969887269453

theorem tailTrace_5429 : CollatzResearch.WordTrace tailWord_5429 prefixEnd_5429 619485882969887269453 := by
  unfold tailWord_5429
  simp only [CollatzResearch.WordTrace]
  refine ⟨198011897339135044491341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132007931559423362994227 198011897339135044491341)
  ·
    refine ⟨74254461502175641684253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198011897339135044491341 74254461502175641684253)
    ·
      refine ⟨27845423063315865631595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74254461502175641684253 27845423063315865631595)
      ·
        refine ⟨41768134594973798447393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27845423063315865631595 41768134594973798447393)
        ·
          refine ⟨31326100946230348835545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41768134594973798447393 31326100946230348835545)
          ·
            refine ⟨23494575709672761626659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31326100946230348835545 23494575709672761626659)
            ·
              refine ⟨35241863564509142439989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23494575709672761626659 35241863564509142439989)
              ·
                refine ⟨3303924709172732103749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35241863564509142439989 3303924709172732103749)
                ·
                  refine ⟨619485882969887269453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3303924709172732103749 619485882969887269453)
                  ·
                    rfl

theorem cell22_5429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_5429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5429 prefixEnd_5429 := by exact prefixLift 5429
  have htrace : WordTrace (prefixWord ++ tailWord_5429) baseStart_5429 baseEnd_5429 := by
    simpa [prefixWord, tailWord_5429, baseEnd_5429] using wordTrace_append hprefix tailTrace_5429
  have hstable : (prefixWord ++ tailWord_5429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429).length < 2 ^ (prefixWord ++ tailWord_5429).sum := by decide
  have hdescent : baseEnd_5429 < baseStart_5429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5440 : List Nat := [2, 1, 1, 2, 2, 1, 13]
def baseStart_5440 : Nat := 118140960795 + 5440 * 2 ^ 59
def prefixEnd_5440 : Nat := 4983230072969 + 3 ^ 40 * 5440 * 2
def baseEnd_5440 : Nat := 68971228655899991975

theorem tailTrace_5440 : CollatzResearch.WordTrace tailWord_5440 prefixEnd_5440 68971228655899991975 := by
  unfold tailWord_5440
  simp only [CollatzResearch.WordTrace]
  refine ⟨99206550149641961570887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132275400199522615427849 99206550149641961570887)
  ·
    refine ⟨148809825224462942356331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99206550149641961570887 148809825224462942356331)
    ·
      refine ⟨223214737836694413534497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148809825224462942356331 223214737836694413534497)
      ·
        refine ⟨167411053377520810150873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223214737836694413534497 167411053377520810150873)
        ·
          refine ⟨125558290033140607613155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167411053377520810150873 125558290033140607613155)
          ·
            refine ⟨188337435049710911419733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125558290033140607613155 188337435049710911419733)
            ·
              refine ⟨68971228655899991975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 188337435049710911419733 68971228655899991975)
              ·
                rfl

theorem cell22_5440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 13].length) (baseStart_5440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5440 prefixEnd_5440 := by exact prefixLift 5440
  have htrace : WordTrace (prefixWord ++ tailWord_5440) baseStart_5440 baseEnd_5440 := by
    simpa [prefixWord, tailWord_5440, baseEnd_5440] using wordTrace_append hprefix tailTrace_5440
  have hstable : (prefixWord ++ tailWord_5440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5440).length < 2 ^ (prefixWord ++ tailWord_5440).sum := by decide
  have hdescent : baseEnd_5440 < baseStart_5440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_5577 : Nat := 118140960795 + 5577 * 2 ^ 59
def prefixEnd_5577 : Nat := 4983230072969 + 3 ^ 40 * 5577 * 2
def baseEnd_5577 : Nat := 1909121073486609107905

theorem tailTrace_5577 : CollatzResearch.WordTrace tailWord_5577 prefixEnd_5577 1909121073486609107905 := by
  unfold tailWord_5577
  simp only [CollatzResearch.WordTrace]
  refine ⟨203409900802956320878985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135606600535304213919323 203409900802956320878985)
  ·
    refine ⟨152557425602217240659239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203409900802956320878985 152557425602217240659239)
    ·
      refine ⟨228836138403325860988859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152557425602217240659239 228836138403325860988859)
      ·
        refine ⟨343254207604988791483289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228836138403325860988859 343254207604988791483289)
        ·
          refine ⟨257440655703741593612467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343254207604988791483289 257440655703741593612467)
          ·
            refine ⟨386160983555612390418701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257440655703741593612467 386160983555612390418701)
            ·
              refine ⟨144810368833354646407013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386160983555612390418701 144810368833354646407013)
              ·
                refine ⟨27151944156253996201315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144810368833354646407013 27151944156253996201315)
                ·
                  refine ⟨40727916234380994301973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27151944156253996201315 40727916234380994301973)
                  ·
                    refine ⟨1909121073486609107905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40727916234380994301973 1909121073486609107905)
                    ·
                      rfl

theorem cell22_5577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_5577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5577 prefixEnd_5577 := by exact prefixLift 5577
  have htrace : WordTrace (prefixWord ++ tailWord_5577) baseStart_5577 baseEnd_5577 := by
    simpa [prefixWord, tailWord_5577, baseEnd_5577] using wordTrace_append hprefix tailTrace_5577
  have hstable : (prefixWord ++ tailWord_5577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577).length < 2 ^ (prefixWord ++ tailWord_5577).sum := by decide
  have hdescent : baseEnd_5577 < baseStart_5577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592 : List Nat := [2, 1, 2, 2, 2, 1, 2, 10]
def baseStart_5592 : Nat := 118140960795 + 5592 * 2 ^ 59
def prefixEnd_5592 : Nat := 4983230072969 + 3 ^ 40 * 5592 * 2
def baseEnd_5592 : Nat := 212695097781285553651

theorem tailTrace_5592 : CollatzResearch.WordTrace tailWord_5592 prefixEnd_5592 212695097781285553651 := by
  unfold tailWord_5592
  simp only [CollatzResearch.WordTrace]
  refine ⟨101978497874306941337515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135971330499075921783353 101978497874306941337515)
  ·
    refine ⟨152967746811460412006273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101978497874306941337515 152967746811460412006273)
    ·
      refine ⟨114725810108595309004705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152967746811460412006273 114725810108595309004705)
      ·
        refine ⟨86044357581446481753529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114725810108595309004705 86044357581446481753529)
        ·
          refine ⟨64533268186084861315147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86044357581446481753529 64533268186084861315147)
          ·
            refine ⟨96799902279127291972721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64533268186084861315147 96799902279127291972721)
            ·
              refine ⟨72599926709345468979541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96799902279127291972721 72599926709345468979541)
              ·
                refine ⟨212695097781285553651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 72599926709345468979541 212695097781285553651)
                ·
                  rfl

theorem cell22_5592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_5592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5592 prefixEnd_5592 := by exact prefixLift 5592
  have htrace : WordTrace (prefixWord ++ tailWord_5592) baseStart_5592 baseEnd_5592 := by
    simpa [prefixWord, tailWord_5592, baseEnd_5592] using wordTrace_append hprefix tailTrace_5592
  have hstable : (prefixWord ++ tailWord_5592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592).length < 2 ^ (prefixWord ++ tailWord_5592).sum := by decide
  have hdescent : baseEnd_5592 < baseStart_5592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_5594 : Nat := 118140960795 + 5594 * 2 ^ 59
def prefixEnd_5594 : Nat := 4983230072969 + 3 ^ 40 * 5594 * 2
def baseEnd_5594 : Nat := 1914940520904231432853

theorem tailTrace_5594 : CollatzResearch.WordTrace tailWord_5594 prefixEnd_5594 1914940520904231432853 := by
  unfold tailWord_5594
  simp only [CollatzResearch.WordTrace]
  refine ⟨51007485435342056061959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136019961160912149498557 51007485435342056061959)
  ·
    refine ⟨76511228153013084092939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51007485435342056061959 76511228153013084092939)
    ·
      refine ⟨114766842229519626139409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76511228153013084092939 114766842229519626139409)
      ·
        refine ⟨86075131672139719604557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114766842229519626139409 86075131672139719604557)
        ·
          refine ⟨32278174377052394851709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86075131672139719604557 32278174377052394851709)
          ·
            refine ⟨12104315391394648069391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32278174377052394851709 12104315391394648069391)
            ·
              refine ⟨18156473087091972104087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12104315391394648069391 18156473087091972104087)
              ·
                refine ⟨27234709630637958156131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18156473087091972104087 27234709630637958156131)
                ·
                  refine ⟨40852064445956937234197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27234709630637958156131 40852064445956937234197)
                  ·
                    refine ⟨1914940520904231432853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40852064445956937234197 1914940520904231432853)
                    ·
                      rfl

theorem cell22_5594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_5594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5594 prefixEnd_5594 := by exact prefixLift 5594
  have htrace : WordTrace (prefixWord ++ tailWord_5594) baseStart_5594 baseEnd_5594 := by
    simpa [prefixWord, tailWord_5594, baseEnd_5594] using wordTrace_append hprefix tailTrace_5594
  have hstable : (prefixWord ++ tailWord_5594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594).length < 2 ^ (prefixWord ++ tailWord_5594).sum := by decide
  have hdescent : baseEnd_5594 < baseStart_5594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_5613 : Nat := 118140960795 + 5613 * 2 ^ 59
def prefixEnd_5613 : Nat := 4983230072969 + 3 ^ 40 * 5613 * 2
def baseEnd_5613 : Nat := 1921444609194515207795

theorem tailTrace_5613 : CollatzResearch.WordTrace tailWord_5613 prefixEnd_5613 1921444609194515207795 := by
  unfold tailWord_5613
  simp only [CollatzResearch.WordTrace]
  refine ⟨204722928672534469189493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136481952448356312792995 204722928672534469189493)
  ·
    refine ⟨19192774563050106486515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204722928672534469189493 19192774563050106486515)
    ·
      refine ⟨28789161844575159729773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19192774563050106486515 28789161844575159729773)
      ·
        refine ⟨10795935691715684898665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28789161844575159729773 10795935691715684898665)
        ·
          refine ⟨8096951768786763673999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10795935691715684898665 8096951768786763673999)
          ·
            refine ⟨12145427653180145510999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8096951768786763673999 12145427653180145510999)
            ·
              refine ⟨18218141479770218266499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12145427653180145510999 18218141479770218266499)
              ·
                refine ⟨27327212219655327399749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18218141479770218266499 27327212219655327399749)
                ·
                  refine ⟨5123852291185373887453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27327212219655327399749 5123852291185373887453)
                  ·
                    refine ⟨1921444609194515207795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5123852291185373887453 1921444609194515207795)
                    ·
                      rfl

theorem cell22_5613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_5613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5613 prefixEnd_5613 := by exact prefixLift 5613
  have htrace : WordTrace (prefixWord ++ tailWord_5613) baseStart_5613 baseEnd_5613 := by
    simpa [prefixWord, tailWord_5613, baseEnd_5613] using wordTrace_append hprefix tailTrace_5613
  have hstable : (prefixWord ++ tailWord_5613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613).length < 2 ^ (prefixWord ++ tailWord_5613).sum := by decide
  have hdescent : baseEnd_5613 < baseStart_5613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_5630 : Nat := 118140960795 + 5630 * 2 ^ 59
def prefixEnd_5630 : Nat := 4983230072969 + 3 ^ 40 * 5630 * 2
def baseEnd_5630 : Nat := 1927264056612137532743

theorem tailTrace_5630 : CollatzResearch.WordTrace tailWord_5630 prefixEnd_5630 1927264056612137532743 := by
  unfold tailWord_5630
  simp only [CollatzResearch.WordTrace]
  refine ⟨25667871201368296569793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136895313073964248372229 25667871201368296569793)
  ·
    refine ⟨19250903401026222427345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25667871201368296569793 19250903401026222427345)
    ·
      refine ⟨14438177550769666820509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19250903401026222427345 14438177550769666820509)
      ·
        refine ⟨5414316581538625057691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14438177550769666820509 5414316581538625057691)
        ·
          refine ⟨8121474872307937586537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414316581538625057691 8121474872307937586537)
          ·
            refine ⟨6091106154230953189903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8121474872307937586537 6091106154230953189903)
            ·
              refine ⟨9136659231346429784855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6091106154230953189903 9136659231346429784855)
              ·
                refine ⟨13704988847019644677283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9136659231346429784855 13704988847019644677283)
                ·
                  refine ⟨20557483270529467015925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13704988847019644677283 20557483270529467015925)
                  ·
                    refine ⟨1927264056612137532743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20557483270529467015925 1927264056612137532743)
                    ·
                      rfl

theorem cell22_5630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_5630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5630 prefixEnd_5630 := by exact prefixLift 5630
  have htrace : WordTrace (prefixWord ++ tailWord_5630) baseStart_5630 baseEnd_5630 := by
    simpa [prefixWord, tailWord_5630, baseEnd_5630] using wordTrace_append hprefix tailTrace_5630
  have hstable : (prefixWord ++ tailWord_5630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630).length < 2 ^ (prefixWord ++ tailWord_5630).sum := by decide
  have hdescent : baseEnd_5630 < baseStart_5630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643 : List Nat := [1, 1, 1, 1, 9, 1, 2, 6]
def baseStart_5643 : Nat := 118140960795 + 5643 * 2 ^ 59
def prefixEnd_5643 : Nat := 4983230072969 + 3 ^ 40 * 5643 * 2
def baseEnd_5643 : Nat := 214634913587159661967

theorem tailTrace_5643 : CollatzResearch.WordTrace tailWord_5643 prefixEnd_5643 214634913587159661967 := by
  unfold tailWord_5643
  simp only [CollatzResearch.WordTrace]
  refine ⟨205817118563849592781583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137211412375899728521055 205817118563849592781583)
  ·
    refine ⟨308725677845774389172375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205817118563849592781583 308725677845774389172375)
    ·
      refine ⟨463088516768661583758563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308725677845774389172375 463088516768661583758563)
      ·
        refine ⟨694632775152992375637845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463088516768661583758563 694632775152992375637845)
        ·
          refine ⟨4070113916912064701003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 694632775152992375637845 4070113916912064701003)
          ·
            refine ⟨6105170875368097051505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070113916912064701003 6105170875368097051505)
            ·
              refine ⟨4578878156526072788629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6105170875368097051505 4578878156526072788629)
              ·
                refine ⟨214634913587159661967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4578878156526072788629 214634913587159661967)
                ·
                  rfl

theorem cell22_5643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 6].length) (baseStart_5643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5643 prefixEnd_5643 := by exact prefixLift 5643
  have htrace : WordTrace (prefixWord ++ tailWord_5643) baseStart_5643 baseEnd_5643 := by
    simpa [prefixWord, tailWord_5643, baseEnd_5643] using wordTrace_append hprefix tailTrace_5643
  have hstable : (prefixWord ++ tailWord_5643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643).length < 2 ^ (prefixWord ++ tailWord_5643).sum := by decide
  have hdescent : baseEnd_5643 < baseStart_5643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5662 : Nat := 118140960795 + 5662 * 2 ^ 59
def prefixEnd_5662 : Nat := 4983230072969 + 3 ^ 40 * 5662 * 2
def baseEnd_5662 : Nat := 1938218310574720732645

theorem tailTrace_5662 : CollatzResearch.WordTrace tailWord_5662 prefixEnd_5662 1938218310574720732645 := by
  unfold tailWord_5662
  simp only [CollatzResearch.WordTrace]
  refine ⟨25813763186876979715405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137673403663343891815493 25813763186876979715405)
  ·
    refine ⟨9680161195078867393277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25813763186876979715405 9680161195078867393277)
    ·
      refine ⟨3630060448154575272479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9680161195078867393277 3630060448154575272479)
      ·
        refine ⟨5445090672231862908719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630060448154575272479 5445090672231862908719)
        ·
          refine ⟨8167636008347794363079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445090672231862908719 8167636008347794363079)
          ·
            refine ⟨12251454012521691544619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8167636008347794363079 12251454012521691544619)
            ·
              refine ⟨18377181018782537316929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12251454012521691544619 18377181018782537316929)
              ·
                refine ⟨13782885764086902987697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18377181018782537316929 13782885764086902987697)
                ·
                  refine ⟨10337164323065177240773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13782885764086902987697 10337164323065177240773)
                  ·
                    refine ⟨1938218310574720732645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10337164323065177240773 1938218310574720732645)
                    ·
                      rfl

theorem cell22_5662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5662 prefixEnd_5662 := by exact prefixLift 5662
  have htrace : WordTrace (prefixWord ++ tailWord_5662) baseStart_5662 baseEnd_5662 := by
    simpa [prefixWord, tailWord_5662, baseEnd_5662] using wordTrace_append hprefix tailTrace_5662
  have hstable : (prefixWord ++ tailWord_5662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662).length < 2 ^ (prefixWord ++ tailWord_5662).sum := by decide
  have hdescent : baseEnd_5662 < baseStart_5662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 5]
def baseStart_5688 : Nat := 118140960795 + 5688 * 2 ^ 59
def prefixEnd_5688 : Nat := 4983230072969 + 3 ^ 40 * 5688 * 2
def baseEnd_5688 : Nat := 649039547306439860855

theorem tailTrace_5688 : CollatzResearch.WordTrace tailWord_5688 prefixEnd_5688 649039547306439860855 := by
  unfold tailWord_5688
  simp only [CollatzResearch.WordTrace]
  refine ⟨103729201700411139084859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138305602267214852113145 103729201700411139084859)
  ·
    refine ⟨155593802550616708627289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103729201700411139084859 155593802550616708627289)
    ·
      refine ⟨116695351912962531470467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155593802550616708627289 116695351912962531470467)
      ·
        refine ⟨175043027869443797205701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116695351912962531470467 175043027869443797205701)
        ·
          refine ⟨32820567725520711976069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175043027869443797205701 32820567725520711976069)
          ·
            refine ⟨6153856448535133495513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32820567725520711976069 6153856448535133495513)
            ·
              refine ⟨4615392336401350121635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6153856448535133495513 4615392336401350121635)
              ·
                refine ⟨6923088504602025182453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615392336401350121635 6923088504602025182453)
                ·
                  refine ⟨649039547306439860855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6923088504602025182453 649039547306439860855)
                  ·
                    rfl

theorem cell22_5688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_5688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5688 prefixEnd_5688 := by exact prefixLift 5688
  have htrace : WordTrace (prefixWord ++ tailWord_5688) baseStart_5688 baseEnd_5688 := by
    simpa [prefixWord, tailWord_5688, baseEnd_5688] using wordTrace_append hprefix tailTrace_5688
  have hstable : (prefixWord ++ tailWord_5688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688).length < 2 ^ (prefixWord ++ tailWord_5688).sum := by decide
  have hdescent : baseEnd_5688 < baseStart_5688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733 : List Nat := [1, 3, 1, 3, 3, 2, 1, 4, 4]
def baseStart_5733 : Nat := 118140960795 + 5733 * 2 ^ 59
def prefixEnd_5733 : Nat := 4983230072969 + 3 ^ 40 * 5733 * 2
def baseEnd_5733 : Nat := 654174353851400735809

theorem tailTrace_5733 : CollatzResearch.WordTrace tailWord_5733 prefixEnd_5733 654174353851400735809 := by
  unfold tailWord_5733
  simp only [CollatzResearch.WordTrace]
  refine ⟨209099688237794963557853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139399792158529975705235 209099688237794963557853)
  ·
    refine ⟨78412383089173111334195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209099688237794963557853 78412383089173111334195)
    ·
      refine ⟨117618574633759667001293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78412383089173111334195 117618574633759667001293)
      ·
        refine ⟨44106965487659875125485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117618574633759667001293 44106965487659875125485)
        ·
          refine ⟨16540112057872453172057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44106965487659875125485 16540112057872453172057)
          ·
            refine ⟨12405084043404339879043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16540112057872453172057 12405084043404339879043)
            ·
              refine ⟨18607626065106509818565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12405084043404339879043 18607626065106509818565)
              ·
                refine ⟨3488929887207470590981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18607626065106509818565 3488929887207470590981)
                ·
                  refine ⟨654174353851400735809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3488929887207470590981 654174353851400735809)
                  ·
                    rfl

theorem cell22_5733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_5733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5733 prefixEnd_5733 := by exact prefixLift 5733
  have htrace : WordTrace (prefixWord ++ tailWord_5733) baseStart_5733 baseEnd_5733 := by
    simpa [prefixWord, tailWord_5733, baseEnd_5733] using wordTrace_append hprefix tailTrace_5733
  have hstable : (prefixWord ++ tailWord_5733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733).length < 2 ^ (prefixWord ++ tailWord_5733).sum := by decide
  have hdescent : baseEnd_5733 < baseStart_5733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 3, 3]
def baseStart_5793 : Nat := 118140960795 + 5793 * 2 ^ 59
def prefixEnd_5793 : Nat := 4983230072969 + 3 ^ 40 * 5793 * 2
def baseEnd_5793 : Nat := 1983062287734045707243

theorem tailTrace_5793 : CollatzResearch.WordTrace tailWord_5793 prefixEnd_5793 1983062287734045707243 := by
  unfold tailWord_5793
  simp only [CollatzResearch.WordTrace]
  refine ⟨211288068020425210742033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140858712013616807161355 211288068020425210742033)
  ·
    refine ⟨158466051015318908056525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211288068020425210742033 158466051015318908056525)
    ·
      refine ⟨59424769130744590521197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158466051015318908056525 59424769130744590521197)
      ·
        refine ⟨22284288424029221445449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59424769130744590521197 22284288424029221445449)
        ·
          refine ⟨16713216318021916084087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22284288424029221445449 16713216318021916084087)
          ·
            refine ⟨25069824477032874126131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16713216318021916084087 25069824477032874126131)
            ·
              refine ⟨37604736715549311189197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25069824477032874126131 37604736715549311189197)
              ·
                refine ⟨14101776268330991695949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37604736715549311189197 14101776268330991695949)
                ·
                  refine ⟨5288166100624121885981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14101776268330991695949 5288166100624121885981)
                  ·
                    refine ⟨1983062287734045707243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5288166100624121885981 1983062287734045707243)
                    ·
                      rfl

theorem cell22_5793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_5793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5793 prefixEnd_5793 := by exact prefixLift 5793
  have htrace : WordTrace (prefixWord ++ tailWord_5793) baseStart_5793 baseEnd_5793 := by
    simpa [prefixWord, tailWord_5793, baseEnd_5793] using wordTrace_append hprefix tailTrace_5793
  have hstable : (prefixWord ++ tailWord_5793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793).length < 2 ^ (prefixWord ++ tailWord_5793).sum := by decide
  have hdescent : baseEnd_5793 < baseStart_5793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 8]
def baseStart_5819 : Nat := 118140960795 + 5819 * 2 ^ 59
def prefixEnd_5819 : Nat := 4983230072969 + 3 ^ 40 * 5819 * 2
def baseEnd_5819 : Nat := 1991962619078644557163

theorem tailTrace_5819 : CollatzResearch.WordTrace tailWord_5819 prefixEnd_5819 1991962619078644557163 := by
  unfold tailWord_5819
  simp only [CollatzResearch.WordTrace]
  refine ⟨212236365926231651188511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141490910617487767459007 212236365926231651188511)
  ·
    refine ⟨318354548889347476782767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212236365926231651188511 318354548889347476782767)
    ·
      refine ⟨477531823334021215174151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318354548889347476782767 477531823334021215174151)
      ·
        refine ⟨716297735001031822761227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477531823334021215174151 716297735001031822761227)
        ·
          refine ⟨1074446602501547734141841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716297735001031822761227 1074446602501547734141841)
          ·
            refine ⟨805834951876160800606381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074446602501547734141841 805834951876160800606381)
            ·
              refine ⟨302188106953560300227393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805834951876160800606381 302188106953560300227393)
              ·
                refine ⟨226641080215170225170545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302188106953560300227393 226641080215170225170545)
                ·
                  refine ⟨169980810161377668877909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226641080215170225170545 169980810161377668877909)
                  ·
                    refine ⟨1991962619078644557163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 169980810161377668877909 1991962619078644557163)
                    ·
                      rfl

theorem cell22_5819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_5819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5819 prefixEnd_5819 := by exact prefixLift 5819
  have htrace : WordTrace (prefixWord ++ tailWord_5819) baseStart_5819 baseEnd_5819 := by
    simpa [prefixWord, tailWord_5819, baseEnd_5819] using wordTrace_append hprefix tailTrace_5819
  have hstable : (prefixWord ++ tailWord_5819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819).length < 2 ^ (prefixWord ++ tailWord_5819).sum := by decide
  have hdescent : baseEnd_5819 < baseStart_5819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844 : List Nat := [2, 4, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_5844 : Nat := 118140960795 + 5844 * 2 ^ 59
def prefixEnd_5844 : Nat := 4983230072969 + 3 ^ 40 * 5844 * 2
def baseEnd_5844 : Nat := 2000520629986912682087

theorem tailTrace_5844 : CollatzResearch.WordTrace tailWord_5844 prefixEnd_5844 2000520629986912682087 := by
  unfold tailWord_5844
  simp only [CollatzResearch.WordTrace]
  refine ⟨106574095417830460424293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142098793890440613899057 106574095417830460424293)
  ·
    refine ⟨19982642890843211329555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106574095417830460424293 19982642890843211329555)
    ·
      refine ⟨29973964336264816994333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19982642890843211329555 29973964336264816994333)
      ·
        refine ⟨11240236626099306372875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29973964336264816994333 11240236626099306372875)
        ·
          refine ⟨16860354939148959559313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11240236626099306372875 16860354939148959559313)
          ·
            refine ⟨12645266204361719669485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16860354939148959559313 12645266204361719669485)
            ·
              refine ⟨4741974826635644876057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12645266204361719669485 4741974826635644876057)
              ·
                refine ⟨3556481119976733657043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4741974826635644876057 3556481119976733657043)
                ·
                  refine ⟨5334721679965100485565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556481119976733657043 5334721679965100485565)
                  ·
                    refine ⟨2000520629986912682087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5334721679965100485565 2000520629986912682087)
                    ·
                      rfl

theorem cell22_5844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_5844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5844 prefixEnd_5844 := by exact prefixLift 5844
  have htrace : WordTrace (prefixWord ++ tailWord_5844) baseStart_5844 baseEnd_5844 := by
    simpa [prefixWord, tailWord_5844, baseEnd_5844] using wordTrace_append hprefix tailTrace_5844
  have hstable : (prefixWord ++ tailWord_5844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844).length < 2 ^ (prefixWord ++ tailWord_5844).sum := by decide
  have hdescent : baseEnd_5844 < baseStart_5844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 5]
def baseStart_5857 : Nat := 118140960795 + 5857 * 2 ^ 59
def prefixEnd_5857 : Nat := 4983230072969 + 3 ^ 40 * 5857 * 2
def baseEnd_5857 : Nat := 668323598553070702349

theorem tailTrace_5857 : CollatzResearch.WordTrace tailWord_5857 prefixEnd_5857 668323598553070702349 := by
  unfold tailWord_5857
  simp only [CollatzResearch.WordTrace]
  refine ⟨213622339788564141071825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142414893192376094047883 213622339788564141071825)
  ·
    refine ⟨160216754841423105803869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213622339788564141071825 160216754841423105803869)
    ·
      refine ⟨60081283065533664676451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160216754841423105803869 60081283065533664676451)
      ·
        refine ⟨90121924598300497014677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60081283065533664676451 90121924598300497014677)
        ·
          refine ⟨4224465215545335797563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90121924598300497014677 4224465215545335797563)
          ·
            refine ⟨6336697823318003696345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224465215545335797563 6336697823318003696345)
            ·
              refine ⟨4752523367488502772259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6336697823318003696345 4752523367488502772259)
              ·
                refine ⟨7128785051232754158389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4752523367488502772259 7128785051232754158389)
                ·
                  refine ⟨668323598553070702349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7128785051232754158389 668323598553070702349)
                  ·
                    rfl

theorem cell22_5857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_5857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5857 prefixEnd_5857 := by exact prefixLift 5857
  have htrace : WordTrace (prefixWord ++ tailWord_5857) baseStart_5857 baseEnd_5857 := by
    simpa [prefixWord, tailWord_5857, baseEnd_5857] using wordTrace_append hprefix tailTrace_5857
  have hstable : (prefixWord ++ tailWord_5857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857).length < 2 ^ (prefixWord ++ tailWord_5857).sum := by decide
  have hdescent : baseEnd_5857 < baseStart_5857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_5898 : Nat := 118140960795 + 5898 * 2 ^ 59
def prefixEnd_5898 : Nat := 4983230072969 + 3 ^ 40 * 5898 * 2
def baseEnd_5898 : Nat := 2019005933548771831921

theorem tailTrace_5898 : CollatzResearch.WordTrace tailWord_5898 prefixEnd_5898 2019005933548771831921 := by
  unfold tailWord_5898
  simp only [CollatzResearch.WordTrace]
  refine ⟨53779433160007035828587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143411821760018762209565 53779433160007035828587)
  ·
    refine ⟨80669149740010553742881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53779433160007035828587 80669149740010553742881)
    ·
      refine ⟨60501862305007915307161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80669149740010553742881 60501862305007915307161)
      ·
        refine ⟨45376396728755936480371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60501862305007915307161 45376396728755936480371)
        ·
          refine ⟨68064595093133904720557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45376396728755936480371 68064595093133904720557)
          ·
            refine ⟨25524223159925214270209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68064595093133904720557 25524223159925214270209)
            ·
              refine ⟨19143167369943910702657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25524223159925214270209 19143167369943910702657)
              ·
                refine ⟨14357375527457933026993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19143167369943910702657 14357375527457933026993)
                ·
                  refine ⟨10768031645593449770245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14357375527457933026993 10768031645593449770245)
                  ·
                    refine ⟨2019005933548771831921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10768031645593449770245 2019005933548771831921)
                    ·
                      rfl

theorem cell22_5898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_5898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5898 prefixEnd_5898 := by exact prefixLift 5898
  have htrace : WordTrace (prefixWord ++ tailWord_5898) baseStart_5898 baseEnd_5898 := by
    simpa [prefixWord, tailWord_5898, baseEnd_5898] using wordTrace_append hprefix tailTrace_5898
  have hstable : (prefixWord ++ tailWord_5898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898).length < 2 ^ (prefixWord ++ tailWord_5898).sum := by decide
  have hdescent : baseEnd_5898 < baseStart_5898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_5973 : Nat := 118140960795 + 5973 * 2 ^ 59
def prefixEnd_5973 : Nat := 4983230072969 + 3 ^ 40 * 5973 * 2
def baseEnd_5973 : Nat := 2044679966273576206691

theorem tailTrace_5973 : CollatzResearch.WordTrace tailWord_5973 prefixEnd_5973 2044679966273576206691 := by
  unfold tailWord_5973
  simp only [CollatzResearch.WordTrace]
  refine ⟨217853207368315952294573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145235471578877301529715 217853207368315952294573)
  ·
    refine ⟨81694952763118482110465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217853207368315952294573 81694952763118482110465)
    ·
      refine ⟨61271214572338861582849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81694952763118482110465 61271214572338861582849)
      ·
        refine ⟨45953410929254146187137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61271214572338861582849 45953410929254146187137)
        ·
          refine ⟨34465058196940609640353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45953410929254146187137 34465058196940609640353)
          ·
            refine ⟨25848793647705457230265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34465058196940609640353 25848793647705457230265)
            ·
              refine ⟨19386595235779092922699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25848793647705457230265 19386595235779092922699)
              ·
                refine ⟨29079892853668639384049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19386595235779092922699 29079892853668639384049)
                ·
                  refine ⟨21809919640251479538037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29079892853668639384049 21809919640251479538037)
                  ·
                    refine ⟨2044679966273576206691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21809919640251479538037 2044679966273576206691)
                    ·
                      rfl

theorem cell22_5973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_5973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_5973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_5973 prefixEnd_5973 := by exact prefixLift 5973
  have htrace : WordTrace (prefixWord ++ tailWord_5973) baseStart_5973 baseEnd_5973 := by
    simpa [prefixWord, tailWord_5973, baseEnd_5973] using wordTrace_append hprefix tailTrace_5973
  have hstable : (prefixWord ++ tailWord_5973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973).length < 2 ^ (prefixWord ++ tailWord_5973).sum := by decide
  have hdescent : baseEnd_5973 < baseStart_5973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6005 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6005 : Nat := 118140960795 + 6005 * 2 ^ 59
def prefixEnd_6005 : Nat := 4983230072969 + 3 ^ 40 * 6005 * 2
def baseEnd_6005 : Nat := 2055634220236159406593

theorem tailTrace_6005 : CollatzResearch.WordTrace tailWord_6005 prefixEnd_6005 2055634220236159406593 := by
  unfold tailWord_6005
  simp only [CollatzResearch.WordTrace]
  refine ⟨219020343252385417459469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146013562168256944972979 219020343252385417459469)
  ·
    refine ⟨82132628719644531547301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219020343252385417459469 82132628719644531547301)
    ·
      refine ⟨15399867884933349665119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82132628719644531547301 15399867884933349665119)
      ·
        refine ⟨23099801827400024497679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15399867884933349665119 23099801827400024497679)
        ·
          refine ⟨34649702741100036746519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23099801827400024497679 34649702741100036746519)
          ·
            refine ⟨51974554111650055119779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34649702741100036746519 51974554111650055119779)
            ·
              refine ⟨77961831167475082679669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51974554111650055119779 77961831167475082679669)
              ·
                refine ⟨7308921671950789001219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77961831167475082679669 7308921671950789001219)
                ·
                  refine ⟨10963382507926183501829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7308921671950789001219 10963382507926183501829)
                  ·
                    refine ⟨2055634220236159406593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10963382507926183501829 2055634220236159406593)
                    ·
                      rfl

theorem cell22_6005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6005 prefixEnd_6005 := by exact prefixLift 6005
  have htrace : WordTrace (prefixWord ++ tailWord_6005) baseStart_6005 baseEnd_6005 := by
    simpa [prefixWord, tailWord_6005, baseEnd_6005] using wordTrace_append hprefix tailTrace_6005
  have hstable : (prefixWord ++ tailWord_6005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6005).length < 2 ^ (prefixWord ++ tailWord_6005).sum := by decide
  have hdescent : baseEnd_6005 < baseStart_6005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020 : List Nat := [2, 3, 2, 1, 1, 1, 2, 6, 4]
def baseStart_6020 : Nat := 118140960795 + 6020 * 2 ^ 59
def prefixEnd_6020 : Nat := 4983230072969 + 3 ^ 40 * 6020 * 2
def baseEnd_6020 : Nat := 686923008927040093849

theorem tailTrace_6020 : CollatzResearch.WordTrace tailWord_6020 prefixEnd_6020 686923008927040093849 := by
  unfold tailWord_6020
  simp only [CollatzResearch.WordTrace]
  refine ⟨109783719099021489627757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146378292132028652837009 109783719099021489627757)
  ·
    refine ⟨41168894662133058610409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109783719099021489627757 41168894662133058610409)
    ·
      refine ⟨30876670996599793957807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41168894662133058610409 30876670996599793957807)
      ·
        refine ⟨46315006494899690936711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30876670996599793957807 46315006494899690936711)
        ·
          refine ⟨69472509742349536405067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46315006494899690936711 69472509742349536405067)
          ·
            refine ⟨104208764613524304607601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69472509742349536405067 104208764613524304607601)
            ·
              refine ⟨78156573460143228455701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104208764613524304607601 78156573460143228455701)
              ·
                refine ⟨3663589380944213833861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78156573460143228455701 3663589380944213833861)
                ·
                  refine ⟨686923008927040093849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3663589380944213833861 686923008927040093849)
                  ·
                    rfl

theorem cell22_6020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_6020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6020 prefixEnd_6020 := by exact prefixLift 6020
  have htrace : WordTrace (prefixWord ++ tailWord_6020) baseStart_6020 baseEnd_6020 := by
    simpa [prefixWord, tailWord_6020, baseEnd_6020] using wordTrace_append hprefix tailTrace_6020
  have hstable : (prefixWord ++ tailWord_6020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020).length < 2 ^ (prefixWord ++ tailWord_6020).sum := by decide
  have hdescent : baseEnd_6020 < baseStart_6020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 1, 4]
def baseStart_6056 : Nat := 118140960795 + 6056 * 2 ^ 59
def prefixEnd_6056 : Nat := 4983230072969 + 3 ^ 40 * 6056 * 2
def baseEnd_6056 : Nat := 2073092562489026381437

theorem tailTrace_6056 : CollatzResearch.WordTrace tailWord_6056 prefixEnd_6056 2073092562489026381437 := by
  unfold tailWord_6056
  simp only [CollatzResearch.WordTrace]
  refine ⟨110440233033810563783011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147253644045080751710681 110440233033810563783011)
  ·
    refine ⟨165660349550715845674517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110440233033810563783011 165660349550715845674517)
    ·
      refine ⟨7765328885189805265993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165660349550715845674517 7765328885189805265993)
      ·
        refine ⟨5823996663892353949495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7765328885189805265993 5823996663892353949495)
        ·
          refine ⟨8735994995838530924243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823996663892353949495 8735994995838530924243)
          ·
            refine ⟨13103992493757796386365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735994995838530924243 13103992493757796386365)
            ·
              refine ⟨4913997185159173644887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13103992493757796386365 4913997185159173644887)
              ·
                refine ⟨7370995777738760467331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913997185159173644887 7370995777738760467331)
                ·
                  refine ⟨11056493666608140700997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7370995777738760467331 11056493666608140700997)
                  ·
                    refine ⟨2073092562489026381437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11056493666608140700997 2073092562489026381437)
                    ·
                      rfl

theorem cell22_6056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_6056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6056 prefixEnd_6056 := by exact prefixLift 6056
  have htrace : WordTrace (prefixWord ++ tailWord_6056) baseStart_6056 baseEnd_6056 := by
    simpa [prefixWord, tailWord_6056, baseEnd_6056] using wordTrace_append hprefix tailTrace_6056
  have hstable : (prefixWord ++ tailWord_6056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056).length < 2 ^ (prefixWord ++ tailWord_6056).sum := by decide
  have hdescent : baseEnd_6056 < baseStart_6056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 3, 3]
def baseStart_6080 : Nat := 118140960795 + 6080 * 2 ^ 59
def prefixEnd_6080 : Nat := 4983230072969 + 3 ^ 40 * 6080 * 2
def baseEnd_6080 : Nat := 2081308252960963781363

theorem tailTrace_6080 : CollatzResearch.WordTrace tailWord_6080 prefixEnd_6080 2081308252960963781363 := by
  unfold tailWord_6080
  simp only [CollatzResearch.WordTrace]
  refine ⟨110877908990336613219847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147837211987115484293129 110877908990336613219847)
  ·
    refine ⟨166316863485504919829771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110877908990336613219847 166316863485504919829771)
    ·
      refine ⟨249475295228257379744657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166316863485504919829771 249475295228257379744657)
      ·
        refine ⟨187106471421193034808493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249475295228257379744657 187106471421193034808493)
        ·
          refine ⟨70164926782947388053185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187106471421193034808493 70164926782947388053185)
          ·
            refine ⟨52623695087210541039889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70164926782947388053185 52623695087210541039889)
            ·
              refine ⟨39467771315407905779917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52623695087210541039889 39467771315407905779917)
              ·
                refine ⟨14800414243277964667469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39467771315407905779917 14800414243277964667469)
                ·
                  refine ⟨5550155341229236750301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14800414243277964667469 5550155341229236750301)
                  ·
                    refine ⟨2081308252960963781363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5550155341229236750301 2081308252960963781363)
                    ·
                      rfl

theorem cell22_6080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_6080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6080 prefixEnd_6080 := by exact prefixLift 6080
  have htrace : WordTrace (prefixWord ++ tailWord_6080) baseStart_6080 baseEnd_6080 := by
    simpa [prefixWord, tailWord_6080, baseEnd_6080] using wordTrace_append hprefix tailTrace_6080
  have hstable : (prefixWord ++ tailWord_6080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080).length < 2 ^ (prefixWord ++ tailWord_6080).sum := by decide
  have hdescent : baseEnd_6080 < baseStart_6080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6142 : Nat := 118140960795 + 6142 * 2 ^ 59
def prefixEnd_6142 : Nat := 4983230072969 + 3 ^ 40 * 6142 * 2
def baseEnd_6142 : Nat := 2102532120013468731173

theorem tailTrace_6142 : CollatzResearch.WordTrace tailWord_6142 prefixEnd_6142 2102532120013468731173 := by
  unfold tailWord_6142
  simp only [CollatzResearch.WordTrace]
  refine ⟨28002142969507226899585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149344762504038543464453 28002142969507226899585)
  ·
    refine ⟨21001607227130420174689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28002142969507226899585 21001607227130420174689)
    ·
      refine ⟨15751205420347815131017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21001607227130420174689 15751205420347815131017)
      ·
        refine ⟨11813404065260861348263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15751205420347815131017 11813404065260861348263)
        ·
          refine ⟨17720106097891292022395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11813404065260861348263 17720106097891292022395)
          ·
            refine ⟨26580159146836938033593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17720106097891292022395 26580159146836938033593)
            ·
              refine ⟨19935119360127703525195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26580159146836938033593 19935119360127703525195)
              ·
                refine ⟨29902679040191555287793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19935119360127703525195 29902679040191555287793)
                ·
                  refine ⟨22427009280143666465845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29902679040191555287793 22427009280143666465845)
                  ·
                    refine ⟨2102532120013468731173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22427009280143666465845 2102532120013468731173)
                    ·
                      rfl

theorem cell22_6142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6142 prefixEnd_6142 := by exact prefixLift 6142
  have htrace : WordTrace (prefixWord ++ tailWord_6142) baseStart_6142 baseEnd_6142 := by
    simpa [prefixWord, tailWord_6142, baseEnd_6142] using wordTrace_append hprefix tailTrace_6142
  have hstable : (prefixWord ++ tailWord_6142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142).length < 2 ^ (prefixWord ++ tailWord_6142).sum := by decide
  have hdescent : baseEnd_6142 < baseStart_6142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150 : List Nat := [6, 2, 1, 2, 2, 1, 2, 6]
def baseStart_6150 : Nat := 118140960795 + 6150 * 2 ^ 59
def prefixEnd_6150 : Nat := 4983230072969 + 3 ^ 40 * 6150 * 2
def baseEnd_6150 : Nat := 233918964833790503461

theorem tailTrace_6150 : CollatzResearch.WordTrace tailWord_6150 prefixEnd_6150 233918964833790503461 := by
  unfold tailWord_6150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009653991471099421497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149539285151383454325269 7009653991471099421497)
  ·
    refine ⟨5257240493603324566123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7009653991471099421497 5257240493603324566123)
    ·
      refine ⟨7885860740404986849185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257240493603324566123 7885860740404986849185)
      ·
        refine ⟨5914395555303740136889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7885860740404986849185 5914395555303740136889)
        ·
          refine ⟨4435796666477805102667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5914395555303740136889 4435796666477805102667)
          ·
            refine ⟨6653694999716707654001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435796666477805102667 6653694999716707654001)
            ·
              refine ⟨4990271249787530740501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653694999716707654001 4990271249787530740501)
              ·
                refine ⟨233918964833790503461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4990271249787530740501 233918964833790503461)
                ·
                  rfl

theorem cell22_6150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_6150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6150 prefixEnd_6150 := by exact prefixLift 6150
  have htrace : WordTrace (prefixWord ++ tailWord_6150) baseStart_6150 baseEnd_6150 := by
    simpa [prefixWord, tailWord_6150, baseEnd_6150] using wordTrace_append hprefix tailTrace_6150
  have hstable : (prefixWord ++ tailWord_6150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150).length < 2 ^ (prefixWord ++ tailWord_6150).sum := by decide
  have hdescent : baseEnd_6150 < baseStart_6150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249 : List Nat := [1, 2, 1, 1, 1, 5, 3, 4, 1, 3]
def baseStart_6249 : Nat := 118140960795 + 6249 * 2 ^ 59
def prefixEnd_6249 : Nat := 4983230072969 + 3 ^ 40 * 6249 * 2
def baseEnd_6249 : Nat := 2139160406700856305845

theorem tailTrace_6249 : CollatzResearch.WordTrace tailWord_6249 prefixEnd_6249 2139160406700856305845 := by
  unfold tailWord_6249
  simp only [CollatzResearch.WordTrace]
  refine ⟨227919754368415089341801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151946502912276726227867 227919754368415089341801)
  ·
    refine ⟨170939815776311317006351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227919754368415089341801 170939815776311317006351)
    ·
      refine ⟨256409723664466975509527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170939815776311317006351 256409723664466975509527)
      ·
        refine ⟨384614585496700463264291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256409723664466975509527 384614585496700463264291)
        ·
          refine ⟨576921878245050694896437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384614585496700463264291 576921878245050694896437)
          ·
            refine ⟨54086426085473502646541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 576921878245050694896437 54086426085473502646541)
            ·
              refine ⟨20282409782052563492453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54086426085473502646541 20282409782052563492453)
              ·
                refine ⟨3802951834134855654835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20282409782052563492453 3802951834134855654835)
                ·
                  refine ⟨5704427751202283482253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802951834134855654835 5704427751202283482253)
                  ·
                    refine ⟨2139160406700856305845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5704427751202283482253 2139160406700856305845)
                    ·
                      rfl

theorem cell22_6249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 3].length) (baseStart_6249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6249 prefixEnd_6249 := by exact prefixLift 6249
  have htrace : WordTrace (prefixWord ++ tailWord_6249) baseStart_6249 baseEnd_6249 := by
    simpa [prefixWord, tailWord_6249, baseEnd_6249] using wordTrace_append hprefix tailTrace_6249
  have hstable : (prefixWord ++ tailWord_6249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249).length < 2 ^ (prefixWord ++ tailWord_6249).sum := by decide
  have hdescent : baseEnd_6249 < baseStart_6249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 5]
def baseStart_6296 : Nat := 118140960795 + 6296 * 2 ^ 59
def prefixEnd_6296 : Nat := 4983230072969 + 3 ^ 40 * 6296 * 2
def baseEnd_6296 : Nat := 718416489069466793567

theorem tailTrace_6296 : CollatzResearch.WordTrace tailWord_6296 prefixEnd_6296 718416489069466793567 := by
  unfold tailWord_6296
  simp only [CollatzResearch.WordTrace]
  refine ⟨114816992599071058151371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153089323465428077535161 114816992599071058151371)
  ·
    refine ⟨172225488898606587227057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114816992599071058151371 172225488898606587227057)
    ·
      refine ⟨129169116673954940420293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172225488898606587227057 129169116673954940420293)
      ·
        refine ⟨24219209376366551328805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129169116673954940420293 24219209376366551328805)
        ·
          refine ⟨4541101758068728374151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24219209376366551328805 4541101758068728374151)
          ·
            refine ⟨6811652637103092561227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541101758068728374151 6811652637103092561227)
            ·
              refine ⟨10217478955654638841841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811652637103092561227 10217478955654638841841)
              ·
                refine ⟨7663109216740979131381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10217478955654638841841 7663109216740979131381)
                ·
                  refine ⟨718416489069466793567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7663109216740979131381 718416489069466793567)
                  ·
                    rfl

theorem cell22_6296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_6296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6296 prefixEnd_6296 := by exact prefixLift 6296
  have htrace : WordTrace (prefixWord ++ tailWord_6296) baseStart_6296 baseEnd_6296 := by
    simpa [prefixWord, tailWord_6296, baseEnd_6296] using wordTrace_append hprefix tailTrace_6296
  have hstable : (prefixWord ++ tailWord_6296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296).length < 2 ^ (prefixWord ++ tailWord_6296).sum := by decide
  have hdescent : baseEnd_6296 < baseStart_6296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_6354 : Nat := 118140960795 + 6354 * 2 ^ 59
def prefixEnd_6354 : Nat := 4983230072969 + 3 ^ 40 * 6354 * 2
def baseEnd_6354 : Nat := 2175104052515582430523

theorem tailTrace_6354 : CollatzResearch.WordTrace tailWord_6354 prefixEnd_6354 2175104052515582430523 := by
  unfold tailWord_6354
  simp only [CollatzResearch.WordTrace]
  refine ⟨57937354747004505478529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154499612658678681276077 57937354747004505478529)
  ·
    refine ⟨43453016060253379108897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57937354747004505478529 43453016060253379108897)
    ·
      refine ⟨32589762045190034331673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43453016060253379108897 32589762045190034331673)
      ·
        refine ⟨24442321533892525748755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32589762045190034331673 24442321533892525748755)
        ·
          refine ⟨36663482300838788623133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24442321533892525748755 36663482300838788623133)
          ·
            refine ⟨13748805862814545733675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36663482300838788623133 13748805862814545733675)
            ·
              refine ⟨20623208794221818600513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13748805862814545733675 20623208794221818600513)
              ·
                refine ⟨15467406595666363950385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20623208794221818600513 15467406595666363950385)
                ·
                  refine ⟨11600554946749772962789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15467406595666363950385 11600554946749772962789)
                  ·
                    refine ⟨2175104052515582430523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11600554946749772962789 2175104052515582430523)
                    ·
                      rfl

theorem cell22_6354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_6354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6354 prefixEnd_6354 := by exact prefixLift 6354
  have htrace : WordTrace (prefixWord ++ tailWord_6354) baseStart_6354 baseEnd_6354 := by
    simpa [prefixWord, tailWord_6354, baseEnd_6354] using wordTrace_append hprefix tailTrace_6354
  have hstable : (prefixWord ++ tailWord_6354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354).length < 2 ^ (prefixWord ++ tailWord_6354).sum := by decide
  have hdescent : baseEnd_6354 < baseStart_6354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6373 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_6373 : Nat := 118140960795 + 6373 * 2 ^ 59
def prefixEnd_6373 : Nat := 4983230072969 + 3 ^ 40 * 6373 * 2
def baseEnd_6373 : Nat := 2181608140805866205465

theorem tailTrace_6373 : CollatzResearch.WordTrace tailWord_6373 prefixEnd_6373 2181608140805866205465 := by
  unfold tailWord_6373
  simp only [CollatzResearch.WordTrace]
  refine ⟨232442405919184266855773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154961603946122844570515 232442405919184266855773)
  ·
    refine ⟨87165902219694100070915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232442405919184266855773 87165902219694100070915)
    ·
      refine ⟨130748853329541150106373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87165902219694100070915 130748853329541150106373)
      ·
        refine ⟨24515409999288965644945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130748853329541150106373 24515409999288965644945)
        ·
          refine ⟨18386557499466724233709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24515409999288965644945 18386557499466724233709)
          ·
            refine ⟨6894959062300021587641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18386557499466724233709 6894959062300021587641)
            ·
              refine ⟨5171219296725016190731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6894959062300021587641 5171219296725016190731)
              ·
                refine ⟨7756828945087524286097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171219296725016190731 7756828945087524286097)
                ·
                  refine ⟨5817621708815643214573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756828945087524286097 5817621708815643214573)
                  ·
                    refine ⟨2181608140805866205465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5817621708815643214573 2181608140805866205465)
                    ·
                      rfl

theorem cell22_6373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_6373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6373 prefixEnd_6373 := by exact prefixLift 6373
  have htrace : WordTrace (prefixWord ++ tailWord_6373) baseStart_6373 baseEnd_6373 := by
    simpa [prefixWord, tailWord_6373, baseEnd_6373] using wordTrace_append hprefix tailTrace_6373
  have hstable : (prefixWord ++ tailWord_6373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6373).length < 2 ^ (prefixWord ++ tailWord_6373).sum := by decide
  have hdescent : baseEnd_6373 < baseStart_6373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6401 : List Nat := [1, 2, 4, 1, 1, 2, 2, 5, 1, 3]
def baseStart_6401 : Nat := 118140960795 + 6401 * 2 ^ 59
def prefixEnd_6401 : Nat := 4983230072969 + 3 ^ 40 * 6401 * 2
def baseEnd_6401 : Nat := 2191193113023126505379

theorem tailTrace_6401 : CollatzResearch.WordTrace tailWord_6401 prefixEnd_6401 2191193113023126505379 := by
  unfold tailWord_6401
  simp only [CollatzResearch.WordTrace]
  refine ⟨233463649817745048875057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155642433211830032583371 233463649817745048875057)
  ·
    refine ⟨175097737363308786656293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233463649817745048875057 175097737363308786656293)
    ·
      refine ⟨32830825755620397498055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175097737363308786656293 32830825755620397498055)
      ·
        refine ⟨49246238633430596247083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32830825755620397498055 49246238633430596247083)
        ·
          refine ⟨73869357950145894370625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49246238633430596247083 73869357950145894370625)
          ·
            refine ⟨55402018462609420777969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73869357950145894370625 55402018462609420777969)
            ·
              refine ⟨41551513846957065583477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55402018462609420777969 41551513846957065583477)
              ·
                refine ⟨3895454423152224898451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41551513846957065583477 3895454423152224898451)
                ·
                  refine ⟨5843181634728337347677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895454423152224898451 5843181634728337347677)
                  ·
                    refine ⟨2191193113023126505379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5843181634728337347677 2191193113023126505379)
                    ·
                      rfl

theorem cell22_6401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_6401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6401 prefixEnd_6401 := by exact prefixLift 6401
  have htrace : WordTrace (prefixWord ++ tailWord_6401) baseStart_6401 baseEnd_6401 := by
    simpa [prefixWord, tailWord_6401, baseEnd_6401] using wordTrace_append hprefix tailTrace_6401
  have hstable : (prefixWord ++ tailWord_6401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6401).length < 2 ^ (prefixWord ++ tailWord_6401).sum := by decide
  have hdescent : baseEnd_6401 < baseStart_6401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_6412 : Nat := 118140960795 + 6412 * 2 ^ 59
def prefixEnd_6412 : Nat := 4983230072969 + 3 ^ 40 * 6412 * 2
def baseEnd_6412 : Nat := 2194958637822764480345

theorem tailTrace_6412 : CollatzResearch.WordTrace tailWord_6412 prefixEnd_6412 2194958637822764480345 := by
  unfold tailWord_6412
  simp only [CollatzResearch.WordTrace]
  refine ⟨116932426388946963762745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155909901851929285016993 116932426388946963762745)
  ·
    refine ⟨87699319791710222822059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116932426388946963762745 87699319791710222822059)
    ·
      refine ⟨131548979687565334233089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87699319791710222822059 131548979687565334233089)
      ·
        refine ⟨98661734765674000674817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131548979687565334233089 98661734765674000674817)
        ·
          refine ⟨73996301074255500506113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98661734765674000674817 73996301074255500506113)
          ·
            refine ⟨55497225805691625379585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73996301074255500506113 55497225805691625379585)
            ·
              refine ⟨41622919354268719034689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55497225805691625379585 41622919354268719034689)
              ·
                refine ⟨31217189515701539276017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41622919354268719034689 31217189515701539276017)
                ·
                  refine ⟨23412892136776154457013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31217189515701539276017 23412892136776154457013)
                  ·
                    refine ⟨2194958637822764480345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23412892136776154457013 2194958637822764480345)
                    ·
                      rfl

theorem cell22_6412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_6412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6412 prefixEnd_6412 := by exact prefixLift 6412
  have htrace : WordTrace (prefixWord ++ tailWord_6412) baseStart_6412 baseEnd_6412 := by
    simpa [prefixWord, tailWord_6412, baseEnd_6412] using wordTrace_append hprefix tailTrace_6412
  have hstable : (prefixWord ++ tailWord_6412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412).length < 2 ^ (prefixWord ++ tailWord_6412).sum := by decide
  have hdescent : baseEnd_6412 < baseStart_6412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_6414 : Nat := 118140960795 + 6414 * 2 ^ 59
def prefixEnd_6414 : Nat := 4983230072969 + 3 ^ 40 * 6414 * 2
def baseEnd_6414 : Nat := 731881092898475310113

theorem tailTrace_6414 : CollatzResearch.WordTrace tailWord_6414 prefixEnd_6414 731881092898475310113 := by
  unfold tailWord_6414
  simp only [CollatzResearch.WordTrace]
  refine ⟨29242224846331033637287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155958532513765512732197 29242224846331033637287)
  ·
    refine ⟨43863337269496550455931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29242224846331033637287 43863337269496550455931)
    ·
      refine ⟨65795005904244825683897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43863337269496550455931 65795005904244825683897)
      ·
        refine ⟨49346254428183619262923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65795005904244825683897 49346254428183619262923)
        ·
          refine ⟨74019381642275428894385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49346254428183619262923 74019381642275428894385)
          ·
            refine ⟨55514536231706571670789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74019381642275428894385 55514536231706571670789)
            ·
              refine ⟨10408975543444982188273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55514536231706571670789 10408975543444982188273)
              ·
                refine ⟨7806731657583736641205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10408975543444982188273 7806731657583736641205)
                ·
                  refine ⟨731881092898475310113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7806731657583736641205 731881092898475310113)
                  ·
                    rfl

theorem cell22_6414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_6414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6414 prefixEnd_6414 := by exact prefixLift 6414
  have htrace : WordTrace (prefixWord ++ tailWord_6414) baseStart_6414 baseEnd_6414 := by
    simpa [prefixWord, tailWord_6414, baseEnd_6414] using wordTrace_append hprefix tailTrace_6414
  have hstable : (prefixWord ++ tailWord_6414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414).length < 2 ^ (prefixWord ++ tailWord_6414).sum := by decide
  have hdescent : baseEnd_6414 < baseStart_6414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 3, 4]
def baseStart_6427 : Nat := 118140960795 + 6427 * 2 ^ 59
def prefixEnd_6427 : Nat := 4983230072969 + 3 ^ 40 * 6427 * 2
def baseEnd_6427 : Nat := 2200093444367725355299

theorem tailTrace_6427 : CollatzResearch.WordTrace tailWord_6427 prefixEnd_6427 2200093444367725355299 := by
  unfold tailWord_6427
  simp only [CollatzResearch.WordTrace]
  refine ⟨234411947723551489321535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156274631815700992881023 234411947723551489321535)
  ·
    refine ⟨351617921585327233982303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234411947723551489321535 351617921585327233982303)
    ·
      refine ⟨527426882377990850973455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351617921585327233982303 527426882377990850973455)
      ·
        refine ⟨791140323566986276460183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527426882377990850973455 791140323566986276460183)
        ·
          refine ⟨1186710485350479414690275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791140323566986276460183 1186710485350479414690275)
          ·
            refine ⟨1780065728025719122035413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186710485350479414690275 1780065728025719122035413)
            ·
              refine ⟨41720290500602791922705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1780065728025719122035413 41720290500602791922705)
              ·
                refine ⟨31290217875452093942029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41720290500602791922705 31290217875452093942029)
                ·
                  refine ⟨11733831703294535228261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31290217875452093942029 11733831703294535228261)
                  ·
                    refine ⟨2200093444367725355299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11733831703294535228261 2200093444367725355299)
                    ·
                      rfl

theorem cell22_6427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_6427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6427 prefixEnd_6427 := by exact prefixLift 6427
  have htrace : WordTrace (prefixWord ++ tailWord_6427) baseStart_6427 baseEnd_6427 := by
    simpa [prefixWord, tailWord_6427, baseEnd_6427] using wordTrace_append hprefix tailTrace_6427
  have hstable : (prefixWord ++ tailWord_6427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427).length < 2 ^ (prefixWord ++ tailWord_6427).sum := by decide
  have hdescent : baseEnd_6427 < baseStart_6427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487 : List Nat := [1, 1, 3, 2, 3, 1, 2, 9]
def baseStart_6487 : Nat := 118140960795 + 6487 * 2 ^ 59
def prefixEnd_6487 : Nat := 4983230072969 + 3 ^ 40 * 6487 * 2
def baseEnd_6487 : Nat := 246736963394174317235

theorem tailTrace_6487 : CollatzResearch.WordTrace tailWord_6487 prefixEnd_6487 246736963394174317235 := by
  unfold tailWord_6487
  simp only [CollatzResearch.WordTrace]
  refine ⟨236600327506181736505715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157733551670787824337143 236600327506181736505715)
  ·
    refine ⟨354900491259272604758573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236600327506181736505715 354900491259272604758573)
    ·
      refine ⟨133087684222227226784465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354900491259272604758573 133087684222227226784465)
      ·
        refine ⟨99815763166670420088349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133087684222227226784465 99815763166670420088349)
        ·
          refine ⟨37430911187501407533131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99815763166670420088349 37430911187501407533131)
          ·
            refine ⟨56146366781252111299697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37430911187501407533131 56146366781252111299697)
            ·
              refine ⟨42109775085939083474773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56146366781252111299697 42109775085939083474773)
              ·
                refine ⟨246736963394174317235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 42109775085939083474773 246736963394174317235)
                ·
                  rfl

theorem cell22_6487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 9].length) (baseStart_6487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6487 prefixEnd_6487 := by exact prefixLift 6487
  have htrace : WordTrace (prefixWord ++ tailWord_6487) baseStart_6487 baseEnd_6487 := by
    simpa [prefixWord, tailWord_6487, baseEnd_6487] using wordTrace_append hprefix tailTrace_6487
  have hstable : (prefixWord ++ tailWord_6487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487).length < 2 ^ (prefixWord ++ tailWord_6487).sum := by decide
  have hdescent : baseEnd_6487 < baseStart_6487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504 : List Nat := [2, 1, 4, 2, 2, 2, 1, 8]
def baseStart_6504 : Nat := 118140960795 + 6504 * 2 ^ 59
def prefixEnd_6504 : Nat := 4983230072969 + 3 ^ 40 * 6504 * 2
def baseEnd_6504 : Nat := 247383568662799020007

theorem tailTrace_6504 : CollatzResearch.WordTrace tailWord_6504 prefixEnd_6504 247383568662799020007 := by
  unfold tailWord_6504
  simp only [CollatzResearch.WordTrace]
  refine ⟨118610184222296819937283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158146912296395759916377 118610184222296819937283)
  ·
    refine ⟨177915276333445229905925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118610184222296819937283 177915276333445229905925)
    ·
      refine ⟨33359114312520980607361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177915276333445229905925 33359114312520980607361)
      ·
        refine ⟨25019335734390735455521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33359114312520980607361 25019335734390735455521)
        ·
          refine ⟨18764501800793051591641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25019335734390735455521 18764501800793051591641)
          ·
            refine ⟨14073376350594788693731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18764501800793051591641 14073376350594788693731)
            ·
              refine ⟨21110064525892183040597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14073376350594788693731 21110064525892183040597)
              ·
                refine ⟨247383568662799020007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 21110064525892183040597 247383568662799020007)
                ·
                  rfl

theorem cell22_6504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_6504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6504 prefixEnd_6504 := by exact prefixLift 6504
  have htrace : WordTrace (prefixWord ++ tailWord_6504) baseStart_6504 baseEnd_6504 := by
    simpa [prefixWord, tailWord_6504, baseEnd_6504] using wordTrace_append hprefix tailTrace_6504
  have hstable : (prefixWord ++ tailWord_6504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504).length < 2 ^ (prefixWord ++ tailWord_6504).sum := by decide
  have hdescent : baseEnd_6504 < baseStart_6504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_6624 : Nat := 118140960795 + 6624 * 2 ^ 59
def prefixEnd_6624 : Nat := 4983230072969 + 3 ^ 40 * 6624 * 2
def baseEnd_6624 : Nat := 2267530570324878179695

theorem tailTrace_6624 : CollatzResearch.WordTrace tailWord_6624 prefixEnd_6624 2267530570324878179695 := by
  unfold tailWord_6624
  simp only [CollatzResearch.WordTrace]
  refine ⟨120798564004927067121463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161064752006569422828617 120798564004927067121463)
  ·
    refine ⟨181197846007390600682195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120798564004927067121463 181197846007390600682195)
    ·
      refine ⟨271796769011085901023293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181197846007390600682195 271796769011085901023293)
      ·
        refine ⟨101923788379157212883735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271796769011085901023293 101923788379157212883735)
        ·
          refine ⟨152885682568735819325603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101923788379157212883735 152885682568735819325603)
          ·
            refine ⟨229328523853103728988405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152885682568735819325603 229328523853103728988405)
            ·
              refine ⟨21499549111228474592663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229328523853103728988405 21499549111228474592663)
              ·
                refine ⟨32249323666842711888995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21499549111228474592663 32249323666842711888995)
                ·
                  refine ⟨48373985500264067833493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32249323666842711888995 48373985500264067833493)
                  ·
                    refine ⟨2267530570324878179695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48373985500264067833493 2267530570324878179695)
                    ·
                      rfl

theorem cell22_6624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_6624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6624 prefixEnd_6624 := by exact prefixLift 6624
  have htrace : WordTrace (prefixWord ++ tailWord_6624) baseStart_6624 baseEnd_6624 := by
    simpa [prefixWord, tailWord_6624, baseEnd_6624] using wordTrace_append hprefix tailTrace_6624
  have hstable : (prefixWord ++ tailWord_6624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624).length < 2 ^ (prefixWord ++ tailWord_6624).sum := by decide
  have hdescent : baseEnd_6624 < baseStart_6624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 4, 5]
def baseStart_6699 : Nat := 118140960795 + 6699 * 2 ^ 59
def prefixEnd_6699 : Nat := 4983230072969 + 3 ^ 40 * 6699 * 2
def baseEnd_6699 : Nat := 2293204603049682554465

theorem tailTrace_6699 : CollatzResearch.WordTrace tailWord_6699 prefixEnd_6699 2293204603049682554465 := by
  unfold tailWord_6699
  simp only [CollatzResearch.WordTrace]
  refine ⟨244332602738141943223151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162888401825427962148767 244332602738141943223151)
  ·
    refine ⟨366498904107212914834727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244332602738141943223151 366498904107212914834727)
    ·
      refine ⟨549748356160819372252091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366498904107212914834727 549748356160819372252091)
      ·
        refine ⟨824622534241229058378137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549748356160819372252091 824622534241229058378137)
        ·
          refine ⟨618466900680921793783603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824622534241229058378137 618466900680921793783603)
          ·
            refine ⟨927700351021382690675405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618466900680921793783603 927700351021382690675405)
            ·
              refine ⟨347887631633018509003277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 927700351021382690675405 347887631633018509003277)
              ·
                refine ⟨130457861862381940876229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347887631633018509003277 130457861862381940876229)
                ·
                  refine ⟨24460849099196613914293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130457861862381940876229 24460849099196613914293)
                  ·
                    refine ⟨2293204603049682554465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24460849099196613914293 2293204603049682554465)
                    ·
                      rfl

theorem cell22_6699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_6699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6699 prefixEnd_6699 := by exact prefixLift 6699
  have htrace : WordTrace (prefixWord ++ tailWord_6699) baseStart_6699 baseEnd_6699 := by
    simpa [prefixWord, tailWord_6699, baseEnd_6699] using wordTrace_append hprefix tailTrace_6699
  have hstable : (prefixWord ++ tailWord_6699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699).length < 2 ^ (prefixWord ++ tailWord_6699).sum := by decide
  have hdescent : baseEnd_6699 < baseStart_6699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_6812 : Nat := 118140960795 + 6812 * 2 ^ 59
def prefixEnd_6812 : Nat := 4983230072969 + 3 ^ 40 * 6812 * 2
def baseEnd_6812 : Nat := 2331886812355054479119

theorem tailTrace_6812 : CollatzResearch.WordTrace tailWord_6812 prefixEnd_6812 2331886812355054479119 := by
  unfold tailWord_6812
  simp only [CollatzResearch.WordTrace]
  refine ⟨124227025664381121043345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165636034219174828057793 124227025664381121043345)
  ·
    refine ⟨93170269248285840782509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124227025664381121043345 93170269248285840782509)
    ·
      refine ⟨34938850968107190293441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93170269248285840782509 34938850968107190293441)
      ·
        refine ⟨26204138226080392720081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34938850968107190293441 26204138226080392720081)
        ·
          refine ⟨19653103669560294540061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26204138226080392720081 19653103669560294540061)
          ·
            refine ⟨7369913876085110452523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19653103669560294540061 7369913876085110452523)
            ·
              refine ⟨11054870814127665678785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369913876085110452523 11054870814127665678785)
              ·
                refine ⟨8291153110595749259089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11054870814127665678785 8291153110595749259089)
                ·
                  refine ⟨6218364832946811944317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8291153110595749259089 6218364832946811944317)
                  ·
                    refine ⟨2331886812355054479119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6218364832946811944317 2331886812355054479119)
                    ·
                      rfl

theorem cell22_6812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_6812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6812 prefixEnd_6812 := by exact prefixLift 6812
  have htrace : WordTrace (prefixWord ++ tailWord_6812) baseStart_6812 baseEnd_6812 := by
    simpa [prefixWord, tailWord_6812, baseEnd_6812] using wordTrace_append hprefix tailTrace_6812
  have hstable : (prefixWord ++ tailWord_6812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812).length < 2 ^ (prefixWord ++ tailWord_6812).sum := by decide
  have hdescent : baseEnd_6812 < baseStart_6812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943 : List Nat := [1, 1, 2, 4, 2, 2, 3, 7]
def baseStart_6943 : Nat := 118140960795 + 6943 * 2 ^ 59
def prefixEnd_6943 : Nat := 4983230072969 + 3 ^ 40 * 6943 * 2
def baseEnd_6943 : Nat := 264081198834931050413

theorem tailTrace_6943 : CollatzResearch.WordTrace tailWord_6943 prefixEnd_6943 264081198834931050413 := by
  unfold tailWord_6943
  simp only [CollatzResearch.WordTrace]
  refine ⟨253232013854171615105483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168821342569447743403655 253232013854171615105483)
  ·
    refine ⟨379848020781257422658225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253232013854171615105483 379848020781257422658225)
    ·
      refine ⟨284886015585943066993669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379848020781257422658225 284886015585943066993669)
      ·
        refine ⟨53416127922364325061313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284886015585943066993669 53416127922364325061313)
        ·
          refine ⟨40062095941773243795985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53416127922364325061313 40062095941773243795985)
          ·
            refine ⟨30046571956329932846989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40062095941773243795985 30046571956329932846989)
            ·
              refine ⟨11267464483623724817621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30046571956329932846989 11267464483623724817621)
              ·
                refine ⟨264081198834931050413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11267464483623724817621 264081198834931050413)
                ·
                  rfl

theorem cell22_6943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 7].length) (baseStart_6943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6943 prefixEnd_6943 := by exact prefixLift 6943
  have htrace : WordTrace (prefixWord ++ tailWord_6943) baseStart_6943 baseEnd_6943 := by
    simpa [prefixWord, tailWord_6943, baseEnd_6943] using wordTrace_append hprefix tailTrace_6943
  have hstable : (prefixWord ++ tailWord_6943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943).length < 2 ^ (prefixWord ++ tailWord_6943).sum := by decide
  have hdescent : baseEnd_6943 < baseStart_6943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992 : List Nat := [2, 1, 1, 1, 1, 4, 4, 4, 1, 3]
def baseStart_6992 : Nat := 118140960795 + 6992 * 2 ^ 59
def prefixEnd_6992 : Nat := 4983230072969 + 3 ^ 40 * 6992 * 2
def baseEnd_6992 : Nat := 2393504490894584978567

theorem tailTrace_6992 : CollatzResearch.WordTrace tailWord_6992 prefixEnd_6992 2393504490894584978567 := by
  unfold tailWord_6992
  simp only [CollatzResearch.WordTrace]
  refine ⟨127509595338326491819615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170012793784435322426153 127509595338326491819615)
  ·
    refine ⟨191264393007489737729423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127509595338326491819615 191264393007489737729423)
    ·
      refine ⟨286896589511234606594135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191264393007489737729423 286896589511234606594135)
      ·
        refine ⟨430344884266851909891203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286896589511234606594135 430344884266851909891203)
        ·
          refine ⟨645517326400277864836805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430344884266851909891203 645517326400277864836805)
          ·
            refine ⟨121034498700052099656901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 645517326400277864836805 121034498700052099656901)
            ·
              refine ⟨22693968506259768685669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121034498700052099656901 22693968506259768685669)
              ·
                refine ⟨4255119094923706628563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22693968506259768685669 4255119094923706628563)
                ·
                  refine ⟨6382678642385559942845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255119094923706628563 6382678642385559942845)
                  ·
                    refine ⟨2393504490894584978567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6382678642385559942845 2393504490894584978567)
                    ·
                      rfl

theorem cell22_6992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 3].length) (baseStart_6992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_6992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_6992 prefixEnd_6992 := by exact prefixLift 6992
  have htrace : WordTrace (prefixWord ++ tailWord_6992) baseStart_6992 baseEnd_6992 := by
    simpa [prefixWord, tailWord_6992, baseEnd_6992] using wordTrace_append hprefix tailTrace_6992
  have hstable : (prefixWord ++ tailWord_6992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992).length < 2 ^ (prefixWord ++ tailWord_6992).sum := by decide
  have hdescent : baseEnd_6992 < baseStart_6992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 1, 4]
def baseStart_7035 : Nat := 118140960795 + 7035 * 2 ^ 59
def prefixEnd_7035 : Nat := 4983230072969 + 3 ^ 40 * 7035 * 2
def baseEnd_7035 : Nat := 2408224269656806153435

theorem tailTrace_7035 : CollatzResearch.WordTrace tailWord_7035 prefixEnd_7035 2408224269656806153435 := by
  unfold tailWord_7035
  simp only [CollatzResearch.WordTrace]
  refine ⟨256587529520871327454559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171058353013914218303039 256587529520871327454559)
  ·
    refine ⟨384881294281306991181839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256587529520871327454559 384881294281306991181839)
    ·
      refine ⟨577321941421960486772759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384881294281306991181839 577321941421960486772759)
      ·
        refine ⟨865982912132940730159139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577321941421960486772759 865982912132940730159139)
        ·
          refine ⟨1298974368199411095238709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865982912132940730159139 1298974368199411095238709)
          ·
            refine ⟨121778847018694790178629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1298974368199411095238709 121778847018694790178629)
            ·
              refine ⟨22833533816005273158493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121778847018694790178629 22833533816005273158493)
              ·
                refine ⟨8562575181001977434435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22833533816005273158493 8562575181001977434435)
                ·
                  refine ⟨12843862771502966151653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562575181001977434435 12843862771502966151653)
                  ·
                    refine ⟨2408224269656806153435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12843862771502966151653 2408224269656806153435)
                    ·
                      rfl

theorem cell22_7035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 4].length) (baseStart_7035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7035 prefixEnd_7035 := by exact prefixLift 7035
  have htrace : WordTrace (prefixWord ++ tailWord_7035) baseStart_7035 baseEnd_7035 := by
    simpa [prefixWord, tailWord_7035, baseEnd_7035] using wordTrace_append hprefix tailTrace_7035
  have hstable : (prefixWord ++ tailWord_7035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035).length < 2 ^ (prefixWord ++ tailWord_7035).sum := by decide
  have hdescent : baseEnd_7035 < baseStart_7035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7094 : List Nat := [5, 1, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7094 : Nat := 118140960795 + 7094 * 2 ^ 59
def prefixEnd_7094 : Nat := 4983230072969 + 3 ^ 40 * 7094 * 2
def baseEnd_7094 : Nat := 2428421175400318928255

theorem tailTrace_7094 : CollatzResearch.WordTrace tailWord_7094 prefixEnd_7094 2428421175400318928255 := by
  unfold tailWord_7094
  simp only [CollatzResearch.WordTrace]
  refine ⟨16171214769195275240771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172492957538082935901557 16171214769195275240771)
  ·
    refine ⟨24256822153792912861157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16171214769195275240771 24256822153792912861157)
    ·
      refine ⟨4548154153836171161467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24256822153792912861157 4548154153836171161467)
      ·
        refine ⟨6822231230754256742201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4548154153836171161467 6822231230754256742201)
        ·
          refine ⟨5116673423065692556651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6822231230754256742201 5116673423065692556651)
          ·
            refine ⟨7675010134598538834977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116673423065692556651 7675010134598538834977)
            ·
              refine ⟨5756257600948904126233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7675010134598538834977 5756257600948904126233)
              ·
                refine ⟨4317193200711678094675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756257600948904126233 4317193200711678094675)
                ·
                  refine ⟨6475789801067517142013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317193200711678094675 6475789801067517142013)
                  ·
                    refine ⟨2428421175400318928255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6475789801067517142013 2428421175400318928255)
                    ·
                      rfl

theorem cell22_7094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7094 prefixEnd_7094 := by exact prefixLift 7094
  have htrace : WordTrace (prefixWord ++ tailWord_7094) baseStart_7094 baseEnd_7094 := by
    simpa [prefixWord, tailWord_7094, baseEnd_7094] using wordTrace_append hprefix tailTrace_7094
  have hstable : (prefixWord ++ tailWord_7094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7094).length < 2 ^ (prefixWord ++ tailWord_7094).sum := by decide
  have hdescent : baseEnd_7094 < baseStart_7094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101 : List Nat := [1, 4, 1, 2, 4, 2, 2, 2, 4]
def baseStart_7101 : Nat := 118140960795 + 7101 * 2 ^ 59
def prefixEnd_7101 : Nat := 4983230072969 + 3 ^ 40 * 7101 * 2
def baseEnd_7101 : Nat := 810272472818211334411

theorem tailTrace_7101 : CollatzResearch.WordTrace tailWord_7101 prefixEnd_7101 810272472818211334411 := by
  unfold tailWord_7101
  simp only [CollatzResearch.WordTrace]
  refine ⟨258994747281764599357157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172663164854509732904771 258994747281764599357157)
  ·
    refine ⟨48561515115330862379467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258994747281764599357157 48561515115330862379467)
    ·
      refine ⟨72842272672996293569201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48561515115330862379467 72842272672996293569201)
      ·
        refine ⟨54631704504747220176901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72842272672996293569201 54631704504747220176901)
        ·
          refine ⟨10243444594640103783169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54631704504747220176901 10243444594640103783169)
          ·
            refine ⟨7682583445980077837377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10243444594640103783169 7682583445980077837377)
            ·
              refine ⟨5761937584485058378033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7682583445980077837377 5761937584485058378033)
              ·
                refine ⟨4321453188363793783525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5761937584485058378033 4321453188363793783525)
                ·
                  refine ⟨810272472818211334411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4321453188363793783525 810272472818211334411)
                  ·
                    rfl

theorem cell22_7101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_7101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7101 prefixEnd_7101 := by exact prefixLift 7101
  have htrace : WordTrace (prefixWord ++ tailWord_7101) baseStart_7101 baseEnd_7101 := by
    simpa [prefixWord, tailWord_7101, baseEnd_7101] using wordTrace_append hprefix tailTrace_7101
  have hstable : (prefixWord ++ tailWord_7101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101).length < 2 ^ (prefixWord ++ tailWord_7101).sum := by decide
  have hdescent : baseEnd_7101 < baseStart_7101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112 : List Nat := [2, 1, 3, 1, 5, 2, 1, 7]
def baseStart_7112 : Nat := 118140960795 + 7112 * 2 ^ 59
def prefixEnd_7112 : Nat := 4983230072969 + 3 ^ 40 * 7112 * 2
def baseEnd_7112 : Nat := 270509215917141330911

theorem tailTrace_7112 : CollatzResearch.WordTrace tailWord_7112 prefixEnd_7112 270509215917141330911 := by
  unfold tailWord_7112
  simp only [CollatzResearch.WordTrace]
  refine ⟨129697975120956739003795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172930633494608985338393 129697975120956739003795)
  ·
    refine ⟨194546962681435108505693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129697975120956739003795 194546962681435108505693)
    ·
      refine ⟨72955111005538165689635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194546962681435108505693 72955111005538165689635)
      ·
        refine ⟨109432666508307248534453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72955111005538165689635 109432666508307248534453)
        ·
          refine ⟨10259312485153804550105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109432666508307248534453 10259312485153804550105)
          ·
            refine ⟨7694484363865353412579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10259312485153804550105 7694484363865353412579)
            ·
              refine ⟨11541726545798030118869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694484363865353412579 11541726545798030118869)
              ·
                refine ⟨270509215917141330911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11541726545798030118869 270509215917141330911)
                ·
                  rfl

theorem cell22_7112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 7].length) (baseStart_7112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7112 prefixEnd_7112 := by exact prefixLift 7112
  have htrace : WordTrace (prefixWord ++ tailWord_7112) baseStart_7112 baseEnd_7112 := by
    simpa [prefixWord, tailWord_7112, baseEnd_7112] using wordTrace_append hprefix tailTrace_7112
  have hstable : (prefixWord ++ tailWord_7112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112).length < 2 ^ (prefixWord ++ tailWord_7112).sum := by decide
  have hdescent : baseEnd_7112 < baseStart_7112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144 : List Nat := [2, 1, 4, 1, 1, 1, 3, 5, 1, 3]
def baseStart_7144 : Nat := 118140960795 + 7144 * 2 ^ 59
def prefixEnd_7144 : Nat := 4983230072969 + 3 ^ 40 * 7144 * 2
def baseEnd_7144 : Nat := 2445537197216855178101

theorem tailTrace_7144 : CollatzResearch.WordTrace tailWord_7144 prefixEnd_7144 2445537197216855178101 := by
  unfold tailWord_7144
  simp only [CollatzResearch.WordTrace]
  refine ⟨130281543062991471586243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173708724083988628781657 130281543062991471586243)
  ·
    refine ⟨195422314594487207379365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130281543062991471586243 195422314594487207379365)
    ·
      refine ⟨36641683986466351383631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195422314594487207379365 36641683986466351383631)
      ·
        refine ⟨54962525979699527075447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36641683986466351383631 54962525979699527075447)
        ·
          refine ⟨82443788969549290613171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54962525979699527075447 82443788969549290613171)
          ·
            refine ⟨123665683454323935919757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82443788969549290613171 123665683454323935919757)
            ·
              refine ⟨46374631295371475969909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123665683454323935919757 46374631295371475969909)
              ·
                refine ⟨4347621683941075872179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46374631295371475969909 4347621683941075872179)
                ·
                  refine ⟨6521432525911613808269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347621683941075872179 6521432525911613808269)
                  ·
                    refine ⟨2445537197216855178101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6521432525911613808269 2445537197216855178101)
                    ·
                      rfl

theorem cell22_7144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_7144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7144 prefixEnd_7144 := by exact prefixLift 7144
  have htrace : WordTrace (prefixWord ++ tailWord_7144) baseStart_7144 baseEnd_7144 := by
    simpa [prefixWord, tailWord_7144, baseEnd_7144] using wordTrace_append hprefix tailTrace_7144
  have hstable : (prefixWord ++ tailWord_7144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144).length < 2 ^ (prefixWord ++ tailWord_7144).sum := by decide
  have hdescent : baseEnd_7144 < baseStart_7144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_7204 : Nat := 118140960795 + 7204 * 2 ^ 59
def prefixEnd_7204 : Nat := 4983230072969 + 3 ^ 40 * 7204 * 2
def baseEnd_7204 : Nat := 2466076423396698677917

theorem tailTrace_7204 : CollatzResearch.WordTrace tailWord_7204 prefixEnd_7204 2466076423396698677917 := by
  unfold tailWord_7204
  simp only [CollatzResearch.WordTrace]
  refine ⟨131375732954306595178333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175167643939075460237777 131375732954306595178333)
  ·
    refine ⟨49265899857864973191875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131375732954306595178333 49265899857864973191875)
    ·
      refine ⟨73898849786797459787813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49265899857864973191875 73898849786797459787813)
      ·
        refine ⟨13856034335024523710215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73898849786797459787813 13856034335024523710215)
        ·
          refine ⟨20784051502536785565323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13856034335024523710215 20784051502536785565323)
          ·
            refine ⟨31176077253805178347985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20784051502536785565323 31176077253805178347985)
            ·
              refine ⟨23382057940353883760989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31176077253805178347985 23382057940353883760989)
              ·
                refine ⟨8768271727632706410371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23382057940353883760989 8768271727632706410371)
                ·
                  refine ⟨13152407591449059615557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8768271727632706410371 13152407591449059615557)
                  ·
                    refine ⟨2466076423396698677917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13152407591449059615557 2466076423396698677917)
                    ·
                      rfl

theorem cell22_7204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_7204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7204 prefixEnd_7204 := by exact prefixLift 7204
  have htrace : WordTrace (prefixWord ++ tailWord_7204) baseStart_7204 baseEnd_7204 := by
    simpa [prefixWord, tailWord_7204, baseEnd_7204] using wordTrace_append hprefix tailTrace_7204
  have hstable : (prefixWord ++ tailWord_7204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204).length < 2 ^ (prefixWord ++ tailWord_7204).sum := by decide
  have hdescent : baseEnd_7204 < baseStart_7204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 4, 3]
def baseStart_7217 : Nat := 118140960795 + 7217 * 2 ^ 59
def prefixEnd_7217 : Nat := 4983230072969 + 3 ^ 40 * 7217 * 2
def baseEnd_7217 : Nat := 2470526589068998102877

theorem tailTrace_7217 : CollatzResearch.WordTrace tailWord_7217 prefixEnd_7217 2470526589068998102877 := by
  unfold tailWord_7217
  simp only [CollatzResearch.WordTrace]
  refine ⟨263225614861516410579905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175483743241010940386603 263225614861516410579905)
  ·
    refine ⟨197419211146137307934929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263225614861516410579905 197419211146137307934929)
    ·
      refine ⟨148064408359602980951197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197419211146137307934929 148064408359602980951197)
      ·
        refine ⟨55524153134851117856699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148064408359602980951197 55524153134851117856699)
        ·
          refine ⟨83286229702276676785049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55524153134851117856699 83286229702276676785049)
          ·
            refine ⟨62464672276707507588787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83286229702276676785049 62464672276707507588787)
            ·
              refine ⟨93697008415061261383181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62464672276707507588787 93697008415061261383181)
              ·
                refine ⟨35136378155647973018693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93697008415061261383181 35136378155647973018693)
                ·
                  refine ⟨6588070904183994941005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35136378155647973018693 6588070904183994941005)
                  ·
                    refine ⟨2470526589068998102877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6588070904183994941005 2470526589068998102877)
                    ·
                      rfl

theorem cell22_7217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_7217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7217 prefixEnd_7217 := by exact prefixLift 7217
  have htrace : WordTrace (prefixWord ++ tailWord_7217) baseStart_7217 baseEnd_7217 := by
    simpa [prefixWord, tailWord_7217, baseEnd_7217] using wordTrace_append hprefix tailTrace_7217
  have hstable : (prefixWord ++ tailWord_7217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217).length < 2 ^ (prefixWord ++ tailWord_7217).sum := by decide
  have hdescent : baseEnd_7217 < baseStart_7217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_7238 : Nat := 118140960795 + 7238 * 2 ^ 59
def prefixEnd_7238 : Nat := 4983230072969 + 3 ^ 40 * 7238 * 2
def baseEnd_7238 : Nat := 2477715318231943327813

theorem tailTrace_7238 : CollatzResearch.WordTrace tailWord_7238 prefixEnd_7238 2477715318231943327813 := by
  unfold tailWord_7238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8249735868294906159199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175994365190291331396245 8249735868294906159199)
  ·
    refine ⟨12374603802442359238799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8249735868294906159199 12374603802442359238799)
    ·
      refine ⟨18561905703663538858199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12374603802442359238799 18561905703663538858199)
      ·
        refine ⟨27842858555495308287299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18561905703663538858199 27842858555495308287299)
        ·
          refine ⟨41764287833242962430949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27842858555495308287299 41764287833242962430949)
          ·
            refine ⟨7830803968733055455803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41764287833242962430949 7830803968733055455803)
            ·
              refine ⟨11746205953099583183705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830803968733055455803 11746205953099583183705)
              ·
                refine ⟨8809654464824687387779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11746205953099583183705 8809654464824687387779)
                ·
                  refine ⟨13214481697237031081669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8809654464824687387779 13214481697237031081669)
                  ·
                    refine ⟨2477715318231943327813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13214481697237031081669 2477715318231943327813)
                    ·
                      rfl

theorem cell22_7238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_7238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7238 prefixEnd_7238 := by exact prefixLift 7238
  have htrace : WordTrace (prefixWord ++ tailWord_7238) baseStart_7238 baseEnd_7238 := by
    simpa [prefixWord, tailWord_7238, baseEnd_7238] using wordTrace_append hprefix tailTrace_7238
  have hstable : (prefixWord ++ tailWord_7238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238).length < 2 ^ (prefixWord ++ tailWord_7238).sum := by decide
  have hdescent : baseEnd_7238 < baseStart_7238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_7277 : Nat := 118140960795 + 7277 * 2 ^ 59
def prefixEnd_7277 : Nat := 4983230072969 + 3 ^ 40 * 7277 * 2
def baseEnd_7277 : Nat := 2491065815248841602693

theorem tailTrace_7277 : CollatzResearch.WordTrace tailWord_7277 prefixEnd_7277 2491065815248841602693 := by
  unfold tailWord_7277
  simp only [CollatzResearch.WordTrace]
  refine ⟨265413994644146657764085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176942663096097771842723 265413994644146657764085)
  ·
    refine ⟨24882561997888749165383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265413994644146657764085 24882561997888749165383)
    ·
      refine ⟨37323842996833123748075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24882561997888749165383 37323842996833123748075)
      ·
        refine ⟨55985764495249685622113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37323842996833123748075 55985764495249685622113)
        ·
          refine ⟨41989323371437264216585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55985764495249685622113 41989323371437264216585)
          ·
            refine ⟨31491992528577948162439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41989323371437264216585 31491992528577948162439)
            ·
              refine ⟨47237988792866922243659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31491992528577948162439 47237988792866922243659)
              ·
                refine ⟨70856983189300383365489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47237988792866922243659 70856983189300383365489)
                ·
                  refine ⟨53142737391975287524117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70856983189300383365489 53142737391975287524117)
                  ·
                    refine ⟨2491065815248841602693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53142737391975287524117 2491065815248841602693)
                    ·
                      rfl

theorem cell22_7277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_7277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7277 prefixEnd_7277 := by exact prefixLift 7277
  have htrace : WordTrace (prefixWord ++ tailWord_7277) baseStart_7277 baseEnd_7277 := by
    simpa [prefixWord, tailWord_7277, baseEnd_7277] using wordTrace_append hprefix tailTrace_7277
  have hstable : (prefixWord ++ tailWord_7277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277).length < 2 ^ (prefixWord ++ tailWord_7277).sum := by decide
  have hdescent : baseEnd_7277 < baseStart_7277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 5]
def baseStart_7292 : Nat := 118140960795 + 7292 * 2 ^ 59
def prefixEnd_7292 : Nat := 4983230072969 + 3 ^ 40 * 7292 * 2
def baseEnd_7292 : Nat := 832066873931267492549

theorem tailTrace_7292 : CollatzResearch.WordTrace tailWord_7292 prefixEnd_7292 832066873931267492549 := by
  unfold tailWord_7292
  simp only [CollatzResearch.WordTrace]
  refine ⟨132980544794902109780065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177307393059869479706753 132980544794902109780065)
  ·
    refine ⟨99735408596176582335049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132980544794902109780065 99735408596176582335049)
    ·
      refine ⟨74801556447132436751287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99735408596176582335049 74801556447132436751287)
      ·
        refine ⟨112202334670698655126931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74801556447132436751287 112202334670698655126931)
        ·
          refine ⟨168303502006047982690397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112202334670698655126931 168303502006047982690397)
          ·
            refine ⟨63113813252267993508899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168303502006047982690397 63113813252267993508899)
            ·
              refine ⟨94670719878401990263349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63113813252267993508899 94670719878401990263349)
              ·
                refine ⟨8875379988600186587189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94670719878401990263349 8875379988600186587189)
                ·
                  refine ⟨832066873931267492549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8875379988600186587189 832066873931267492549)
                  ·
                    rfl

theorem cell22_7292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_7292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7292 prefixEnd_7292 := by exact prefixLift 7292
  have htrace : WordTrace (prefixWord ++ tailWord_7292) baseStart_7292 baseEnd_7292 := by
    simpa [prefixWord, tailWord_7292, baseEnd_7292] using wordTrace_append hprefix tailTrace_7292
  have hstable : (prefixWord ++ tailWord_7292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292).length < 2 ^ (prefixWord ++ tailWord_7292).sum := by decide
  have hdescent : baseEnd_7292 < baseStart_7292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7326 : Nat := 118140960795 + 7326 * 2 ^ 59
def prefixEnd_7326 : Nat := 4983230072969 + 3 ^ 40 * 7326 * 2
def baseEnd_7326 : Nat := 835946505543015709181

theorem tailTrace_7326 : CollatzResearch.WordTrace tailWord_7326 prefixEnd_7326 835946505543015709181 := by
  unfold tailWord_7326
  simp only [CollatzResearch.WordTrace]
  refine ⟨33400146433328503287229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178134114311085350865221 33400146433328503287229)
  ·
    refine ⟨12525054912498188732711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33400146433328503287229 12525054912498188732711)
    ·
      refine ⟨18787582368747283099067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12525054912498188732711 18787582368747283099067)
      ·
        refine ⟨28181373553120924648601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18787582368747283099067 28181373553120924648601)
        ·
          refine ⟨21136030164840693486451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28181373553120924648601 21136030164840693486451)
          ·
            refine ⟨31704045247261040229677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21136030164840693486451 31704045247261040229677)
            ·
              refine ⟨11889016967722890086129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31704045247261040229677 11889016967722890086129)
              ·
                refine ⟨8916762725792167564597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11889016967722890086129 8916762725792167564597)
                ·
                  refine ⟨835946505543015709181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8916762725792167564597 835946505543015709181)
                  ·
                    rfl

theorem cell22_7326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7326 prefixEnd_7326 := by exact prefixLift 7326
  have htrace : WordTrace (prefixWord ++ tailWord_7326) baseStart_7326 baseEnd_7326 := by
    simpa [prefixWord, tailWord_7326, baseEnd_7326] using wordTrace_append hprefix tailTrace_7326
  have hstable : (prefixWord ++ tailWord_7326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326).length < 2 ^ (prefixWord ++ tailWord_7326).sum := by decide
  have hdescent : baseEnd_7326 < baseStart_7326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7352 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_7352 : Nat := 118140960795 + 7352 * 2 ^ 59
def prefixEnd_7352 : Nat := 4983230072969 + 3 ^ 40 * 7352 * 2
def baseEnd_7352 : Nat := 2516739847973645977463

theorem tailTrace_7352 : CollatzResearch.WordTrace tailWord_7352 prefixEnd_7352 2516739847973645977463 := by
  unfold tailWord_7352
  simp only [CollatzResearch.WordTrace]
  refine ⟨134074734686217233372155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178766312914956311162873 134074734686217233372155)
  ·
    refine ⟨201112102029325850058233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134074734686217233372155 201112102029325850058233)
    ·
      refine ⟨150834076521994387543675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201112102029325850058233 150834076521994387543675)
      ·
        refine ⟨226251114782991581315513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150834076521994387543675 226251114782991581315513)
        ·
          refine ⟨169688336087243685986635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226251114782991581315513 169688336087243685986635)
          ·
            refine ⟨254532504130865528979953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169688336087243685986635 254532504130865528979953)
            ·
              refine ⟨190899378098149146734965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254532504130865528979953 190899378098149146734965)
              ·
                refine ⟨17896816696701482506403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190899378098149146734965 17896816696701482506403)
                ·
                  refine ⟨26845225045052223759605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17896816696701482506403 26845225045052223759605)
                  ·
                    refine ⟨2516739847973645977463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26845225045052223759605 2516739847973645977463)
                    ·
                      rfl

theorem cell22_7352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_7352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7352 prefixEnd_7352 := by exact prefixLift 7352
  have htrace : WordTrace (prefixWord ++ tailWord_7352) baseStart_7352 baseEnd_7352 := by
    simpa [prefixWord, tailWord_7352, baseEnd_7352] using wordTrace_append hprefix tailTrace_7352
  have hstable : (prefixWord ++ tailWord_7352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7352).length < 2 ^ (prefixWord ++ tailWord_7352).sum := by decide
  have hdescent : baseEnd_7352 < baseStart_7352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7356 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_7356 : Nat := 118140960795 + 7356 * 2 ^ 59
def prefixEnd_7356 : Nat := 4983230072969 + 3 ^ 40 * 7356 * 2
def baseEnd_7356 : Nat := 2518109129718968877451

theorem tailTrace_7356 : CollatzResearch.WordTrace tailWord_7356 prefixEnd_7356 2518109129718968877451 := by
  unfold tailWord_7356
  simp only [CollatzResearch.WordTrace]
  refine ⟨134147680678971574944961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178863574238628766593281 134147680678971574944961)
  ·
    refine ⟨100610760509228681208721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134147680678971574944961 100610760509228681208721)
    ·
      refine ⟨75458070381921510906541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100610760509228681208721 75458070381921510906541)
      ·
        refine ⟨28296776393220566589953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75458070381921510906541 28296776393220566589953)
        ·
          refine ⟨21222582294915424942465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28296776393220566589953 21222582294915424942465)
          ·
            refine ⟨15916936721186568706849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21222582294915424942465 15916936721186568706849)
            ·
              refine ⟨11937702540889926530137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15916936721186568706849 11937702540889926530137)
              ·
                refine ⟨8953276905667444897603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11937702540889926530137 8953276905667444897603)
                ·
                  refine ⟨13429915358501167346405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8953276905667444897603 13429915358501167346405)
                  ·
                    refine ⟨2518109129718968877451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13429915358501167346405 2518109129718968877451)
                    ·
                      rfl

theorem cell22_7356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_7356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7356 prefixEnd_7356 := by exact prefixLift 7356
  have htrace : WordTrace (prefixWord ++ tailWord_7356) baseStart_7356 baseEnd_7356 := by
    simpa [prefixWord, tailWord_7356, baseEnd_7356] using wordTrace_append hprefix tailTrace_7356
  have hstable : (prefixWord ++ tailWord_7356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7356).length < 2 ^ (prefixWord ++ tailWord_7356).sum := by decide
  have hdescent : baseEnd_7356 < baseStart_7356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 6, 4]
def baseStart_7367 : Nat := 118140960795 + 7367 * 2 ^ 59
def prefixEnd_7367 : Nat := 4983230072969 + 3 ^ 40 * 7367 * 2
def baseEnd_7367 : Nat := 2521874654518606852417

theorem tailTrace_7367 : CollatzResearch.WordTrace tailWord_7367 prefixEnd_7367 2521874654518606852417 := by
  unfold tailWord_7367
  simp only [CollatzResearch.WordTrace]
  refine ⟨268696564318092028540355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179131042878728019026903 268696564318092028540355)
  ·
    refine ⟨403044846477138042810533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268696564318092028540355 403044846477138042810533)
    ·
      refine ⟨75570908714463383026975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403044846477138042810533 75570908714463383026975)
      ·
        refine ⟨113356363071695074540463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75570908714463383026975 113356363071695074540463)
        ·
          refine ⟨170034544607542611810695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113356363071695074540463 170034544607542611810695)
          ·
            refine ⟨255051816911313917716043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170034544607542611810695 255051816911313917716043)
            ·
              refine ⟨382577725366970876574065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255051816911313917716043 382577725366970876574065)
              ·
                refine ⟨286933294025228157430549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382577725366970876574065 286933294025228157430549)
                ·
                  refine ⟨13449998157432569879557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 286933294025228157430549 13449998157432569879557)
                  ·
                    refine ⟨2521874654518606852417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13449998157432569879557 2521874654518606852417)
                    ·
                      rfl

theorem cell22_7367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_7367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7367 prefixEnd_7367 := by exact prefixLift 7367
  have htrace : WordTrace (prefixWord ++ tailWord_7367) baseStart_7367 baseEnd_7367 := by
    simpa [prefixWord, tailWord_7367, baseEnd_7367] using wordTrace_append hprefix tailTrace_7367
  have hstable : (prefixWord ++ tailWord_7367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367).length < 2 ^ (prefixWord ++ tailWord_7367).sum := by decide
  have hdescent : baseEnd_7367 < baseStart_7367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 2, 3]
def baseStart_7403 : Nat := 118140960795 + 7403 * 2 ^ 59
def prefixEnd_7403 : Nat := 4983230072969 + 3 ^ 40 * 7403 * 2
def baseEnd_7403 : Nat := 2534198190226512952307

theorem tailTrace_7403 : CollatzResearch.WordTrace tailWord_7403 prefixEnd_7403 2534198190226512952307 := by
  unfold tailWord_7403
  simp only [CollatzResearch.WordTrace]
  refine ⟨270009592187670176850863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180006394791780117900575 270009592187670176850863)
  ·
    refine ⟨405014388281505265276295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270009592187670176850863 405014388281505265276295)
    ·
      refine ⟨607521582422257897914443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405014388281505265276295 607521582422257897914443)
      ·
        refine ⟨911282373633386846871665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607521582422257897914443 911282373633386846871665)
        ·
          refine ⟨683461780225040135153749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911282373633386846871665 683461780225040135153749)
          ·
            refine ⟨8009317737012189083833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 683461780225040135153749 8009317737012189083833)
            ·
              refine ⟨6006988302759141812875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8009317737012189083833 6006988302759141812875)
              ·
                refine ⟨9010482454138712719313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006988302759141812875 9010482454138712719313)
                ·
                  refine ⟨6757861840604034539485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9010482454138712719313 6757861840604034539485)
                  ·
                    refine ⟨2534198190226512952307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6757861840604034539485 2534198190226512952307)
                    ·
                      rfl

theorem cell22_7403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 3].length) (baseStart_7403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7403 prefixEnd_7403 := by exact prefixLift 7403
  have htrace : WordTrace (prefixWord ++ tailWord_7403) baseStart_7403 baseEnd_7403 := by
    simpa [prefixWord, tailWord_7403, baseEnd_7403] using wordTrace_append hprefix tailTrace_7403
  have hstable : (prefixWord ++ tailWord_7403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403).length < 2 ^ (prefixWord ++ tailWord_7403).sum := by decide
  have hdescent : baseEnd_7403 < baseStart_7403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448 : List Nat := [2, 1, 2, 3, 1, 4, 1, 4, 1, 3]
def baseStart_7448 : Nat := 118140960795 + 7448 * 2 ^ 59
def prefixEnd_7448 : Nat := 4983230072969 + 3 ^ 40 * 7448 * 2
def baseEnd_7448 : Nat := 2549602609861395577169

theorem tailTrace_7448 : CollatzResearch.WordTrace tailWord_7448 prefixEnd_7448 2549602609861395577169 := by
  unfold tailWord_7448
  simp only [CollatzResearch.WordTrace]
  refine ⟨135825438512321431119499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181100584683095241492665 135825438512321431119499)
  ·
    refine ⟨203738157768482146679249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135825438512321431119499 203738157768482146679249)
    ·
      refine ⟨152803618326361610009437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203738157768482146679249 152803618326361610009437)
      ·
        refine ⟨57301356872385603753539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152803618326361610009437 57301356872385603753539)
        ·
          refine ⟨85952035308578405630309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57301356872385603753539 85952035308578405630309)
          ·
            refine ⟨16116006620358451055683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85952035308578405630309 16116006620358451055683)
            ·
              refine ⟨24174009930537676583525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16116006620358451055683 24174009930537676583525)
              ·
                refine ⟨4532626861975814359411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24174009930537676583525 4532626861975814359411)
                ·
                  refine ⟨6798940292963721539117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532626861975814359411 6798940292963721539117)
                  ·
                    refine ⟨2549602609861395577169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6798940292963721539117 2549602609861395577169)
                    ·
                      rfl

theorem cell22_7448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_7448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7448 prefixEnd_7448 := by exact prefixLift 7448
  have htrace : WordTrace (prefixWord ++ tailWord_7448) baseStart_7448 baseEnd_7448 := by
    simpa [prefixWord, tailWord_7448, baseEnd_7448] using wordTrace_append hprefix tailTrace_7448
  have hstable : (prefixWord ++ tailWord_7448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448).length < 2 ^ (prefixWord ++ tailWord_7448).sum := by decide
  have hdescent : baseEnd_7448 < baseStart_7448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7459 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 2, 5]
def baseStart_7459 : Nat := 118140960795 + 7459 * 2 ^ 59
def prefixEnd_7459 : Nat := 4983230072969 + 3 ^ 40 * 7459 * 2
def baseEnd_7459 : Nat := 2553368134661033552135

theorem tailTrace_7459 : CollatzResearch.WordTrace tailWord_7459 prefixEnd_7459 2553368134661033552135 := by
  unfold tailWord_7459
  simp only [CollatzResearch.WordTrace]
  refine ⟨272052079984791740889431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181368053323194493926287 272052079984791740889431)
  ·
    refine ⟨408078119977187611334147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272052079984791740889431 408078119977187611334147)
    ·
      refine ⟨612117179965781417001221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408078119977187611334147 612117179965781417001221)
      ·
        refine ⟨114771971243584015687729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 612117179965781417001221 114771971243584015687729)
        ·
          refine ⟨86078978432688011765797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114771971243584015687729 86078978432688011765797)
          ·
            refine ⟨16139808456129002206087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86078978432688011765797 16139808456129002206087)
            ·
              refine ⟨24209712684193503309131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16139808456129002206087 24209712684193503309131)
              ·
                refine ⟨36314569026290254963697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24209712684193503309131 36314569026290254963697)
                ·
                  refine ⟨27235926769717691222773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36314569026290254963697 27235926769717691222773)
                  ·
                    refine ⟨2553368134661033552135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27235926769717691222773 2553368134661033552135)
                    ·
                      rfl

theorem cell22_7459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_7459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7459 prefixEnd_7459 := by exact prefixLift 7459
  have htrace : WordTrace (prefixWord ++ tailWord_7459) baseStart_7459 baseEnd_7459 := by
    simpa [prefixWord, tailWord_7459, baseEnd_7459] using wordTrace_append hprefix tailTrace_7459
  have hstable : (prefixWord ++ tailWord_7459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7459).length < 2 ^ (prefixWord ++ tailWord_7459).sum := by decide
  have hdescent : baseEnd_7459 < baseStart_7459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 2, 3]
def baseStart_7521 : Nat := 118140960795 + 7521 * 2 ^ 59
def prefixEnd_7521 : Nat := 4983230072969 + 3 ^ 40 * 7521 * 2
def baseEnd_7521 : Nat := 2574592001713538501945

theorem tailTrace_7521 : CollatzResearch.WordTrace tailWord_7521 prefixEnd_7521 2574592001713538501945 := by
  unfold tailWord_7521
  simp only [CollatzResearch.WordTrace]
  refine ⟨274313405760176329646417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182875603840117553097611 274313405760176329646417)
  ·
    refine ⟨205735054320132247234813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274313405760176329646417 205735054320132247234813)
    ·
      refine ⟨77150645370049592713055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205735054320132247234813 77150645370049592713055)
      ·
        refine ⟨115725968055074389069583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77150645370049592713055 115725968055074389069583)
        ·
          refine ⟨173588952082611583604375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115725968055074389069583 173588952082611583604375)
          ·
            refine ⟨260383428123917375406563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173588952082611583604375 260383428123917375406563)
            ·
              refine ⟨390575142185876063109845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260383428123917375406563 390575142185876063109845)
              ·
                refine ⟨9154104894981470229137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 390575142185876063109845 9154104894981470229137)
                ·
                  refine ⟨6865578671236102671853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9154104894981470229137 6865578671236102671853)
                  ·
                    refine ⟨2574592001713538501945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6865578671236102671853 2574592001713538501945)
                    ·
                      rfl

theorem cell22_7521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_7521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7521 prefixEnd_7521 := by exact prefixLift 7521
  have htrace : WordTrace (prefixWord ++ tailWord_7521) baseStart_7521 baseEnd_7521 := by
    simpa [prefixWord, tailWord_7521, baseEnd_7521] using wordTrace_append hprefix tailTrace_7521
  have hstable : (prefixWord ++ tailWord_7521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521).length < 2 ^ (prefixWord ++ tailWord_7521).sum := by decide
  have hdescent : baseEnd_7521 < baseStart_7521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_7553 : Nat := 118140960795 + 7553 * 2 ^ 59
def prefixEnd_7553 : Nat := 4983230072969 + 3 ^ 40 * 7553 * 2
def baseEnd_7553 : Nat := 2585546255676121701847

theorem tailTrace_7553 : CollatzResearch.WordTrace tailWord_7553 prefixEnd_7553 2585546255676121701847 := by
  unfold tailWord_7553
  simp only [CollatzResearch.WordTrace]
  refine ⟨275480541644245794811313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183653694429497196540875 275480541644245794811313)
  ·
    refine ⟨206610406233184346108485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275480541644245794811313 206610406233184346108485)
    ·
      refine ⟨38739451168722064895341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206610406233184346108485 38739451168722064895341)
      ·
        refine ⟨14527294188270774335753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38739451168722064895341 14527294188270774335753)
        ·
          refine ⟨10895470641203080751815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14527294188270774335753 10895470641203080751815)
          ·
            refine ⟨16343205961804621127723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895470641203080751815 16343205961804621127723)
            ·
              refine ⟨24514808942706931691585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16343205961804621127723 24514808942706931691585)
              ·
                refine ⟨18386106707030198768689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24514808942706931691585 18386106707030198768689)
                ·
                  refine ⟨13789580030272649076517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18386106707030198768689 13789580030272649076517)
                  ·
                    refine ⟨2585546255676121701847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13789580030272649076517 2585546255676121701847)
                    ·
                      rfl

theorem cell22_7553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_7553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7553 prefixEnd_7553 := by exact prefixLift 7553
  have htrace : WordTrace (prefixWord ++ tailWord_7553) baseStart_7553 baseEnd_7553 := by
    simpa [prefixWord, tailWord_7553, baseEnd_7553] using wordTrace_append hprefix tailTrace_7553
  have hstable : (prefixWord ++ tailWord_7553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553).length < 2 ^ (prefixWord ++ tailWord_7553).sum := by decide
  have hdescent : baseEnd_7553 < baseStart_7553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7564 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_7564 : Nat := 118140960795 + 7564 * 2 ^ 59
def prefixEnd_7564 : Nat := 4983230072969 + 3 ^ 40 * 7564 * 2
def baseEnd_7564 : Nat := 2589311780475759676813

theorem tailTrace_7564 : CollatzResearch.WordTrace tailWord_7564 prefixEnd_7564 2589311780475759676813 := by
  unfold tailWord_7564
  simp only [CollatzResearch.WordTrace]
  refine ⟨137940872302197336730873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183921163069596448974497 137940872302197336730873)
  ·
    refine ⟨103455654226648002548155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137940872302197336730873 103455654226648002548155)
    ·
      refine ⟨155183481339972003822233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103455654226648002548155 155183481339972003822233)
      ·
        refine ⟨116387611004979002866675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155183481339972003822233 116387611004979002866675)
        ·
          refine ⟨174581416507468504300013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116387611004979002866675 174581416507468504300013)
          ·
            refine ⟨65468031190300689112505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174581416507468504300013 65468031190300689112505)
            ·
              refine ⟨49101023392725516834379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65468031190300689112505 49101023392725516834379)
              ·
                refine ⟨73651535089088275251569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49101023392725516834379 73651535089088275251569)
                ·
                  refine ⟨55238651316816206438677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73651535089088275251569 55238651316816206438677)
                  ·
                    refine ⟨2589311780475759676813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55238651316816206438677 2589311780475759676813)
                    ·
                      rfl

theorem cell22_7564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_7564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7564 prefixEnd_7564 := by exact prefixLift 7564
  have htrace : WordTrace (prefixWord ++ tailWord_7564) baseStart_7564 baseEnd_7564 := by
    simpa [prefixWord, tailWord_7564, baseEnd_7564] using wordTrace_append hprefix tailTrace_7564
  have hstable : (prefixWord ++ tailWord_7564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7564).length < 2 ^ (prefixWord ++ tailWord_7564).sum := by decide
  have hdescent : baseEnd_7564 < baseStart_7564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_7572 : Nat := 118140960795 + 7572 * 2 ^ 59
def prefixEnd_7572 : Nat := 4983230072969 + 3 ^ 40 * 7572 * 2
def baseEnd_7572 : Nat := 2592050343966405476789

theorem tailTrace_7572 : CollatzResearch.WordTrace tailWord_7572 prefixEnd_7572 2592050343966405476789 := by
  unfold tailWord_7572
  simp only [CollatzResearch.WordTrace]
  refine ⟨138086764287706019876485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184115685716941359835313 138086764287706019876485)
  ·
    refine ⟨25891268303944878726841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138086764287706019876485 25891268303944878726841)
    ·
      refine ⟨19418451227958659045131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25891268303944878726841 19418451227958659045131)
      ·
        refine ⟨29127676841937988567697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19418451227958659045131 29127676841937988567697)
        ·
          refine ⟨21845757631453491425773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29127676841937988567697 21845757631453491425773)
          ·
            refine ⟨8192159111795059284665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21845757631453491425773 8192159111795059284665)
            ·
              refine ⟨6144119333846294463499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8192159111795059284665 6144119333846294463499)
              ·
                refine ⟨9216179000769441695249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144119333846294463499 9216179000769441695249)
                ·
                  refine ⟨6912134250577081271437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216179000769441695249 6912134250577081271437)
                  ·
                    refine ⟨2592050343966405476789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6912134250577081271437 2592050343966405476789)
                    ·
                      rfl

theorem cell22_7572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_7572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7572 prefixEnd_7572 := by exact prefixLift 7572
  have htrace : WordTrace (prefixWord ++ tailWord_7572) baseStart_7572 baseEnd_7572 := by
    simpa [prefixWord, tailWord_7572, baseEnd_7572] using wordTrace_append hprefix tailTrace_7572
  have hstable : (prefixWord ++ tailWord_7572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572).length < 2 ^ (prefixWord ++ tailWord_7572).sum := by decide
  have hdescent : baseEnd_7572 < baseStart_7572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_7626 : Nat := 118140960795 + 7626 * 2 ^ 59
def prefixEnd_7626 : Nat := 4983230072969 + 3 ^ 40 * 7626 * 2
def baseEnd_7626 : Nat := 2610535647528264626623

theorem tailTrace_7626 : CollatzResearch.WordTrace tailWord_7626 prefixEnd_7626 2610535647528264626623 := by
  unfold tailWord_7626
  simp only [CollatzResearch.WordTrace]
  refine ⟨69535767594944815554683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185428713586519508145821 69535767594944815554683)
  ·
    refine ⟨104303651392417223332025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69535767594944815554683 104303651392417223332025)
    ·
      refine ⟨78227738544312917499019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104303651392417223332025 78227738544312917499019)
      ·
        refine ⟨117341607816469376248529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78227738544312917499019 117341607816469376248529)
        ·
          refine ⟨88006205862352032186397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117341607816469376248529 88006205862352032186397)
          ·
            refine ⟨33002327198382012069899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88006205862352032186397 33002327198382012069899)
            ·
              refine ⟨49503490797573018104849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33002327198382012069899 49503490797573018104849)
              ·
                refine ⟨37127618098179763578637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49503490797573018104849 37127618098179763578637)
                ·
                  refine ⟨13922856786817411341989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37127618098179763578637 13922856786817411341989)
                  ·
                    refine ⟨2610535647528264626623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13922856786817411341989 2610535647528264626623)
                    ·
                      rfl

theorem cell22_7626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_7626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7626 prefixEnd_7626 := by exact prefixLift 7626
  have htrace : WordTrace (prefixWord ++ tailWord_7626) baseStart_7626 baseEnd_7626 := by
    simpa [prefixWord, tailWord_7626, baseEnd_7626] using wordTrace_append hprefix tailTrace_7626
  have hstable : (prefixWord ++ tailWord_7626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626).length < 2 ^ (prefixWord ++ tailWord_7626).sum := by decide
  have hdescent : baseEnd_7626 < baseStart_7626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 6]
def baseStart_7641 : Nat := 118140960795 + 7641 * 2 ^ 59
def prefixEnd_7641 : Nat := 4983230072969 + 3 ^ 40 * 7641 * 2
def baseEnd_7641 : Nat := 871890151357741833859

theorem tailTrace_7641 : CollatzResearch.WordTrace tailWord_7641 prefixEnd_7641 871890151357741833859 := by
  unfold tailWord_7641
  simp only [CollatzResearch.WordTrace]
  refine ⟨278690165325436824014777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185793443550291216009851 278690165325436824014777)
  ·
    refine ⟨209017623994077618011083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278690165325436824014777 209017623994077618011083)
    ·
      refine ⟨313526435991116427016625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209017623994077618011083 313526435991116427016625)
      ·
        refine ⟨235144826993337320262469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313526435991116427016625 235144826993337320262469)
        ·
          refine ⟨44089655061250747549213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235144826993337320262469 44089655061250747549213)
          ·
            refine ⟨16533620647969030330955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44089655061250747549213 16533620647969030330955)
            ·
              refine ⟨24800430971953545496433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16533620647969030330955 24800430971953545496433)
              ·
                refine ⟨18600323228965159122325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24800430971953545496433 18600323228965159122325)
                ·
                  refine ⟨871890151357741833859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18600323228965159122325 871890151357741833859)
                  ·
                    rfl

theorem cell22_7641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_7641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7641 prefixEnd_7641 := by exact prefixLift 7641
  have htrace : WordTrace (prefixWord ++ tailWord_7641) baseStart_7641 baseEnd_7641 := by
    simpa [prefixWord, tailWord_7641, baseEnd_7641] using wordTrace_append hprefix tailTrace_7641
  have hstable : (prefixWord ++ tailWord_7641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641).length < 2 ^ (prefixWord ++ tailWord_7641).sum := by decide
  have hdescent : baseEnd_7641 < baseStart_7641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7656 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_7656 : Nat := 118140960795 + 7656 * 2 ^ 59
def prefixEnd_7656 : Nat := 4983230072969 + 3 ^ 40 * 7656 * 2
def baseEnd_7656 : Nat := 2620805260618186376531

theorem tailTrace_7656 : CollatzResearch.WordTrace tailWord_7656 prefixEnd_7656 2620805260618186376531 := by
  unfold tailWord_7656
  simp only [CollatzResearch.WordTrace]
  refine ⟨139618630135547192905411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186158173514062923873881 139618630135547192905411)
  ·
    refine ⟨209427945203320789358117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139618630135547192905411 209427945203320789358117)
    ·
      refine ⟨39267739725622648004647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209427945203320789358117 39267739725622648004647)
      ·
        refine ⟨58901609588433972006971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39267739725622648004647 58901609588433972006971)
        ·
          refine ⟨88352414382650958010457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58901609588433972006971 88352414382650958010457)
          ·
            refine ⟨66264310786988218507843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88352414382650958010457 66264310786988218507843)
            ·
              refine ⟨99396466180482327761765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66264310786988218507843 99396466180482327761765)
              ·
                refine ⟨18636837408840436455331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99396466180482327761765 18636837408840436455331)
                ·
                  refine ⟨27955256113260654682997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18636837408840436455331 27955256113260654682997)
                  ·
                    refine ⟨2620805260618186376531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27955256113260654682997 2620805260618186376531)
                    ·
                      rfl

theorem cell22_7656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_7656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7656 prefixEnd_7656 := by exact prefixLift 7656
  have htrace : WordTrace (prefixWord ++ tailWord_7656) baseStart_7656 baseEnd_7656 := by
    simpa [prefixWord, tailWord_7656, baseEnd_7656] using wordTrace_append hprefix tailTrace_7656
  have hstable : (prefixWord ++ tailWord_7656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7656).length < 2 ^ (prefixWord ++ tailWord_7656).sum := by decide
  have hdescent : baseEnd_7656 < baseStart_7656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720 : List Nat := [2, 1, 5, 2, 3, 1, 8]
def baseStart_7720 : Nat := 118140960795 + 7720 * 2 ^ 59
def prefixEnd_7720 : Nat := 4983230072969 + 3 ^ 40 * 7720 * 2
def baseEnd_7720 : Nat := 97878287723827880605

theorem tailTrace_7720 : CollatzResearch.WordTrace tailWord_7720 prefixEnd_7720 97878287723827880605 := by
  unfold tailWord_7720
  simp only [CollatzResearch.WordTrace]
  refine ⟨140785766019616658070307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187714354692822210760409 140785766019616658070307)
  ·
    refine ⟨211178649029424987105461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140785766019616658070307 211178649029424987105461)
    ·
      refine ⟨19797998346508592541137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211178649029424987105461 19797998346508592541137)
      ·
        refine ⟨14848498759881444405853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19797998346508592541137 14848498759881444405853)
        ·
          refine ⟨5568187034955541652195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14848498759881444405853 5568187034955541652195)
          ·
            refine ⟨8352280552433312478293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568187034955541652195 8352280552433312478293)
            ·
              refine ⟨97878287723827880605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 8352280552433312478293 97878287723827880605)
              ·
                rfl

theorem cell22_7720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 8].length) (baseStart_7720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7720 prefixEnd_7720 := by exact prefixLift 7720
  have htrace : WordTrace (prefixWord ++ tailWord_7720) baseStart_7720 baseEnd_7720 := by
    simpa [prefixWord, tailWord_7720, baseEnd_7720] using wordTrace_append hprefix tailTrace_7720
  have hstable : (prefixWord ++ tailWord_7720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720).length < 2 ^ (prefixWord ++ tailWord_7720).sum := by decide
  have hdescent : baseEnd_7720 < baseStart_7720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 7]
def baseStart_7731 : Nat := 118140960795 + 7731 * 2 ^ 59
def prefixEnd_7731 : Nat := 4983230072969 + 3 ^ 40 * 7731 * 2
def baseEnd_7731 : Nat := 882159764447663583767

theorem tailTrace_7731 : CollatzResearch.WordTrace tailWord_7731 prefixEnd_7731 882159764447663583767 := by
  unfold tailWord_7731
  simp only [CollatzResearch.WordTrace]
  refine ⟨281972734999382194791047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187981823332921463194031 281972734999382194791047)
  ·
    refine ⟨422959102499073292186571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281972734999382194791047 422959102499073292186571)
    ·
      refine ⟨634438653748609938279857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422959102499073292186571 634438653748609938279857)
      ·
        refine ⟨475828990311457453709893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634438653748609938279857 475828990311457453709893)
        ·
          refine ⟨89217935683398272570605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475828990311457453709893 89217935683398272570605)
          ·
            refine ⟨33456725881274352213977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89217935683398272570605 33456725881274352213977)
            ·
              refine ⟨25092544410955764160483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33456725881274352213977 25092544410955764160483)
              ·
                refine ⟨37638816616433646240725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25092544410955764160483 37638816616433646240725)
                ·
                  refine ⟨882159764447663583767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37638816616433646240725 882159764447663583767)
                  ·
                    rfl

theorem cell22_7731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 7].length) (baseStart_7731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7731 prefixEnd_7731 := by exact prefixLift 7731
  have htrace : WordTrace (prefixWord ++ tailWord_7731) baseStart_7731 baseEnd_7731 := by
    simpa [prefixWord, tailWord_7731, baseEnd_7731] using wordTrace_append hprefix tailTrace_7731
  have hstable : (prefixWord ++ tailWord_7731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731).length < 2 ^ (prefixWord ++ tailWord_7731).sum := by decide
  have hdescent : baseEnd_7731 < baseStart_7731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 3, 3]
def baseStart_7735 : Nat := 118140960795 + 7735 * 2 ^ 59
def prefixEnd_7735 : Nat := 4983230072969 + 3 ^ 40 * 7735 * 2
def baseEnd_7735 : Nat := 2647848575088313651289

theorem tailTrace_7735 : CollatzResearch.WordTrace tailWord_7735 prefixEnd_7735 2647848575088313651289 := by
  unfold tailWord_7735
  simp only [CollatzResearch.WordTrace]
  refine ⟨282118626984890877936659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188079084656593918624439 282118626984890877936659)
  ·
    refine ⟨423177940477336316904989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282118626984890877936659 423177940477336316904989)
    ·
      refine ⟨158691727679001118839371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423177940477336316904989 158691727679001118839371)
      ·
        refine ⟨238037591518501678259057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158691727679001118839371 238037591518501678259057)
        ·
          refine ⟨178528193638876258694293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238037591518501678259057 178528193638876258694293)
          ·
            refine ⟨8368509076822324626295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178528193638876258694293 8368509076822324626295)
            ·
              refine ⟨12552763615233486939443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368509076822324626295 12552763615233486939443)
              ·
                refine ⟨18829145422850230409165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12552763615233486939443 18829145422850230409165)
                ·
                  refine ⟨7060929533568836403437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18829145422850230409165 7060929533568836403437)
                  ·
                    refine ⟨2647848575088313651289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7060929533568836403437 2647848575088313651289)
                    ·
                      rfl

theorem cell22_7735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_7735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7735 prefixEnd_7735 := by exact prefixLift 7735
  have htrace : WordTrace (prefixWord ++ tailWord_7735) baseStart_7735 baseEnd_7735 := by
    simpa [prefixWord, tailWord_7735, baseEnd_7735] using wordTrace_append hprefix tailTrace_7735
  have hstable : (prefixWord ++ tailWord_7735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735).length < 2 ^ (prefixWord ++ tailWord_7735).sum := by decide
  have hdescent : baseEnd_7735 < baseStart_7735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7791 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 5, 5]
def baseStart_7791 : Nat := 118140960795 + 7791 * 2 ^ 59
def prefixEnd_7791 : Nat := 4983230072969 + 3 ^ 40 * 7791 * 2
def baseEnd_7791 : Nat := 2667018519522834251117

theorem tailTrace_7791 : CollatzResearch.WordTrace tailWord_7791 prefixEnd_7791 2667018519522834251117 := by
  unfold tailWord_7791
  simp only [CollatzResearch.WordTrace]
  refine ⟨284161114782012441975227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189440743188008294650151 284161114782012441975227)
  ·
    refine ⟨426241672173018662962841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284161114782012441975227 426241672173018662962841)
    ·
      refine ⟨319681254129763997222131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426241672173018662962841 319681254129763997222131)
      ·
        refine ⟨479521881194645995833197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319681254129763997222131 479521881194645995833197)
        ·
          refine ⟨179820705447992248437449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479521881194645995833197 179820705447992248437449)
          ·
            refine ⟨134865529085994186328087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179820705447992248437449 134865529085994186328087)
            ·
              refine ⟨202298293628991279492131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134865529085994186328087 202298293628991279492131)
              ·
                refine ⟨303447440443486919238197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202298293628991279492131 303447440443486919238197)
                ·
                  refine ⟨28448197541576898678581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303447440443486919238197 28448197541576898678581)
                  ·
                    refine ⟨2667018519522834251117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28448197541576898678581 2667018519522834251117)
                    ·
                      rfl

theorem cell22_7791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_7791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7791 prefixEnd_7791 := by exact prefixLift 7791
  have htrace : WordTrace (prefixWord ++ tailWord_7791) baseStart_7791 baseEnd_7791 := by
    simpa [prefixWord, tailWord_7791, baseEnd_7791] using wordTrace_append hprefix tailTrace_7791
  have hstable : (prefixWord ++ tailWord_7791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7791).length < 2 ^ (prefixWord ++ tailWord_7791).sum := by decide
  have hdescent : baseEnd_7791 < baseStart_7791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_7808 : Nat := 118140960795 + 7808 * 2 ^ 59
def prefixEnd_7808 : Nat := 4983230072969 + 3 ^ 40 * 7808 * 2
def baseEnd_7808 : Nat := 2672837966940456576065

theorem tailTrace_7808 : CollatzResearch.WordTrace tailWord_7808 prefixEnd_7808 2672837966940456576065 := by
  unfold tailWord_7808
  simp only [CollatzResearch.WordTrace]
  refine ⟨142390577860212172672039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189854103813616230229385 142390577860212172672039)
  ·
    refine ⟨213585866790318259008059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142390577860212172672039 213585866790318259008059)
    ·
      refine ⟨320378800185477388512089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213585866790318259008059 320378800185477388512089)
      ·
        refine ⟨240284100139108041384067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320378800185477388512089 240284100139108041384067)
        ·
          refine ⟨360426150208662062076101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240284100139108041384067 360426150208662062076101)
          ·
            refine ⟨67579903164124136639269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360426150208662062076101 67579903164124136639269)
            ·
              refine ⟨12671231843273275619863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67579903164124136639269 12671231843273275619863)
              ·
                refine ⟨19006847764909913429795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12671231843273275619863 19006847764909913429795)
                ·
                  refine ⟨28510271647364870144693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19006847764909913429795 28510271647364870144693)
                  ·
                    refine ⟨2672837966940456576065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28510271647364870144693 2672837966940456576065)
                    ·
                      rfl

theorem cell22_7808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_7808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7808 prefixEnd_7808 := by exact prefixLift 7808
  have htrace : WordTrace (prefixWord ++ tailWord_7808) baseStart_7808 baseEnd_7808 := by
    simpa [prefixWord, tailWord_7808, baseEnd_7808] using wordTrace_append hprefix tailTrace_7808
  have hstable : (prefixWord ++ tailWord_7808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808).length < 2 ^ (prefixWord ++ tailWord_7808).sum := by decide
  have hdescent : baseEnd_7808 < baseStart_7808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_7913 : Nat := 118140960795 + 7913 * 2 ^ 59
def prefixEnd_7913 : Nat := 4983230072969 + 3 ^ 40 * 7913 * 2
def baseEnd_7913 : Nat := 2708781612755182700743

theorem tailTrace_7913 : CollatzResearch.WordTrace tailWord_7913 prefixEnd_7913 2708781612755182700743 := by
  unfold tailWord_7913
  simp only [CollatzResearch.WordTrace]
  refine ⟨288610820340027277916393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192407213560018185277595 288610820340027277916393)
  ·
    refine ⟨216458115255020458437295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288610820340027277916393 216458115255020458437295)
    ·
      refine ⟨324687172882530687655943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216458115255020458437295 324687172882530687655943)
      ·
        refine ⟨487030759323796031483915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324687172882530687655943 487030759323796031483915)
        ·
          refine ⟨730546138985694047225873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487030759323796031483915 730546138985694047225873)
          ·
            refine ⟨547909604239270535419405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730546138985694047225873 547909604239270535419405)
            ·
              refine ⟨205466101589726450782277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 547909604239270535419405 205466101589726450782277)
              ·
                refine ⟨38524894048073709521677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205466101589726450782277 38524894048073709521677)
                ·
                  refine ⟨14446835268027641070629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38524894048073709521677 14446835268027641070629)
                  ·
                    refine ⟨2708781612755182700743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14446835268027641070629 2708781612755182700743)
                    ·
                      rfl

theorem cell22_7913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_7913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7913 prefixEnd_7913 := by exact prefixLift 7913
  have htrace : WordTrace (prefixWord ++ tailWord_7913) baseStart_7913 baseEnd_7913 := by
    simpa [prefixWord, tailWord_7913, baseEnd_7913] using wordTrace_append hprefix tailTrace_7913
  have hstable : (prefixWord ++ tailWord_7913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913).length < 2 ^ (prefixWord ++ tailWord_7913).sum := by decide
  have hdescent : baseEnd_7913 < baseStart_7913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 5]
def baseStart_7917 : Nat := 118140960795 + 7917 * 2 ^ 59
def prefixEnd_7917 : Nat := 4983230072969 + 3 ^ 40 * 7917 * 2
def baseEnd_7917 : Nat := 903383631500168533577

theorem tailTrace_7917 : CollatzResearch.WordTrace tailWord_7917 prefixEnd_7917 903383631500168533577 := by
  unfold tailWord_7917
  simp only [CollatzResearch.WordTrace]
  refine ⟨288756712325535961062005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192504474883690640708003 288756712325535961062005)
  ·
    refine ⟨27070941780518996349563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288756712325535961062005 27070941780518996349563)
    ·
      refine ⟨40606412670778494524345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27070941780518996349563 40606412670778494524345)
      ·
        refine ⟨30454809503083870893259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40606412670778494524345 30454809503083870893259)
        ·
          refine ⟨45682214254625806339889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30454809503083870893259 45682214254625806339889)
          ·
            refine ⟨34261660690969354754917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45682214254625806339889 34261660690969354754917)
            ·
              refine ⟨6424061379556754016547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34261660690969354754917 6424061379556754016547)
              ·
                refine ⟨9636092069335131024821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424061379556754016547 9636092069335131024821)
                ·
                  refine ⟨903383631500168533577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9636092069335131024821 903383631500168533577)
                  ·
                    rfl

theorem cell22_7917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_7917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7917 prefixEnd_7917 := by exact prefixLift 7917
  have htrace : WordTrace (prefixWord ++ tailWord_7917) baseStart_7917 baseEnd_7917 := by
    simpa [prefixWord, tailWord_7917, baseEnd_7917] using wordTrace_append hprefix tailTrace_7917
  have hstable : (prefixWord ++ tailWord_7917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917).length < 2 ^ (prefixWord ++ tailWord_7917).sum := by decide
  have hdescent : baseEnd_7917 < baseStart_7917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7945 : List Nat := [1, 2, 1, 1, 3, 2, 1, 7, 4]
def baseStart_7945 : Nat := 118140960795 + 7945 * 2 ^ 59
def prefixEnd_7945 : Nat := 4983230072969 + 3 ^ 40 * 7945 * 2
def baseEnd_7945 : Nat := 906578622239255300215

theorem tailTrace_7945 : CollatzResearch.WordTrace tailWord_7945 prefixEnd_7945 906578622239255300215 := by
  unfold tailWord_7945
  simp only [CollatzResearch.WordTrace]
  refine ⟨289777956224096743081289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193185304149397828720859 289777956224096743081289)
  ·
    refine ⟨217333467168072557310967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289777956224096743081289 217333467168072557310967)
    ·
      refine ⟨326000200752108835966451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217333467168072557310967 326000200752108835966451)
      ·
        refine ⟨489000301128163253949677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326000200752108835966451 489000301128163253949677)
        ·
          refine ⟨183375112923061220231129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489000301128163253949677 183375112923061220231129)
          ·
            refine ⟨137531334692295915173347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183375112923061220231129 137531334692295915173347)
            ·
              refine ⟨206297002038443872760021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137531334692295915173347 206297002038443872760021)
              ·
                refine ⟨4835085985276028267813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206297002038443872760021 4835085985276028267813)
                ·
                  refine ⟨906578622239255300215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4835085985276028267813 906578622239255300215)
                  ·
                    rfl

theorem cell22_7945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_7945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7945 prefixEnd_7945 := by exact prefixLift 7945
  have htrace : WordTrace (prefixWord ++ tailWord_7945) baseStart_7945 baseEnd_7945 := by
    simpa [prefixWord, tailWord_7945, baseEnd_7945] using wordTrace_append hprefix tailTrace_7945
  have hstable : (prefixWord ++ tailWord_7945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7945).length < 2 ^ (prefixWord ++ tailWord_7945).sum := by decide
  have hdescent : baseEnd_7945 < baseStart_7945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 4, 3]
def baseStart_7960 : Nat := 118140960795 + 7960 * 2 ^ 59
def prefixEnd_7960 : Nat := 4983230072969 + 3 ^ 40 * 7960 * 2
def baseEnd_7960 : Nat := 2724870673262726775599

theorem tailTrace_7960 : CollatzResearch.WordTrace tailWord_7960 prefixEnd_7960 2724870673262726775599 := by
  unfold tailWord_7960
  simp only [CollatzResearch.WordTrace]
  refine ⟨145162525584877152438667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193550034113169536584889 145162525584877152438667)
  ·
    refine ⟨217743788377315728658001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145162525584877152438667 217743788377315728658001)
    ·
      refine ⟨163307841282986796493501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217743788377315728658001 163307841282986796493501)
      ·
        refine ⟨61240440481120048685063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163307841282986796493501 61240440481120048685063)
        ·
          refine ⟨91860660721680073027595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61240440481120048685063 91860660721680073027595)
          ·
            refine ⟨137790991082520109541393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91860660721680073027595 137790991082520109541393)
            ·
              refine ⟨103343243311890082156045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137790991082520109541393 103343243311890082156045)
              ·
                refine ⟨38753716241958780808517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103343243311890082156045 38753716241958780808517)
                ·
                  refine ⟨7266321795367271401597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38753716241958780808517 7266321795367271401597)
                  ·
                    refine ⟨2724870673262726775599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7266321795367271401597 2724870673262726775599)
                    ·
                      rfl

theorem cell22_7960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_7960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7960 prefixEnd_7960 := by exact prefixLift 7960
  have htrace : WordTrace (prefixWord ++ tailWord_7960) baseStart_7960 baseEnd_7960 := by
    simpa [prefixWord, tailWord_7960, baseEnd_7960] using wordTrace_append hprefix tailTrace_7960
  have hstable : (prefixWord ++ tailWord_7960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960).length < 2 ^ (prefixWord ++ tailWord_7960).sum := by decide
  have hdescent : baseEnd_7960 < baseStart_7960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962 : List Nat := [3, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_7962 : Nat := 118140960795 + 7962 * 2 ^ 59
def prefixEnd_7962 : Nat := 4983230072969 + 3 ^ 40 * 7962 * 2
def baseEnd_7962 : Nat := 908518438045129408531

theorem tailTrace_7962 : CollatzResearch.WordTrace tailWord_7962 prefixEnd_7962 908518438045129408531 := by
  unfold tailWord_7962
  simp only [CollatzResearch.WordTrace]
  refine ⟨72599499290627161612535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193598664775005764300093 72599499290627161612535)
  ·
    refine ⟨108899248935940742418803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72599499290627161612535 108899248935940742418803)
    ·
      refine ⟨163348873403911113628205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108899248935940742418803 163348873403911113628205)
      ·
        refine ⟨61255827526466667610577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163348873403911113628205 61255827526466667610577)
        ·
          refine ⟨45941870644850000707933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61255827526466667610577 45941870644850000707933)
          ·
            refine ⟨17228201491818750265475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45941870644850000707933 17228201491818750265475)
            ·
              refine ⟨25842302237728125398213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17228201491818750265475 25842302237728125398213)
              ·
                refine ⟨4845431669574023512165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25842302237728125398213 4845431669574023512165)
                ·
                  refine ⟨908518438045129408531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4845431669574023512165 908518438045129408531)
                  ·
                    rfl

theorem cell22_7962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_7962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7962 prefixEnd_7962 := by exact prefixLift 7962
  have htrace : WordTrace (prefixWord ++ tailWord_7962) baseStart_7962 baseEnd_7962 := by
    simpa [prefixWord, tailWord_7962, baseEnd_7962] using wordTrace_append hprefix tailTrace_7962
  have hstable : (prefixWord ++ tailWord_7962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962).length < 2 ^ (prefixWord ++ tailWord_7962).sum := by decide
  have hdescent : baseEnd_7962 < baseStart_7962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 2, 4]
def baseStart_7992 : Nat := 118140960795 + 7992 * 2 ^ 59
def prefixEnd_7992 : Nat := 4983230072969 + 3 ^ 40 * 7992 * 2
def baseEnd_7992 : Nat := 2735824927225309975501

theorem tailTrace_7992 : CollatzResearch.WordTrace tailWord_7992 prefixEnd_7992 2735824927225309975501 := by
  unfold tailWord_7992
  simp only [CollatzResearch.WordTrace]
  refine ⟨145746093526911885021115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194328124702549180028153 145746093526911885021115)
  ·
    refine ⟨218619140290367827531673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145746093526911885021115 218619140290367827531673)
    ·
      refine ⟨163964355217775870648755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218619140290367827531673 163964355217775870648755)
      ·
        refine ⟨245946532826663805973133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163964355217775870648755 245946532826663805973133)
        ·
          refine ⟨92229949809998927239925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245946532826663805973133 92229949809998927239925)
          ·
            refine ⟨8646557794687399428743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92229949809998927239925 8646557794687399428743)
            ·
              refine ⟨12969836692031099143115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646557794687399428743 12969836692031099143115)
              ·
                refine ⟨19454755038046648714673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12969836692031099143115 19454755038046648714673)
                ·
                  refine ⟨14591066278534986536005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19454755038046648714673 14591066278534986536005)
                  ·
                    refine ⟨2735824927225309975501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14591066278534986536005 2735824927225309975501)
                    ·
                      rfl

theorem cell22_7992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_7992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_7992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_7992 prefixEnd_7992 := by exact prefixLift 7992
  have htrace : WordTrace (prefixWord ++ tailWord_7992) baseStart_7992 baseEnd_7992 := by
    simpa [prefixWord, tailWord_7992, baseEnd_7992] using wordTrace_append hprefix tailTrace_7992
  have hstable : (prefixWord ++ tailWord_7992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992).length < 2 ^ (prefixWord ++ tailWord_7992).sum := by decide
  have hdescent : baseEnd_7992 < baseStart_7992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_8005 : Nat := 118140960795 + 8005 * 2 ^ 59
def prefixEnd_8005 : Nat := 4983230072969 + 3 ^ 40 * 8005 * 2
def baseEnd_8005 : Nat := 2740275092897609400461

theorem tailTrace_8005 : CollatzResearch.WordTrace tailWord_8005 prefixEnd_8005 2740275092897609400461 := by
  unfold tailWord_8005
  simp only [CollatzResearch.WordTrace]
  refine ⟨291966336006726990265469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194644224004484660176979 291966336006726990265469)
  ·
    refine ⟨109487376002522621349551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291966336006726990265469 109487376002522621349551)
    ·
      refine ⟨164231064003783932024327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109487376002522621349551 164231064003783932024327)
      ·
        refine ⟨246346596005675898036491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164231064003783932024327 246346596005675898036491)
        ·
          refine ⟨369519894008513847054737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246346596005675898036491 369519894008513847054737)
          ·
            refine ⟨277139920506385385291053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369519894008513847054737 277139920506385385291053)
            ·
              refine ⟨103927470189894519484145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277139920506385385291053 103927470189894519484145)
              ·
                refine ⟨77945602642420889613109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103927470189894519484145 77945602642420889613109)
                ·
                  refine ⟨7307400247726958401229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77945602642420889613109 7307400247726958401229)
                  ·
                    refine ⟨2740275092897609400461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7307400247726958401229 2740275092897609400461)
                    ·
                      rfl

theorem cell22_8005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_8005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8005 prefixEnd_8005 := by exact prefixLift 8005
  have htrace : WordTrace (prefixWord ++ tailWord_8005) baseStart_8005 baseEnd_8005 := by
    simpa [prefixWord, tailWord_8005, baseEnd_8005] using wordTrace_append hprefix tailTrace_8005
  have hstable : (prefixWord ++ tailWord_8005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005).length < 2 ^ (prefixWord ++ tailWord_8005).sum := by decide
  have hdescent : baseEnd_8005 < baseStart_8005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125 : List Nat := [1, 4, 1, 2, 3, 11]
def baseStart_8125 : Nat := 118140960795 + 8125 * 2 ^ 59
def prefixEnd_8125 : Nat := 4983230072969 + 3 ^ 40 * 8125 * 2
def baseEnd_8125 : Nat := 34337698089596251853

theorem tailTrace_8125 : CollatzResearch.WordTrace tailWord_8125 prefixEnd_8125 34337698089596251853 := by
  unfold tailWord_8125
  simp only [CollatzResearch.WordTrace]
  refine ⟨296343095571987484633829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197562063714658323089219 296343095571987484633829)
  ·
    refine ⟨55564330419747653368843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296343095571987484633829 55564330419747653368843)
    ·
      refine ⟨83346495629621480053265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55564330419747653368843 83346495629621480053265)
      ·
        refine ⟨62509871722216110039949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83346495629621480053265 62509871722216110039949)
        ·
          refine ⟨23441201895831041264981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62509871722216110039949 23441201895831041264981)
          ·
            refine ⟨34337698089596251853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 23441201895831041264981 34337698089596251853)
            ·
              rfl

theorem cell22_8125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 11].length) (baseStart_8125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8125 prefixEnd_8125 := by exact prefixLift 8125
  have htrace : WordTrace (prefixWord ++ tailWord_8125) baseStart_8125 baseEnd_8125 := by
    simpa [prefixWord, tailWord_8125, baseEnd_8125] using wordTrace_append hprefix tailTrace_8125
  have hstable : (prefixWord ++ tailWord_8125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125).length < 2 ^ (prefixWord ++ tailWord_8125).sum := by decide
  have hdescent : baseEnd_8125 < baseStart_8125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 5]
def baseStart_8187 : Nat := 118140960795 + 8187 * 2 ^ 59
def prefixEnd_8187 : Nat := 4983230072969 + 3 ^ 40 * 8187 * 2
def baseEnd_8187 : Nat := 934192470769933783301

theorem tailTrace_8187 : CollatzResearch.WordTrace tailWord_8187 prefixEnd_8187 934192470769933783301 := by
  unfold tailWord_8187
  simp only [CollatzResearch.WordTrace]
  refine ⟨298604421347372073390815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199069614231581382260543 298604421347372073390815)
  ·
    refine ⟨447906632021058110086223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298604421347372073390815 447906632021058110086223)
    ·
      refine ⟨671859948031587165129335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447906632021058110086223 671859948031587165129335)
      ·
        refine ⟨1007789922047380747694003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671859948031587165129335 1007789922047380747694003)
        ·
          refine ⟨1511684883071071121541005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007789922047380747694003 1511684883071071121541005)
          ·
            refine ⟨566881831151651670577877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1511684883071071121541005 566881831151651670577877)
            ·
              refine ⟨13286292917616836029169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 566881831151651670577877 13286292917616836029169)
              ·
                refine ⟨9964719688212627021877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13286292917616836029169 9964719688212627021877)
                ·
                  refine ⟨934192470769933783301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9964719688212627021877 934192470769933783301)
                  ·
                    rfl

theorem cell22_8187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 5].length) (baseStart_8187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8187 prefixEnd_8187 := by exact prefixLift 8187
  have htrace : WordTrace (prefixWord ++ tailWord_8187) baseStart_8187 baseEnd_8187 := by
    simpa [prefixWord, tailWord_8187, baseEnd_8187] using wordTrace_append hprefix tailTrace_8187
  have hstable : (prefixWord ++ tailWord_8187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187).length < 2 ^ (prefixWord ++ tailWord_8187).sum := by decide
  have hdescent : baseEnd_8187 < baseStart_8187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8204 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 5]
def baseStart_8204 : Nat := 118140960795 + 8204 * 2 ^ 59
def prefixEnd_8204 : Nat := 4983230072969 + 3 ^ 40 * 8204 * 2
def baseEnd_8204 : Nat := 936132286575807891617

theorem tailTrace_8204 : CollatzResearch.WordTrace tailWord_8204 prefixEnd_8204 936132286575807891617 := by
  unfold tailWord_8204
  simp only [CollatzResearch.WordTrace]
  refine ⟨149612231142891988379833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199482974857189317839777 149612231142891988379833)
  ·
    refine ⟨112209173357168991284875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149612231142891988379833 112209173357168991284875)
    ·
      refine ⟨168313760035753486927313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112209173357168991284875 168313760035753486927313)
      ·
        refine ⟨126235320026815115195485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168313760035753486927313 126235320026815115195485)
        ·
          refine ⟨47338245010055668198307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126235320026815115195485 47338245010055668198307)
          ·
            refine ⟨71007367515083502297461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47338245010055668198307 71007367515083502297461)
            ·
              refine ⟨6656940704539078340387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71007367515083502297461 6656940704539078340387)
              ·
                refine ⟨9985411056808617510581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656940704539078340387 9985411056808617510581)
                ·
                  refine ⟨936132286575807891617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9985411056808617510581 936132286575807891617)
                  ·
                    rfl

theorem cell22_8204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_8204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8204 prefixEnd_8204 := by exact prefixLift 8204
  have htrace : WordTrace (prefixWord ++ tailWord_8204) baseStart_8204 baseEnd_8204 := by
    simpa [prefixWord, tailWord_8204, baseEnd_8204] using wordTrace_append hprefix tailTrace_8204
  have hstable : (prefixWord ++ tailWord_8204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8204).length < 2 ^ (prefixWord ++ tailWord_8204).sum := by decide
  have hdescent : baseEnd_8204 < baseStart_8204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225 : List Nat := [1, 2, 3, 2, 5, 1, 1, 3, 1, 3]
def baseStart_8225 : Nat := 118140960795 + 8225 * 2 ^ 59
def prefixEnd_8225 : Nat := 4983230072969 + 3 ^ 40 * 8225 * 2
def baseEnd_8225 : Nat := 2815585588890368899787

theorem tailTrace_8225 : CollatzResearch.WordTrace tailWord_8225 prefixEnd_8225 2815585588890368899787 := by
  unfold tailWord_8225
  simp only [CollatzResearch.WordTrace]
  refine ⟨299990395209704563274129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199993596806469708849419 299990395209704563274129)
  ·
    refine ⟨224992796407278422455597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299990395209704563274129 224992796407278422455597)
    ·
      refine ⟨84372298652729408420849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224992796407278422455597 84372298652729408420849)
      ·
        refine ⟨63279223989547056315637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84372298652729408420849 63279223989547056315637)
        ·
          refine ⟨5932427249020036529591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63279223989547056315637 5932427249020036529591)
          ·
            refine ⟨8898640873530054794387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5932427249020036529591 8898640873530054794387)
            ·
              refine ⟨13347961310295082191581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8898640873530054794387 13347961310295082191581)
              ·
                refine ⟨5005485491360655821843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13347961310295082191581 5005485491360655821843)
                ·
                  refine ⟨7508228237040983732765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005485491360655821843 7508228237040983732765)
                  ·
                    refine ⟨2815585588890368899787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7508228237040983732765 2815585588890368899787)
                    ·
                      rfl

theorem cell22_8225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_8225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8225 prefixEnd_8225 := by exact prefixLift 8225
  have htrace : WordTrace (prefixWord ++ tailWord_8225) baseStart_8225 baseEnd_8225 := by
    simpa [prefixWord, tailWord_8225, baseEnd_8225] using wordTrace_append hprefix tailTrace_8225
  have hstable : (prefixWord ++ tailWord_8225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225).length < 2 ^ (prefixWord ++ tailWord_8225).sum := by decide
  have hdescent : baseEnd_8225 < baseStart_8225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277 : List Nat := [1, 3, 2, 2, 1, 3, 2, 8]
def baseStart_8277 : Nat := 118140960795 + 8277 * 2 ^ 59
def prefixEnd_8277 : Nat := 4983230072969 + 3 ^ 40 * 8277 * 2
def baseEnd_8277 : Nat := 314820694619951844403

theorem tailTrace_8277 : CollatzResearch.WordTrace tailWord_8277 prefixEnd_8277 314820694619951844403 := by
  unfold tailWord_8277
  simp only [CollatzResearch.WordTrace]
  refine ⟨301886991021317444167085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201257994014211629444723 301886991021317444167085)
  ·
    refine ⟨113207621632994041562657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301886991021317444167085 113207621632994041562657)
    ·
      refine ⟨84905716224745531171993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113207621632994041562657 84905716224745531171993)
      ·
        refine ⟨63679287168559148378995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84905716224745531171993 63679287168559148378995)
        ·
          refine ⟨95518930752838722568493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63679287168559148378995 95518930752838722568493)
          ·
            refine ⟨35819599032314520963185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95518930752838722568493 35819599032314520963185)
            ·
              refine ⟨26864699274235890722389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35819599032314520963185 26864699274235890722389)
              ·
                refine ⟨314820694619951844403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 26864699274235890722389 314820694619951844403)
                ·
                  rfl

theorem cell22_8277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 8].length) (baseStart_8277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8277 prefixEnd_8277 := by exact prefixLift 8277
  have htrace : WordTrace (prefixWord ++ tailWord_8277) baseStart_8277 baseEnd_8277 := by
    simpa [prefixWord, tailWord_8277, baseEnd_8277] using wordTrace_append hprefix tailTrace_8277
  have hstable : (prefixWord ++ tailWord_8277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277).length < 2 ^ (prefixWord ++ tailWord_8277).sum := by decide
  have hdescent : baseEnd_8277 < baseStart_8277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_8298 : Nat := 118140960795 + 8298 * 2 ^ 59
def prefixEnd_8298 : Nat := 4983230072969 + 3 ^ 40 * 8298 * 2
def baseEnd_8298 : Nat := 2840574980742511824563

theorem tailTrace_8298 : CollatzResearch.WordTrace tailWord_8298 prefixEnd_8298 2840574980742511824563 := by
  unfold tailWord_8298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75663230986309507670387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201768615963492020454365 75663230986309507670387)
  ·
    refine ⟨113494846479464261505581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75663230986309507670387 113494846479464261505581)
    ·
      refine ⟨42560567429799098064593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113494846479464261505581 42560567429799098064593)
      ·
        refine ⟨31920425572349323548445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42560567429799098064593 31920425572349323548445)
        ·
          refine ⟨11970159589630996330667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31920425572349323548445 11970159589630996330667)
          ·
            refine ⟨17955239384446494496001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970159589630996330667 17955239384446494496001)
            ·
              refine ⟨13466429538334870872001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17955239384446494496001 13466429538334870872001)
              ·
                refine ⟨10099822153751153154001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13466429538334870872001 10099822153751153154001)
                ·
                  refine ⟨7574866615313364865501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099822153751153154001 7574866615313364865501)
                  ·
                    refine ⟨2840574980742511824563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7574866615313364865501 2840574980742511824563)
                    ·
                      rfl

theorem cell22_8298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_8298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8298 prefixEnd_8298 := by exact prefixLift 8298
  have htrace : WordTrace (prefixWord ++ tailWord_8298) baseStart_8298 baseEnd_8298 := by
    simpa [prefixWord, tailWord_8298, baseEnd_8298] using wordTrace_append hprefix tailTrace_8298
  have hstable : (prefixWord ++ tailWord_8298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298).length < 2 ^ (prefixWord ++ tailWord_8298).sum := by decide
  have hdescent : baseEnd_8298 < baseStart_8298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 6]
def baseStart_8384 : Nat := 118140960795 + 8384 * 2 ^ 59
def prefixEnd_8384 : Nat := 4983230072969 + 3 ^ 40 * 8384 * 2
def baseEnd_8384 : Nat := 956671512755651391433

theorem tailTrace_8384 : CollatzResearch.WordTrace tailWord_8384 prefixEnd_8384 956671512755651391433 := by
  unfold tailWord_8384
  simp only [CollatzResearch.WordTrace]
  refine ⟨152894800816837359156103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203859734422449812208137 152894800816837359156103)
  ·
    refine ⟨229342201225256038734155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152894800816837359156103 229342201225256038734155)
    ·
      refine ⟨344013301837884058101233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229342201225256038734155 344013301837884058101233)
      ·
        refine ⟨258009976378413043575925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344013301837884058101233 258009976378413043575925)
        ·
          refine ⟨24188435285476222835243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258009976378413043575925 24188435285476222835243)
          ·
            refine ⟨36282652928214334252865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24188435285476222835243 36282652928214334252865)
            ·
              refine ⟨27211989696160750689649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36282652928214334252865 27211989696160750689649)
              ·
                refine ⟨20408992272120563017237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27211989696160750689649 20408992272120563017237)
                ·
                  refine ⟨956671512755651391433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20408992272120563017237 956671512755651391433)
                  ·
                    rfl

theorem cell22_8384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_8384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8384 prefixEnd_8384 := by exact prefixLift 8384
  have htrace : WordTrace (prefixWord ++ tailWord_8384) baseStart_8384 baseEnd_8384 := by
    simpa [prefixWord, tailWord_8384, baseEnd_8384] using wordTrace_append hprefix tailTrace_8384
  have hstable : (prefixWord ++ tailWord_8384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384).length < 2 ^ (prefixWord ++ tailWord_8384).sum := by decide
  have hdescent : baseEnd_8384 < baseStart_8384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8399 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 6, 3]
def baseStart_8399 : Nat := 118140960795 + 8399 * 2 ^ 59
def prefixEnd_8399 : Nat := 4983230072969 + 3 ^ 40 * 8399 * 2
def baseEnd_8399 : Nat := 2875149344811915049253

theorem tailTrace_8399 : CollatzResearch.WordTrace tailWord_8399 prefixEnd_8399 2875149344811915049253 := by
  unfold tailWord_8399
  simp only [CollatzResearch.WordTrace]
  refine ⟨306336696579332280108251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 204224464386221520072167 306336696579332280108251)
  ·
    refine ⟨459505044868998420162377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 306336696579332280108251 459505044868998420162377)
    ·
      refine ⟨344628783651748815121783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 459505044868998420162377 344628783651748815121783)
      ·
        refine ⟨516943175477623222682675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344628783651748815121783 516943175477623222682675)
        ·
          refine ⟨775414763216434834024013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516943175477623222682675 775414763216434834024013)
          ·
            refine ⟨290780536206163062759005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 775414763216434834024013 290780536206163062759005)
            ·
              refine ⟨109042701077311148534627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290780536206163062759005 109042701077311148534627)
              ·
                refine ⟨163564051615966722801941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109042701077311148534627 163564051615966722801941)
                ·
                  refine ⟨7667064919498440131341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163564051615966722801941 7667064919498440131341)
                  ·
                    refine ⟨2875149344811915049253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7667064919498440131341 2875149344811915049253)
                    ·
                      rfl

theorem cell22_8399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_8399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8399 prefixEnd_8399 := by exact prefixLift 8399
  have htrace : WordTrace (prefixWord ++ tailWord_8399) baseStart_8399 baseEnd_8399 := by
    simpa [prefixWord, tailWord_8399, baseEnd_8399] using wordTrace_append hprefix tailTrace_8399
  have hstable : (prefixWord ++ tailWord_8399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8399).length < 2 ^ (prefixWord ++ tailWord_8399).sum := by decide
  have hdescent : baseEnd_8399 < baseStart_8399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8401 : List Nat := [1, 2, 2, 1, 2, 2, 5, 3, 4]
def baseStart_8401 : Nat := 118140960795 + 8401 * 2 ^ 59
def prefixEnd_8401 : Nat := 4983230072969 + 3 ^ 40 * 8401 * 2
def baseEnd_8401 : Nat := 958611328561525499749

theorem tailTrace_8401 : CollatzResearch.WordTrace tailWord_8401 prefixEnd_8401 958611328561525499749 := by
  unfold tailWord_8401
  simp only [CollatzResearch.WordTrace]
  refine ⟨306409642572086621681057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 204273095048057747787371 306409642572086621681057)
  ·
    refine ⟨229807231929064966260793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 306409642572086621681057 229807231929064966260793)
    ·
      refine ⟨172355423946798724695595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229807231929064966260793 172355423946798724695595)
      ·
        refine ⟨258533135920198087043393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172355423946798724695595 258533135920198087043393)
        ·
          refine ⟨193899851940148565282545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258533135920198087043393 193899851940148565282545)
          ·
            refine ⟨145424888955111423961909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193899851940148565282545 145424888955111423961909)
            ·
              refine ⟨13633583339541695996429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145424888955111423961909 13633583339541695996429)
              ·
                refine ⟨5112593752328135998661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13633583339541695996429 5112593752328135998661)
                ·
                  refine ⟨958611328561525499749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5112593752328135998661 958611328561525499749)
                  ·
                    rfl

theorem cell22_8401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_8401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8401 prefixEnd_8401 := by exact prefixLift 8401
  have htrace : WordTrace (prefixWord ++ tailWord_8401) baseStart_8401 baseEnd_8401 := by
    simpa [prefixWord, tailWord_8401, baseEnd_8401] using wordTrace_append hprefix tailTrace_8401
  have hstable : (prefixWord ++ tailWord_8401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8401).length < 2 ^ (prefixWord ++ tailWord_8401).sum := by decide
  have hdescent : baseEnd_8401 < baseStart_8401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8416 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 2, 3]
def baseStart_8416 : Nat := 118140960795 + 8416 * 2 ^ 59
def prefixEnd_8416 : Nat := 4983230072969 + 3 ^ 40 * 8416 * 2
def baseEnd_8416 : Nat := 2880968792229537374201

theorem tailTrace_8416 : CollatzResearch.WordTrace tailWord_8416 prefixEnd_8416 2880968792229537374201 := by
  unfold tailWord_8416
  simp only [CollatzResearch.WordTrace]
  refine ⟨153478368758872091738551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 204637825011829455651401 153478368758872091738551)
  ·
    refine ⟨230217553138308137607827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153478368758872091738551 230217553138308137607827)
    ·
      refine ⟨345326329707462206411741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230217553138308137607827 345326329707462206411741)
      ·
        refine ⟨129497373640298327404403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345326329707462206411741 129497373640298327404403)
        ·
          refine ⟨194246060460447491106605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129497373640298327404403 194246060460447491106605)
          ·
            refine ⟨72842272672667809164977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194246060460447491106605 72842272672667809164977)
            ·
              refine ⟨54631704504500856873733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72842272672667809164977 54631704504500856873733)
              ·
                refine ⟨10243444594593910663825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54631704504500856873733 10243444594593910663825)
                ·
                  refine ⟨7682583445945432997869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10243444594593910663825 7682583445945432997869)
                  ·
                    refine ⟨2880968792229537374201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7682583445945432997869 2880968792229537374201)
                    ·
                      rfl

theorem cell22_8416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_8416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8416 prefixEnd_8416 := by exact prefixLift 8416
  have htrace : WordTrace (prefixWord ++ tailWord_8416) baseStart_8416 baseEnd_8416 := by
    simpa [prefixWord, tailWord_8416, baseEnd_8416] using wordTrace_append hprefix tailTrace_8416
  have hstable : (prefixWord ++ tailWord_8416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8416).length < 2 ^ (prefixWord ++ tailWord_8416).sum := by decide
  have hdescent : baseEnd_8416 < baseStart_8416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8433 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 2, 3]
def baseStart_8433 : Nat := 118140960795 + 8433 * 2 ^ 59
def prefixEnd_8433 : Nat := 4983230072969 + 3 ^ 40 * 8433 * 2
def baseEnd_8433 : Nat := 2886788239647159699149

theorem tailTrace_8433 : CollatzResearch.WordTrace tailWord_8433 prefixEnd_8433 2886788239647159699149 := by
  unfold tailWord_8433
  simp only [CollatzResearch.WordTrace]
  refine ⟨307576778456156086845953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 205051185637437391230635 307576778456156086845953)
  ·
    refine ⟨230682583842117065134465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 307576778456156086845953 230682583842117065134465)
    ·
      refine ⟨173011937881587798850849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230682583842117065134465 173011937881587798850849)
      ·
        refine ⟨129758953411190849138137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173011937881587798850849 129758953411190849138137)
        ·
          refine ⟨97319215058393136853603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129758953411190849138137 97319215058393136853603)
          ·
            refine ⟨145978822587589705280405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97319215058393136853603 145978822587589705280405)
            ·
              refine ⟨6842757308793267435019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145978822587589705280405 6842757308793267435019)
              ·
                refine ⟨10264135963189901152529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6842757308793267435019 10264135963189901152529)
                ·
                  refine ⟨7698101972392425864397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10264135963189901152529 7698101972392425864397)
                  ·
                    refine ⟨2886788239647159699149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7698101972392425864397 2886788239647159699149)
                    ·
                      rfl

theorem cell22_8433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_8433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8433 prefixEnd_8433 := by exact prefixLift 8433
  have htrace : WordTrace (prefixWord ++ tailWord_8433) baseStart_8433 baseEnd_8433 := by
    simpa [prefixWord, tailWord_8433, baseEnd_8433] using wordTrace_append hprefix tailTrace_8433
  have hstable : (prefixWord ++ tailWord_8433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8433).length < 2 ^ (prefixWord ++ tailWord_8433).sum := by decide
  have hdescent : baseEnd_8433 < baseStart_8433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8519 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 8]
def baseStart_8519 : Nat := 118140960795 + 8519 * 2 ^ 59
def prefixEnd_8519 : Nat := 4983230072969 + 3 ^ 40 * 8519 * 2
def baseEnd_8519 : Nat := 972075932390534016295

theorem tailTrace_8519 : CollatzResearch.WordTrace tailWord_8519 prefixEnd_8519 972075932390534016295 := by
  unfold tailWord_8519
  simp only [CollatzResearch.WordTrace]
  refine ⟨310713456144592774476611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 207142304096395182984407 310713456144592774476611)
  ·
    refine ⟨466070184216889161714917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 310713456144592774476611 466070184216889161714917)
    ·
      refine ⟨87388159540666717821547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 466070184216889161714917 87388159540666717821547)
      ·
        refine ⟨131082239311000076732321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87388159540666717821547 131082239311000076732321)
        ·
          refine ⟨98311679483250057549241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131082239311000076732321 98311679483250057549241)
          ·
            refine ⟨73733759612437543161931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98311679483250057549241 73733759612437543161931)
            ·
              refine ⟨110600639418656314742897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73733759612437543161931 110600639418656314742897)
              ·
                refine ⟨82950479563992236057173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110600639418656314742897 82950479563992236057173)
                ·
                  refine ⟨972075932390534016295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 82950479563992236057173 972075932390534016295)
                  ·
                    rfl

theorem cell22_8519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 8].length) (baseStart_8519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8519 prefixEnd_8519 := by exact prefixLift 8519
  have htrace : WordTrace (prefixWord ++ tailWord_8519) baseStart_8519 baseEnd_8519 := by
    simpa [prefixWord, tailWord_8519, baseEnd_8519] using wordTrace_append hprefix tailTrace_8519
  have hstable : (prefixWord ++ tailWord_8519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8519).length < 2 ^ (prefixWord ++ tailWord_8519).sum := by decide
  have hdescent : baseEnd_8519 < baseStart_8519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8602 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_8602 : Nat := 118140960795 + 8602 * 2 ^ 59
def prefixEnd_8602 : Nat := 4983230072969 + 3 ^ 40 * 8602 * 2
def baseEnd_8602 : Nat := 2944640393387052223631

theorem tailTrace_8602 : CollatzResearch.WordTrace tailWord_8602 prefixEnd_8602 2944640393387052223631 := by
  unfold tailWord_8602
  simp only [CollatzResearch.WordTrace]
  refine ⟨78435178710974487437015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 209160476562598633165373 78435178710974487437015)
  ·
    refine ⟨117652768066461731155523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78435178710974487437015 117652768066461731155523)
    ·
      refine ⟨176479152099692596733285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117652768066461731155523 176479152099692596733285)
      ·
        refine ⟨33089841018692361887491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176479152099692596733285 33089841018692361887491)
        ·
          refine ⟨49634761528038542831237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33089841018692361887491 49634761528038542831237)
          ·
            refine ⟨9306517786507226780857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49634761528038542831237 9306517786507226780857)
            ·
              refine ⟨6979888339880420085643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9306517786507226780857 6979888339880420085643)
              ·
                refine ⟨10469832509820630128465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6979888339880420085643 10469832509820630128465)
                ·
                  refine ⟨7852374382365472596349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10469832509820630128465 7852374382365472596349)
                  ·
                    refine ⟨2944640393387052223631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7852374382365472596349 2944640393387052223631)
                    ·
                      rfl

theorem cell22_8602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_8602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8602 prefixEnd_8602 := by exact prefixLift 8602
  have htrace : WordTrace (prefixWord ++ tailWord_8602) baseStart_8602 baseEnd_8602 := by
    simpa [prefixWord, tailWord_8602, baseEnd_8602] using wordTrace_append hprefix tailTrace_8602
  have hstable : (prefixWord ++ tailWord_8602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8602).length < 2 ^ (prefixWord ++ tailWord_8602).sum := by decide
  have hdescent : baseEnd_8602 < baseStart_8602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
